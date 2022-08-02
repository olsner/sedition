{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

-- sameStringPass: Find cases where a string variable is set to the same other
-- variable on every incoming branch. Should rewrite many uses of
-- S{pattern-space} when we know statically which pattern-space value is being
-- referred to.

module SameString (sameStringPass) where

import Compiler.Hoopl as H hiding ((<*>))

import Data.Map (Map)
import qualified Data.Map as M
import Debug.Trace

import IR

type SameStringFact = Map SVar (WithTop SVar)
constLattice :: DataflowLattice SameStringFact
constLattice = DataflowLattice
 { fact_name = "Same string"
 , fact_bot  = M.empty
 , fact_join = joinMaps (extendJoinDomain constFactAdd) }
 where
   constFactAdd _ (OldFact old) (NewFact new)
       = if new == old then (NoChange, PElem new)
         else               (SomeChange, Top)

deleteValues value = M.filter (/= value)

sameStringTransfer :: FwdTransfer Insn SameStringFact
sameStringTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> SameStringFact -> SameStringFact
    -- C O
    first (Label _)  f = f

    -- O O
    middle :: Insn O O -> SameStringFact -> SameStringFact
    -- When changing s, we also need to invalidate other references to s in the
    -- *values* of the fact base. That's annoying.
    middle (SetS s (SVarRef s2)) = M.insert s (PElem s2)
    middle (SetS s _)            = M.insert s Top
    middle (GetMessage s)        = M.insert s Top
    middle (Read s _)            = M.insert s Top
    middle _insn                 = id

    -- O C
    last :: Insn O C -> SameStringFact -> FactBase SameStringFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase constLattice [(l, f) | l <- ls]

sameString :: FuelMonad m => FwdRewrite m Insn SameStringFact
sameString = deepFwdRw rw
  where
    -- Operations that read from a string variable can be rewritten to use the
    -- incoming variable instead, if that is constant.
    -- TODO Annoying duplication of return/Just/mkMiddle and pattern matching
    -- on the helpers. And where is fuel consumed? Perhaps every variable
    -- replaced should consume its own fuel so that we can bisect with enough
    -- detail.
    rw :: FuelMonad m => Insn e x -> SameStringFact -> m (Maybe (Graph Insn e x))
    rw (SetS s expr) f | Just expr' <- rwE expr f = return (Just (mkMiddle (SetS s expr')))
    rw (SetP p cond) f | Just cond' <- rwC cond f = return (Just (mkMiddle (SetP p cond')))
    rw (SetM m expr) f | Just expr' <- rwM expr f = return (Just (mkMiddle (SetM m expr')))
    rw (Print fd s) f | Just s' <- var s f = return (Just (mkMiddle (Print fd s')))
    rw (WriteFile path s) f | Just s' <- var s f = return (Just (mkMiddle (WriteFile path s')))
    -- rw (Message s) =
    -- rw (PrintLiteral _ _ s) =
    -- rw (ShellExec s) =
    -- rw (WriteFile _ s) =
    rw _ _ = return Nothing

    rwE (SVarRef s)        f = SVarRef <$> var s f
    rwE (SAppendNL s1 s2)  f = SAppendNL <$> var s1 f <*> var s2 f
    rwE (SAppend s1 s2)    f = SAppend <$> var s1 f <*> var s2 f
    rwE (STrans from to s) f = STrans from to <$> var s f
    rwE _                  _ = Nothing

    rwM (Match s re)       f = Match <$> var s f <*> pure re
    rwM (MatchLastRE s)    f = MatchLastRE <$> var s f
    rwM _                  _ = Nothing

    rwC _                  _ = Nothing

    var s f | Just (PElem t) <- M.lookup s f = Just t
            | otherwise                      = Nothing


sameStringPass :: FuelMonad m => FwdPass m Insn SameStringFact
sameStringPass = FwdPass
  { fp_lattice = constLattice
  , fp_transfer = sameStringTransfer
  , fp_rewrite = sameString }

