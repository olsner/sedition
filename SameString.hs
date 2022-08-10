{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

-- sameStringPass: Find cases where a string variable is set to the same other
-- variable on every incoming branch. Should rewrite many uses of
-- S{pattern-space} when we know statically which pattern-space value is being
-- referred to.

module SameString (sameStringPass) where

import Compiler.Hoopl as H hiding ((<*>))

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
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

deleteValues value = M.map (\x -> if x == value then Top else x)
changeString s = deleteValues (PElem s)

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
    middle (SetS s (SVarRef s2)) = changeString s . M.insert s (PElem s2)
    middle (SetS s _)            = changeString s . M.insert s Top
    middle (AppendS s _)         = changeString s . M.insert s Top
    middle (GetMessage s)        = M.insert s Top
    middle (Read s _)            = M.insert s Top
    middle (ReadFile s _)        = M.insert s Top
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
    -- Note that we only rewrite the input variables.
    rw :: FuelMonad m => Insn e x -> SameStringFact -> m (Maybe (Graph Insn e x))
    rw (SetS s expr)   f = return (mkMiddle . SetS s <$> rwE expr f)
    rw (SetP p cond)   f = return (mkMiddle . SetP p <$> rwC cond f)
    rw (SetM m expr)   f = return (mkMiddle . SetM m <$> rwM expr f)
    rw (Print fd s)    f = return (mkMiddle <$> var1 (Print fd) s f)
    rw (AppendS s1 s2) f = return (mkMiddle <$> var1 (AppendS s1) s2 f)
    rw (Message s)     f = return (mkMiddle <$> var1 Message s f)
    rw (ShellExec s)   f = return (mkMiddle <$> var1 ShellExec s f)
    rw _ _ = return Nothing

    rwE (SVarRef s)        f = var1 SVarRef s f
    rwE (SAppendNL s1 s2)  f = var2 SAppendNL s1 s2 f
    rwE (SAppend s1 s2)    f = var2 SAppend s1 s2 f
    rwE (STrans from to s) f = var1 (STrans from to) s f
    rwE (SFormatLiteral w s) f = var1 (SFormatLiteral w) s f
    rwE (SSubstring s i j) f = var1 (\s -> SSubstring s i j) s f
    rwE _                  _ = Nothing

    rwM (Match s re)       f = var1 (\s -> Match s re) s f
    rwM (MatchLastRE s)    f = var1 MatchLastRE s f
    rwM (NextMatch m s)    f = var1 (NextMatch m) s f
    rwM _                  _ = Nothing

    rwC _                  _ = Nothing

    -- Don't return Just x unless at least one of the arguments were rewritten.
    -- Avoids wasting optimization fuel when nothing changes.
    var2 :: (SVar -> SVar -> a) -> SVar -> SVar -> SameStringFact -> Maybe a
    var2 con s1 s2 f | s1' <- var1 id s1 f, s2' <- var1 id s2 f =
        if isJust s1' || isJust s2'
          then Just (con (fromMaybe s1 s1') (fromMaybe s2 s2'))
          else Nothing

    var1 :: (SVar -> a) -> SVar -> SameStringFact -> Maybe a
    var1 con s f | Just (PElem t) <- M.lookup s f = Just (con t)
                 | otherwise                      = Nothing


sameStringPass :: FuelMonad m => FwdPass m Insn SameStringFact
sameStringPass = {- debugFwdJoins trace (const True) $ -} FwdPass
  { fp_lattice = constLattice
  , fp_transfer = sameStringTransfer
  , fp_rewrite = sameString }
