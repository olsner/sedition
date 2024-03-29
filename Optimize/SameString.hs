{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

-- sameStringPass: Find cases where a string variable is set to the same other
-- variable on every incoming branch. Should rewrite many uses of
-- S{pattern-space} when we know statically which pattern-space value is being
-- referred to.
-- The tricky bit is handling mutable strings - when a variable changes we
-- can no longer rewrite copies of it into references to the original variable.
-- The effect of this compile-time optimization can probably also be achieved
-- by having CoW strings and lazy substring/append at runtime.

module Optimize.SameString (sameStringPass) where

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
   constFactAdd ::
     Label -> OldFact SVar -> NewFact SVar -> (ChangeFlag, WithTop SVar)
   constFactAdd _ (OldFact old) (NewFact new)
       = if new == old then (NoChange, PElem new)
         else               (SomeChange, Top)

-- TODO Make a reversible map that has an efficient way to do this?
deleteValues value = M.map (\x -> if x == value then Top else x)
-- s has changed value to new. Use "Top" when the value is not something we
-- can represent in the mapping (i.e. anything except a copy of another string).
-- When changing s, we also need to invalidate other references to s in the
-- *values* of the fact base. That's annoying.
changeString s new = deleteValues (PElem s) . M.insert s new

sameStringTransfer :: FwdTransfer Insn SameStringFact
sameStringTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> SameStringFact -> SameStringFact
    -- C O
    first (Label _)  f = f

    -- O O
    middle :: Insn O O -> SameStringFact -> SameStringFact
    middle (SetS s (SVarRef s2)) = changeString s (PElem s2)
    middle (SetS s _)            = changeString s Top
    middle (GetMessage s)        = changeString s Top
    middle (Read s _)            = changeString s Top
    middle (ReadFile s _)        = changeString s Top
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
    rw (Message s)     f = return (mkMiddle <$> var1 Message s f)
    rw (ShellExec s)   f = return (mkMiddle <$> var1 ShellExec s f)
    rw _ _ = return Nothing

    rwE (SVarRef s)        f = var1 SVarRef s f
    rwE (SAppend xs)       f = SAppend <$> varN xs f
    rwE (STrans from to s) f = var1 (STrans from to) s f
    rwE (SFormatLiteral w s) f = var1 (SFormatLiteral w) s f
    rwE (SSubstring s i j) f = var1 (\s -> SSubstring s i j) s f
    rwE _                  _ = Nothing

    rwM (Match s re)       f = var1 (\s -> Match s re) s f
    rwM (MatchLastRE s)    f = var1 MatchLastRE s f
    rwM (NextMatch m s)    f = var1 (NextMatch m) s f
    rwM _                  _ = Nothing

    rwC _                  _ = Nothing

    var1 :: (SVar -> a) -> SVar -> SameStringFact -> Maybe a
    var1 con s f | Just (PElem t) <- M.lookup s f = Just (con t)
                 | otherwise                      = Nothing

    varN :: [StringExpr] -> SameStringFact -> Maybe [StringExpr]
    varN []     _ = Nothing
    varN [x]    f = (:[]) <$> rwE x f
    varN (x:xs) f | Just x'  <- rwE x f   = Just (x':xs)
                  | Just xs' <- varN xs f = Just (x:xs')
                  | otherwise             = Nothing


sameStringPass :: FuelMonad m => FwdPass m Insn SameStringFact
sameStringPass = {- debugFwdJoins trace (const True) $ -} FwdPass
  { fp_lattice = constLattice
  , fp_transfer = sameStringTransfer
  , fp_rewrite = sameString }
