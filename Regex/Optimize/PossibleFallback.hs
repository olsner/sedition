{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.PossibleFallback (possibleFallbackPass) where

import Compiler.Hoopl as H

import Debug.Trace

import Regex.IR

type PossibleFallbackFact = LabelSet

fallbackLattice :: DataflowLattice PossibleFallbackFact
fallbackLattice = DataflowLattice
 { fact_name = "Possible fallback targets"
 , fact_bot  = setEmpty
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `setUnion` old
              ch = changeIf (setSize j > setSize old)

fallbackTransfer :: FwdTransfer Insn PossibleFallbackFact
fallbackTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> PossibleFallbackFact -> PossibleFallbackFact
    -- C O
    first (Label _)  f = f

    -- O O
    middle :: Insn O O -> PossibleFallbackFact -> PossibleFallbackFact
    middle (SetFallback l) _ = setSingleton l
    middle _insn f = {-trace ("Unhandled instruction " ++ show insn)-} f

    -- O C
    last :: Insn O C -> PossibleFallbackFact -> FactBase PossibleFallbackFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase fallbackLattice [(l, f) | l <- ls]

fallback :: FuelMonad m => FwdRewrite m Insn PossibleFallbackFact
fallback = deepFwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> PossibleFallbackFact -> m (Maybe (Graph Insn e x))
    rw (Fallback ls) f | [l] <- setElems ls = rwLast (Branch l)
                       | [l] <- setElems f  = rwLast (Branch l)
                       | otherwise          = rwLast (Fallback (setIntersection ls f))
    rw _ _ = return Nothing

    rwLast insn = return (Just (mkLast insn))

possibleFallbackPass :: FuelMonad m => FwdPass m Insn PossibleFallbackFact
possibleFallbackPass = FwdPass
  { fp_lattice = fallbackLattice
  , fp_transfer = fallbackTransfer
  , fp_rewrite = fallback }
