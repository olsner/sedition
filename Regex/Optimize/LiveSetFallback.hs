{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.LiveSetFallback (liveSetFallbackPass) where

import Compiler.Hoopl as H

--import Debug.Trace

import Regex.IR

type LiveSetFallbackFact = Bool
liveLattice :: DataflowLattice LiveSetFallbackFact
liveLattice = DataflowLattice
 { fact_name = "Live SetFallback"
 , fact_bot  = False
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new || old
              ch = changeIf (new /= old)

kill :: Insn e x -> LiveSetFallbackFact -> LiveSetFallbackFact
kill (SetFallback _) _ = False
kill _               f = f

gen :: Insn e x -> LiveSetFallbackFact -> LiveSetFallbackFact
gen (Fallback _) _ = True
gen _            f = f

liveSetFallbackTransfer :: BwdTransfer Insn LiveSetFallbackFact
liveSetFallbackTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LiveSetFallbackFact -> LiveSetFallbackFact
    first (Label _)  f = f
    middle :: Insn O O -> LiveSetFallbackFact -> LiveSetFallbackFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LiveSetFallbackFact -> LiveSetFallbackFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact f l = mapFindWithDefault False l f
    facts ls f = or (map (fact f) ls)

liveSetFallback :: FuelMonad m => BwdRewrite m Insn LiveSetFallbackFact
liveSetFallback = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LiveSetFallbackFact -> m (Maybe (Graph Insn e x))
    rw (SetFallback _) False = return (Just emptyGraph)
    rw _ _ = return Nothing

liveSetFallbackPass :: FuelMonad m => BwdPass m Insn LiveSetFallbackFact
liveSetFallbackPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveSetFallbackTransfer
  , bp_rewrite = liveSetFallback }


