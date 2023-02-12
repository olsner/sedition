{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module LivePred (livePredPass) where

import Compiler.Hoopl as H

--import Debug.Trace

import Collections
import IR

type LivePredFact = PredSet
liveLattice :: DataflowLattice LivePredFact
liveLattice = DataflowLattice
 { fact_name = "Live predicate"
 , fact_bot  = setEmpty
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `setUnion` old
              ch = changeIf (setSize j > setSize old)

kill :: Insn e x -> LivePredFact -> LivePredFact
kill (SetP p _) f = setDelete p f
kill _         f = f

gen :: Insn e x -> LivePredFact -> LivePredFact
gen (If c _ _) = genC c
gen (SetP _ c) = genC c
gen _          = id

genC (PRef p) = setInsert p
genC _ = id

livePredTransfer :: BwdTransfer Insn LivePredFact
livePredTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LivePredFact -> LivePredFact
    first (Label _)  f = f
    middle :: Insn O O -> LivePredFact -> LivePredFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LivePredFact -> LivePredFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact f l = mapFindWithDefault setEmpty l f
    facts ls f = setUnions (map (fact f) ls)

livePred :: FuelMonad m => BwdRewrite m Insn LivePredFact
livePred = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LivePredFact -> m (Maybe (Graph Insn e x))
    rw (SetP p _) f | not (setMember p f) = return (Just emptyGraph)
    rw _ _ = return Nothing

livePredPass :: FuelMonad m => BwdPass m Insn LivePredFact
livePredPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = livePredTransfer
  , bp_rewrite = livePred }


