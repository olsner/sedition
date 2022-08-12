{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module LivePred (livePredPass) where

import Compiler.Hoopl as H

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
--import Debug.Trace

import IR

type LivePredFact = Set Pred
liveLattice :: DataflowLattice LivePredFact
liveLattice = DataflowLattice
 { fact_name = "Live predicate"
 , fact_bot  = S.empty
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `S.union` old
              ch = changeIf (S.size j > S.size old)

kill :: Insn e x -> LivePredFact -> LivePredFact
kill (SetP p _) f = S.delete p f
kill _         f = f

gen :: Insn e x -> LivePredFact -> LivePredFact
gen (If p _ _) f = S.insert p f
gen _          f = f

livePredTransfer :: BwdTransfer Insn LivePredFact
livePredTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LivePredFact -> LivePredFact
    first (Label _)  f = f
    middle :: Insn O O -> LivePredFact -> LivePredFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LivePredFact -> LivePredFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact f l = fromMaybe S.empty (mapLookup l f)
    facts ls f = S.unions (map (fact f) ls)

livePred :: FuelMonad m => BwdRewrite m Insn LivePredFact
livePred = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LivePredFact -> m (Maybe (Graph Insn e x))
    rw (SetP p _) f | not (S.member p f) = return (Just emptyGraph)
    rw _ _ = return Nothing

livePredPass :: FuelMonad m => BwdPass m Insn LivePredFact
livePredPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = livePredTransfer
  , bp_rewrite = livePred }


