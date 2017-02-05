{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module LivePred (livePredPass) where

import Compiler.Hoopl as H

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Debug.Trace

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


livePredTransfer :: BwdTransfer Insn LivePredFact
livePredTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LivePredFact -> LivePredFact
    -- C O
    first (Label _)  f = f

    -- O O
    middle :: Insn O O -> LivePredFact -> LivePredFact
    middle (Set p _)       f = S.delete p f

    middle _insn f = {-trace ("Unhandled instruction " ++ show insn)-} f

    -- O C
    last :: Insn O C -> FactBase LivePredFact -> LivePredFact
    last (Branch l) f = fact f l
    last (If p tl fl) f = S.insert p (facts f [fl,tl])
    last (Cycle _ intr read eof) f = facts f [intr,read,eof]
    last (Quit _) _ = S.empty
    -- All predicates are reset in the child, so only the "next"-label needs
    -- to be present in the output fact.
    last (Fork _ b) f = fact f b

    fact f l = fromMaybe S.empty (mapLookup l f)
    facts f ls = S.unions (map (fact f) ls)

livePred :: FuelMonad m => BwdRewrite m Insn LivePredFact
livePred = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LivePredFact -> m (Maybe (Graph Insn e x))
    rw (Set p _) f | not (S.member p f) =
        trace ("Dropping Set " ++ show p) $
        return $ Just emptyGraph
    rw _ _ = return Nothing

livePredPass :: FuelMonad m => BwdPass m Insn LivePredFact
livePredPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = livePredTransfer
  , bp_rewrite = livePred }


