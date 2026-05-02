{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.LiveSaveCursor (liveSaveCursorPass) where

import Compiler.Hoopl as H

--import Debug.Trace

import Regex.IR

type LiveSaveCursorFact = Bool
liveLattice :: DataflowLattice LiveSaveCursorFact
liveLattice = DataflowLattice
 { fact_name = "Live SaveCursor"
 , fact_bot  = False
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new || old
              ch = changeIf (new /= old)

kill :: Insn e x -> LiveSaveCursorFact -> LiveSaveCursorFact
kill SaveCursor _ = False
kill _          f = f

gen :: Insn e x -> LiveSaveCursorFact -> LiveSaveCursorFact
gen RestoreCursor _ = True
gen _             f = f

liveSaveCursorTransfer :: BwdTransfer Insn LiveSaveCursorFact
liveSaveCursorTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LiveSaveCursorFact -> LiveSaveCursorFact
    first (Label _)  f = f
    middle :: Insn O O -> LiveSaveCursorFact -> LiveSaveCursorFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LiveSaveCursorFact -> LiveSaveCursorFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact f l = mapFindWithDefault False l f
    facts ls f = or (map (fact f) ls)

liveSaveCursor :: FuelMonad m => BwdRewrite m Insn LiveSaveCursorFact
liveSaveCursor = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LiveSaveCursorFact -> m (Maybe (Graph Insn e x))
    rw SaveCursor False = return (Just emptyGraph)
    rw _ _ = return Nothing

liveSaveCursorPass :: FuelMonad m => BwdPass m Insn LiveSaveCursorFact
liveSaveCursorPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveSaveCursorTransfer
  , bp_rewrite = liveSaveCursor }


