{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.LiveCursor (liveCursorPass) where

import Compiler.Hoopl as H

import Debug.Trace

import Regex.IR

type LiveCursorFact = Bool
liveLattice :: DataflowLattice LiveCursorFact
liveLattice = DataflowLattice
 { fact_name = "Live Cursor"
 , fact_bot  = False
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new || old
              ch = changeIf (new /= old)

kill :: Insn e x -> LiveCursorFact -> LiveCursorFact
kill (LoadCursor _) _ = False
kill _              f = f

gen :: Insn e x -> LiveCursorFact -> LiveCursorFact
gen (SaveCursor _ _)    _ = True
gen (Switch _ _ _)      _ = True
gen (TotalSwitch _ _)   _ = True
gen (IfBOL _ _)         _ = True
gen (CheckBounds _ _ _) _ = True
gen _                   f = f

liveCursorTransfer :: BwdTransfer Insn LiveCursorFact
liveCursorTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LiveCursorFact -> LiveCursorFact
    first (Label _)  f = f
    middle :: Insn O O -> LiveCursorFact -> LiveCursorFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LiveCursorFact -> LiveCursorFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact f l = mapFindWithDefault False l f
    facts ls f = or (map (fact f) ls)

liveCursor :: FuelMonad m => BwdRewrite m Insn LiveCursorFact
liveCursor = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LiveCursorFact -> m (Maybe (Graph Insn e x))
    rw (LoadCursor _) False = return (Just emptyGraph)
    rw (MoveCursor _) False = return (Just emptyGraph)
    rw _ _ = return Nothing

liveCursorPass :: FuelMonad m => BwdPass m Insn LiveCursorFact
liveCursorPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveCursorTransfer
  , bp_rewrite = liveCursor }

