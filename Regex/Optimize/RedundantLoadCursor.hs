{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantLoadCursor (redundantLoadCursorPass) where

import Compiler.Hoopl as H

import Debug.Trace

import Regex.IR
import Regex.TDFA (RegId)

type LoadCursorFact = WithTopAndBot RegId

liveLattice :: DataflowLattice LoadCursorFact
liveLattice = addPoints' "Live SaveCursor" add
 where
  add _ (OldFact old) (NewFact new)
    | new == old = (NoChange, PElem old)
    | otherwise = (SomeChange, Top)

redundantLoadCursorTransfer :: FwdTransfer Insn LoadCursorFact
redundantLoadCursorTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> LoadCursorFact -> LoadCursorFact
    first (Label _)  f = f
    middle :: Insn O O -> LoadCursorFact -> LoadCursorFact
    middle (MoveCursor _) _ = Top
    middle (SaveCursor r 0) _ = PElem r
    middle (SaveCursor _ _) _ = {-trace "SaveCursor with offset?"-} Top
    middle _                f = f
    last :: Insn O C -> LoadCursorFact -> FactBase LoadCursorFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase liveLattice [(l, f) | l <- ls]

redundantLoadCursor :: FuelMonad m => FwdRewrite m Insn LoadCursorFact
redundantLoadCursor = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> LoadCursorFact -> m (Maybe (Graph Insn e x))
    -- We only touch LoadCursor in this pass - the live register pass may
    -- remove the matching save call if this was the last use of that register.
    rw (LoadCursor r1) (PElem r2) | r1 == r2 = return (Just emptyGraph)
    rw _ _ = return Nothing

enableTrace = False

interesting (SaveCursor _ _) = True
interesting (LoadCursor _) = True
interesting (MoveCursor _) = True
interesting _ = False

ifChanged SomeChange = True
ifChanged NoChange = False

addTracing
  | enableTrace = debugFwdJoins trace ifChanged . debugFwdTransfers trace show (\insn _ -> interesting insn)
  | otherwise = id

redundantLoadCursorPass :: FuelMonad m => FwdPass m Insn LoadCursorFact
redundantLoadCursorPass = addTracing $ FwdPass
  { fp_lattice = liveLattice
  , fp_transfer = redundantLoadCursorTransfer
  , fp_rewrite = redundantLoadCursor }
