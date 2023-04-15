{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantRestoreCursor (redundantRestoreCursorPass) where

import Compiler.Hoopl as H

--import Debug.Trace

import Regex.IR

-- True if cursor has moved since saving, or more generally if it might change
-- by a restore.
type RedundantRestoreFact = Bool

redundantRestoreLattice :: DataflowLattice RedundantRestoreFact
redundantRestoreLattice = DataflowLattice
 { fact_name = "Redundant RestoreCursor"
 , fact_bot  = True
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new || old
              ch = changeIf (j /= old)

-- Moving the cursor means a restore may be necessary from now on.
kill :: Insn e O -> RedundantRestoreFact -> RedundantRestoreFact
kill Next _ = True
kill _    f = f

-- Restoring or saving cursor makes current cursor definitely exactly the same
-- as the saved cursor.
gen :: Insn e O -> RedundantRestoreFact -> RedundantRestoreFact
gen RestoreCursor _ = False
gen SaveCursor    _ = False
gen _             f = f

redundantRestoreCursorTransfer :: FwdTransfer Insn RedundantRestoreFact
redundantRestoreCursorTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> RedundantRestoreFact -> RedundantRestoreFact
    first _ f = f
    middle :: Insn O O -> RedundantRestoreFact -> RedundantRestoreFact
    middle insn = gen insn . kill insn
    -- Final instructions never change the cursor.
    last :: Insn O C -> RedundantRestoreFact -> FactBase RedundantRestoreFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase redundantRestoreLattice [(l, f) | l <- ls]

redundantRestoreCursor :: FuelMonad m => FwdRewrite m Insn RedundantRestoreFact
redundantRestoreCursor = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> RedundantRestoreFact -> m (Maybe (Graph Insn e x))
    rw RestoreCursor False = return (Just emptyGraph)
    rw _ _ = return Nothing

redundantRestoreCursorPass :: FuelMonad m => FwdPass m Insn RedundantRestoreFact
redundantRestoreCursorPass = FwdPass
  { fp_lattice = redundantRestoreLattice
  , fp_transfer = redundantRestoreCursorTransfer
  , fp_rewrite = redundantRestoreCursor }
