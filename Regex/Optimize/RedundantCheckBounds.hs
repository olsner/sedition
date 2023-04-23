{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantCheckBounds (redundantCheckBoundsPass) where

import Compiler.Hoopl as H

--import Debug.Trace

import Regex.IR

-- Lower bound of checked bounds on all incoming paths, or Bot if no bounds
-- have been checked yet.
type RedundantBoundsFact = WithBot Int

redundantBoundsLattice :: DataflowLattice RedundantBoundsFact
redundantBoundsLattice = addPoints "Bounds checked" add
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = min new old
              ch = changeIf (j /= old)

redundantCheckBoundsTransfer :: FwdTransfer Insn RedundantBoundsFact
redundantCheckBoundsTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> RedundantBoundsFact -> RedundantBoundsFact
    first _ f = f
    middle :: Insn O O -> RedundantBoundsFact -> RedundantBoundsFact
    middle Next Bot       = Bot
    middle Next (PElem 0) = PElem 0
    middle Next (PElem n) = PElem (n - 1)
    middle _    f         = f
    last :: Insn O C -> RedundantBoundsFact -> FactBase RedundantBoundsFact
    last (CheckBounds n eof cont) f =
      mkFactBase redundantBoundsLattice [(eof, f), (cont, PElem n)]
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase redundantBoundsLattice [(l, f) | l <- ls]

redundantCheckBounds :: FuelMonad m => FwdRewrite m Insn RedundantBoundsFact
redundantCheckBounds = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> RedundantBoundsFact -> m (Maybe (Graph Insn e x))
    rw (CheckBounds n _ cont) (PElem m) | n <= m = rwLast (Branch cont)
    rw _ _ = return Nothing

    rwLast insn = return (Just (mkLast insn))

redundantCheckBoundsPass :: FuelMonad m => FwdPass m Insn RedundantBoundsFact
redundantCheckBoundsPass = FwdPass
  { fp_lattice = redundantBoundsLattice
  , fp_transfer = redundantCheckBoundsTransfer
  , fp_rewrite = redundantCheckBounds }
