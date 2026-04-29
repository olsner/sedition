{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantCheckBounds (redundantCheckBoundsPass) where

import Compiler.Hoopl as H hiding (joinMaps)

--import Debug.Trace

import Regex.IR
import Collections

-- Lower bound of checked bounds on all incoming paths, or Bot if no bounds
-- have been checked yet.
-- TODO Also track failed checks somehow?
-- TODO Needs to include Top, I think?
type RedundantBoundsFact = RegMap Int

redundantBoundsLattice :: DataflowLattice RedundantBoundsFact
redundantBoundsLattice = DataflowLattice
 { fact_name = "Redundant bounds check"
 , fact_bot  = mapEmpty
 , fact_join = joinMaps add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = min new old
              ch = changeIf (j /= old)

unknow dst f = mapInsert dst (-1) f

redundantCheckBoundsTransfer :: FwdTransfer Insn RedundantBoundsFact
redundantCheckBoundsTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> RedundantBoundsFact -> RedundantBoundsFact
    first _ f = f
    middle :: Insn O O -> RedundantBoundsFact -> RedundantBoundsFact
    middle (Set dst (src, m)) f
      | Just n <- mapLookup src f = mapInsert dst (max 0 (n - m)) f
      | otherwise                 = unknow dst f
    middle (Copy dst src)     f
      | Just n <- mapLookup src f = mapInsert dst n f
      | otherwise                 = unknow dst f
    middle (Clear dst)        f   = unknow dst f
    middle (InitCursor dst)   f   = unknow dst f
    middle _                  f   = f
    last :: Insn O C -> RedundantBoundsFact -> FactBase RedundantBoundsFact
    last (CheckBounds (r, n) eof cont) f =
      mkFactBase redundantBoundsLattice [(eof, f), (cont, mapInsert r n f)]
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase redundantBoundsLattice [(l, f) | l <- ls]

redundantCheckBounds :: FuelMonad m => FwdRewrite m Insn RedundantBoundsFact
redundantCheckBounds = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> RedundantBoundsFact -> m (Maybe (Graph Insn e x))
    rw (CheckBounds (r, n) _ cont) f | Just m <- mapLookup r f, n <= m = rwLast (Branch cont)
    rw _ _ = return Nothing

    rwLast insn = return (Just (mkLast insn))

redundantCheckBoundsPass :: FuelMonad m => FwdPass m Insn RedundantBoundsFact
redundantCheckBoundsPass = FwdPass
  { fp_lattice = redundantBoundsLattice
  , fp_transfer = redundantCheckBoundsTransfer
  , fp_rewrite = redundantCheckBounds }
