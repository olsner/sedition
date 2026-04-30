{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.PropagateRegister (propagateRegisterPass) where

import Compiler.Hoopl as H hiding (joinMaps)

import qualified Data.Map as M
--import Debug.Trace

import Regex.IR

import Collections

-- Map register to other register plus offset. Invalidation when modifying
-- registers might be tricky though.
type PropRegFact = RegMap (WithTop (R, Int))

propRegLattice :: DataflowLattice PropRegFact
propRegLattice = DataflowLattice
 { fact_name = "Propagate register offsets"
 , fact_bot  = mapEmpty
 , fact_join = joinMaps (extendJoinDomain add) }
 where add _ (OldFact old@(r1,d1)) (NewFact new@(r2,d2))
          | new == old = (NoChange, PElem old)
          -- Prefer to use common registers with higher offsets
          | r1 /= r2, d2 > d1 = (SomeChange, PElem new)
          | otherwise  = (SomeChange, Top)

-- TODO Needs a more efficient data structure!
-- e.g. track (reverse) dependencies in a RegMap RegSet as well?
update r new = mapInsert r new . const mapEmpty -- cleanup
  where
    cleanup :: PropRegFact -> PropRegFact
    cleanup  = mapFilter (\t -> case t of PElem (r2,_) -> r2 /= r; Top -> True)

propagateRegisterTransfer :: FwdTransfer Insn PropRegFact
propagateRegisterTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> PropRegFact -> PropRegFact
    first _ f = f
    middle :: Insn O O -> PropRegFact -> PropRegFact
    middle (Set r (r2,n)) f
      | r == r2             = update r Top f
      | otherwise           = update r (PElem (r2, n)) f
    middle (Copy r r2) f
      | r == r2             = update r Top f
      | otherwise           = update r (PElem (r2, 0)) f
    middle (Clear r) f      = update r Top f
    middle (InitCursor r) f = update r Top f
    middle _ f = f
    -- Final instructions never change the cursor.
    last :: Insn O C -> PropRegFact -> FactBase PropRegFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase propRegLattice [(l, f) | l <- ls]

propagateRegister :: FuelMonad m => FwdRewrite m Insn PropRegFact
propagateRegister = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> PropRegFact -> m (Maybe (Graph Insn e x))
    rw (Set r1 (r2,n)) f
      | Just (PElem (r3,d)) <- mapLookup r2 f, r3 < r1 = rwMid (Set r1 (r3, d + n))
    rw (Copy r1 r2) f
      | Just (PElem (r3,d)) <- mapLookup r2 f, r3 < r1 = rwMid (Set r1 (r3, d))
    rw (Set r1 (r2,0)) _ = rwMid (Copy r1 r2)
    rw (Switch (r1,n) table def) f
      | Just (PElem (r2,d)) <- mapLookup r1 f = rwLast (Switch (r2,d+n) table def)
    rw (TotalSwitch (r1,n) table) f
      | Just (PElem (r2,d)) <- mapLookup r1 f = rwLast (TotalSwitch (r2,d+n) table)
    rw (Match map) f
      | Just map' <- rewriteTagMap f map = rwLast (Match map')
    rw _ _ = return Nothing

    rwMid insn = return (Just (mkMiddle insn))
    rwLast insn = return (Just (mkLast insn))

rewriteTagMap f map | map' == map = Nothing
                    | otherwise = Just map'
  where
    map' = M.map t map
    t (Reg r d) | Just (PElem (r2,d2)) <- mapLookup r f = Reg r2 (d - d2)
                | otherwise = Reg r d

propagateRegisterPass :: FuelMonad m => FwdPass m Insn PropRegFact
propagateRegisterPass = FwdPass
  { fp_lattice = propRegLattice
  , fp_transfer = propagateRegisterTransfer
  , fp_rewrite = propagateRegister }
