{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.PropagateRegister (propagateRegisterPass) where

import Compiler.Hoopl as H hiding (joinMaps)

import qualified Data.Map as M
import Debug.Trace

import Regex.IR

import Collections

-- Map register to other register plus offset. Invalidation when modifying
-- registers might be tricky though.
type PropRegFact = (RegMap (WithTop (R, Int)), RegMap RegSet)

propRegLattice :: DataflowLattice PropRegFact
propRegLattice = DataflowLattice
 { fact_name = "Propagate register offsets"
 , fact_bot  = (mapEmpty, mapEmpty)
 , fact_join = join }
 where
  join l (OldFact (old, reverse)) (NewFact (new, _)) =
    case joinMaps (extendJoinDomain add) l (OldFact old) (NewFact new) of
      (NoChange, joined) -> (NoChange, (joined, reverse))
      (SomeChange, joined) -> (SomeChange, (joined, makeReverseMap joined))
  add _ (OldFact old) (NewFact new)
          | new == old = (NoChange, PElem old)
          | otherwise  = (SomeChange, Top)

addReverseMap :: R -> WithTop (R, Int) -> RegMap RegSet -> RegMap RegSet
addReverseMap _  Top = id
addReverseMap r1 (PElem (r2,_)) = mapInsertWith setUnion r2 (setSingleton r1)

makeReverseMap :: RegMap (WithTop (R, Int)) -> RegMap RegSet
makeReverseMap = mapFoldWithKey addReverseMap mapEmpty

update r new (f,rev) = (mapInsert r new (cleanup f), addReverseMap r new (mapDelete r rev))
  where
    invalidatedKeys = setElems (mapFindWithDefault setEmpty r rev)
    cleanup = mapInsertList [(k,Top) | k <- invalidatedKeys]

doLookup r (f,_) = mapLookup r f

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
      | r == r2             = trace "Copy to same register??" f
      | otherwise           = update r (PElem (r2, 0)) f
    middle (Clear r) f      = update r Top f
    middle (LoadCursor r) f = update r Top f
    middle _ f = f
    -- Final instructions never change the cursor.
    last :: Insn O C -> PropRegFact -> FactBase PropRegFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase propRegLattice [(l, f) | l <- ls]

propagateRegister :: FuelMonad m => FwdRewrite m Insn PropRegFact
propagateRegister = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> PropRegFact -> m (Maybe (Graph Insn e x))
    -- TODO Not very principled with just checking the index... The goal should
    -- be to maximize the offset to try to do as much as possible from the
    -- furthest-back register?
    rw (Set r1 (r2,n)) f
      | Just (PElem (r3,d)) <- doLookup r2 f, r3 < r1 = rwMid (Set r1 (r3, d + n))
    rw (Copy r1 r2) f
      | Just (PElem (r3,d)) <- doLookup r2 f, r3 < r1 = rwMid (Set r1 (r3, d))
    rw (Set r1 (r2,0)) _ = rwMid (Copy r1 r2)
    rw (Match map) f
      | Just map' <- rewriteTagMap f map = trace (show f) $ rwLast (Match map')
    rw _ _ = return Nothing

    rwMid insn = return (Just (mkMiddle insn))
    rwLast insn = return (Just (mkLast insn))

rewriteTagMap f map | map' == map = Nothing
                    | otherwise = Just map'
  where
    map' = M.map t map
    t (Reg r d) | Just (PElem (r2,d2)) <- doLookup r f = Reg r2 (d - d2)
                | otherwise = Reg r d

enableTrace = True

interesting (Set _ _) = False
interesting (Copy _ _) = True
interesting (Clear _) = True
interesting (SaveCursor _ _) = True
interesting (LoadCursor _) = True
interesting (MoveCursor _) = True
interesting (Match _) = True
interesting _ = False

ifChanged SomeChange = True
ifChanged NoChange = False

limitedShow :: Show a => a -> String
limitedShow = take 100 . show

addTracing
  | enableTrace = debugFwdJoins trace (const False) . debugFwdTransfers trace limitedShow (\insn _ -> interesting insn)
  | otherwise = id

propagateRegisterPass :: FuelMonad m => FwdPass m Insn PropRegFact
propagateRegisterPass = addTracing $ FwdPass
  { fp_lattice = propRegLattice
  , fp_transfer = propagateRegisterTransfer
  , fp_rewrite = propagateRegister }
