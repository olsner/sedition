{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.ConstRegister (constRegisterPass) where

import Compiler.Hoopl as H hiding (joinMaps)

import qualified Data.Map as M
import Debug.Trace

import Regex.IR

import Collections

data ConstRegValue = IsNil | NotNil deriving (Eq, Ord, Show)

-- Map register to other register plus offset. Invalidation when modifying
-- registers might be tricky though.
type ConstRegFact = RegMap (WithTop ConstRegValue)

propRegLattice :: DataflowLattice ConstRegFact
propRegLattice = DataflowLattice
 { fact_name = "Const register value(s)"
 , fact_bot  = mapEmpty
 , fact_join = joinMaps (extendJoinDomain add) }
 where
  add _ (OldFact old) (NewFact new)
          | new == old = (NoChange, PElem old)
          | otherwise  = (SomeChange, Top)

constRegisterTransfer :: FwdTransfer Insn ConstRegFact
constRegisterTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> ConstRegFact -> ConstRegFact
    first _ f = f
    middle :: Insn O O -> ConstRegFact -> ConstRegFact
    middle (Copy r r2) f
      | Just v <- mapLookup r2 f = mapInsert r v f
      | otherwise           = mapDelete r f
    middle (Clear r) f      = mapInsert r (PElem IsNil) f
    middle (SaveCursor r _) f = mapInsert r (PElem NotNil) f
    middle _ f = f
    last :: Insn O C -> ConstRegFact -> FactBase ConstRegFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase propRegLattice [(l, f) | l <- ls]

constRegister :: FuelMonad m => FwdRewrite m Insn ConstRegFact
constRegister = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> ConstRegFact -> m (Maybe (Graph Insn e x))
    rw (Copy dst src) f | Just (PElem IsNil) <- mapLookup src f = rwMid (Clear dst)
    -- LiveRegister also takes care of removing clears of unused tags
    -- rw (Clear dst) f | Just (PElem IsNil) <- mapLookup dst f = return (Just emptyGraph)
    rw (Match map) f | Just map' <- rewriteTagMap f map = rwLast (Match map')
    rw _ _ = return Nothing

    -- rwMid insn = trace ("ConstReg -> " ++ show insn) $ return (Just (mkMiddle insn))
    -- rwLast insn = trace ("ConstReg -> " ++ show insn) $ return (Just (mkLast insn))
    rwMid insn = return (Just (mkMiddle insn))
    rwLast insn = return (Just (mkLast insn))

rewriteTagMap f map | map' == map = Nothing
                    | otherwise = Just map'
  where
    map' = M.map t map
    t NoTag = NoTag
    t (Cursor d) = Cursor d
    t (Reg r d) | Just (PElem IsNil) <- mapLookup r f = NoTag
                | otherwise = Reg r d

enableTrace = False

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
  | enableTrace = debugFwdJoins trace ifChanged . debugFwdTransfers trace limitedShow (\insn _ -> interesting insn)
  | otherwise = id

constRegisterPass :: FuelMonad m => FwdPass m Insn ConstRegFact
constRegisterPass = addTracing $ FwdPass
  { fp_lattice = propRegLattice
  , fp_transfer = constRegisterTransfer
  , fp_rewrite = constRegister }
