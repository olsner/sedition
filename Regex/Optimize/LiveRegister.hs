{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.LiveRegister (liveRegisterPass) where

import Compiler.Hoopl as H

import qualified Data.Map as M
import Data.Maybe (mapMaybe)
--import Debug.Trace

import Collections
import Regex.IR

type LiveRegFact = RegSet
liveLattice :: DataflowLattice LiveRegFact
liveLattice = DataflowLattice
 { fact_name = "Live register"
 , fact_bot  = setEmpty
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `setUnion` old
              ch = changeIf (setSize j > setSize old)

kill :: Insn e x -> LiveRegFact -> LiveRegFact
kill (Set r)    = setDelete r
kill (Clear r)  = setDelete r
kill (Copy r _) = setDelete r
kill _          = id

gen :: Insn e x -> LiveRegFact -> LiveRegFact
gen (Copy _ r)     f = setInsert r f
gen (Match tagMap) f = setUnion f (setFromList (mapMaybe reg (M.elems tagMap)))
  where reg (Reg r _)      = Just r
        reg (EndOfMatch _) = Nothing
gen _              f = f

liveRegisterTransfer :: BwdTransfer Insn LiveRegFact
liveRegisterTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LiveRegFact -> LiveRegFact
    first (Label _)  f = f
    middle :: Insn O O -> LiveRegFact -> LiveRegFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LiveRegFact -> LiveRegFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact f l = mapFindWithDefault setEmpty l f
    facts ls f = setUnions (map (fact f) ls)

liveRegister :: FuelMonad m => BwdRewrite m Insn LiveRegFact
liveRegister = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LiveRegFact -> m (Maybe (Graph Insn e x))
    rw (Set r)    f | not (setMember r f) = return (Just emptyGraph)
    rw (Clear r)  f | not (setMember r f) = return (Just emptyGraph)
    rw (Copy r _) f | not (setMember r f) = return (Just emptyGraph)
    rw _ _ = return Nothing

liveRegisterPass :: FuelMonad m => BwdPass m Insn LiveRegFact
liveRegisterPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveRegisterTransfer
  , bp_rewrite = liveRegister }


