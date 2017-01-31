{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module RedundantBranches (redundantBranchesPass) where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace

import Compiler.Hoopl

import IR

type RBFact = WithTop Label
lattice :: DataflowLattice RBFact
lattice = DataflowLattice
 { fact_name = "Const predicate"
 , fact_bot  = Top
 , fact_join = extendJoinDomain addFact }
 where
   addFact _ (OldFact old) (NewFact new)
       = if new == old then (NoChange, PElem new)
         else               (SomeChange, Top)

transfer :: BwdTransfer Insn RBFact
transfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> RBFact -> RBFact
    -- C O
    first (Label l) f = Top

    -- O O
    middle :: Insn O O -> RBFact -> RBFact
    middle _ f = Top

    -- O C
    last :: Insn O C -> FactBase RBFact -> RBFact
    last (Branch l) fb = PElem l
    last _ fb = Top

rewrite :: FuelMonad m => BwdRewrite m Insn RBFact
rewrite = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw (Branch t) f =
      case mapLookup t f of
        Just (PElem b) -> return (Just (mkLast (Branch b)))
        _ -> return Nothing

    rw _ f = return Nothing

redundantBranchesPass :: FuelMonad m => BwdPass m Insn RBFact
redundantBranchesPass = BwdPass
  { bp_lattice = lattice
  , bp_transfer = transfer
  , bp_rewrite = rewrite }


