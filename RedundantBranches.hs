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

type RBFact = WithTopAndBot (Insn O C)
lattice :: DataflowLattice RBFact
lattice = addPoints "Redundant branches" join
 where
   join _ (OldFact old) (NewFact new)
       = if new == old then (NoChange, new)
         else               (SomeChange, new)

transfer :: BwdTransfer Insn RBFact
transfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> RBFact -> RBFact
    -- C O
    first (Label l) f = f

    -- O O
    middle :: Insn O O -> RBFact -> RBFact
    middle _ f = Top

    -- O C
    last :: Insn O C -> FactBase RBFact -> RBFact
    last insn fb = PElem insn

rewrite :: FuelMonad m => BwdRewrite m Insn RBFact
rewrite = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw old@(Branch t) f | Just (PElem new) <- mapLookup t f = rwLast old new
    rw old@(If p tl fl) f = rwLast old (If p (label tl f) (label fl f))
    rw old@(Fork l1 l2) f = rwLast old (Fork (label l1 f) (label l2 f))
    rw old@(Read fd (Just l1) l2) f = rwLast old (Read fd (Just (label l1 f)) (label l2 f))
    rw _ f = return Nothing

    rwLast :: FuelMonad m => Insn O C -> Insn O C -> m (Maybe (Graph Insn O C))
    rwLast old new = --trace ("rewrite: " ++ show old ++ " -> " ++ show new) $
        if old == new then return Nothing else return (Just (mkLast new))

    label :: Label -> FactBase RBFact -> Label
    label l f | Just (PElem (Branch b)) <- mapLookup l f = b
              | otherwise = l

simplifySameIfs :: FuelMonad m => BwdRewrite m Insn RBFact
simplifySameIfs = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw i@(If p tl fl) f | tl == fl = trace ("simplifySameIf: " ++ show i) $ return (Just (mkLast (Branch tl)))
    rw _ f = return Nothing

redundantBranchesPass :: FuelMonad m => BwdPass m Insn RBFact
redundantBranchesPass = BwdPass
  { bp_lattice = lattice
  , bp_transfer = transfer
  , bp_rewrite = rewrite `thenBwdRw` simplifySameIfs }


