{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module RedundantBranches (redundantBranchesPass) where

import Compiler.Hoopl as H

--import Debug.Trace

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
    first (Label _) f = f

    -- O O
    middle :: Insn O O -> RBFact -> RBFact
    middle _ _ = Top

    -- O C
    last :: Insn O C -> FactBase RBFact -> RBFact
    last insn _ = PElem insn

rewrite :: FuelMonad m => BwdRewrite m Insn RBFact
rewrite = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    -- Replaces a branch to any control-flow with a copy of the control-flow
    rw old@(Branch t) f | Just (PElem new) <- mapLookup t f = rwLast old new
    -- Replaces only branch-to-branch with a branch to the target.
    -- Redundant usually, unless rwLast rejected the rewrite above.
    rw old@(Branch t) f = rwLast old (Branch (label t f))
    rw old@(If p tl fl) f = rwLast old (If p (label tl f) (label fl f))
    rw old@(Fork l1 l2) f = rwLast old (Fork (label l1 f) (label l2 f))
    rw old@(Cycle fd l1 l2 l3) f = rwLast old (Cycle fd (label l1 f) (label l2 f) (label l3 f))
    rw _ _ = return Nothing

    rwLast :: FuelMonad m => Insn O C -> Insn O C -> m (Maybe (Graph Insn O C))
    -- Mainly for esthetics, don't copy Cycle into a Branch
    rwLast (Branch _) (Cycle _ _ _ _) = return Nothing
    rwLast old new
        | old /= new = return (Just (mkLast new))
        | otherwise  = return Nothing

    label :: Label -> FactBase RBFact -> Label
    label l f | Just (PElem (Branch b)) <- mapLookup l f = b
              | otherwise = l

simplifySameIfs :: FuelMonad m => BwdRewrite m Insn RBFact
simplifySameIfs = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw (If _ tl fl) _ | tl == fl = return (Just (mkLast (Branch tl)))
    rw _ _ = return Nothing

redundantBranchesPass :: FuelMonad m => BwdPass m Insn RBFact
redundantBranchesPass = BwdPass
  { bp_lattice = lattice
  , bp_transfer = transfer
  , bp_rewrite = rewrite `thenBwdRw` simplifySameIfs }


