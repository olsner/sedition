{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module RedundantBranches (redundantBranchesPass) where

import Compiler.Hoopl as H

--import Debug.Trace

import IR

type RBFact = WithTopAndBot Label
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
    last (Branch t) _ = PElem t
    last _          _ = Top

rewrite :: FuelMonad m => BwdRewrite m Insn RBFact
rewrite = deepBwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    -- Replaces a branch to any control-flow with a copy of the control-flow
    rw old@(Branch t) f
        | Just t' <- label t f = rwLast (Branch t')
    -- Replaces only branch-to-branch with a branch to the target.
    -- Redundant usually, unless rwLast rejected the rewrite above.
    rw old@(Branch t) f
        | Just t' <- label t f = rwLast (Branch t')
    rw old@(If p tl fl) f
        | Just tl' <- label tl f = rwLast (If p tl' fl)
        | Just fl' <- label fl f = rwLast (If p tl fl')
    rw old@(Fork l1 l2) f
        | Just l1' <- label l1 f = rwLast (Fork l1' l2)
        | Just l2' <- label l2 f = rwLast (Fork l1 l2')
    rw _ _ = return Nothing

    rwLast :: FuelMonad m => Insn O C -> m (Maybe (Graph Insn O C))
    rwLast new = return (Just (mkLast new))

    label :: Label -> FactBase RBFact -> Maybe Label
    label l f | Just (PElem l') <- mapLookup l f = Just l'
              | otherwise = Nothing

simplifySameIfs :: FuelMonad m => BwdRewrite m Insn RBFact
simplifySameIfs = deepBwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw (If _ tl fl) _ | tl == fl = return (Just (mkLast (Branch tl)))
    rw _ _ = return Nothing

redundantBranchesPass :: FuelMonad m => BwdPass m Insn RBFact
redundantBranchesPass = BwdPass
  { bp_lattice = lattice
  , bp_transfer = transfer
  , bp_rewrite = rewrite `thenBwdRw` simplifySameIfs }


