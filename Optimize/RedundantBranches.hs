{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Optimize.RedundantBranches (redundantBranchesPass) where

import Compiler.Hoopl as H

-- import Debug.Trace

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
rewrite = deepBwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    -- Do just one change at a time so that optimization fuel applies.
    rw i@(If p tl fl) f | Just tl' <- label tl f = rwLast i (If p tl' fl)
                        | Just fl' <- label fl f = rwLast i (If p tl fl')
                        -- Branch to an if with the same condition, so we can
                        -- skip one step ahead.
                        | Just (If p' tl' _) <- insn tl f, p == p'
                                                 = rwLast i (If p tl' fl)
                        | Just (If p' _ fl') <- insn fl f, p == p'
                                                 = rwLast i (If p tl fl')
    rw i@(Fork l1 l2) f | Just l1' <- label l1 f = rwLast i (Fork l1' l2)
                        | Just l2' <- label l2 f = rwLast i (Fork l1 l2')
    rw i@(Branch t)   f                          = rwInsn i t f
    rw _ _ = return Nothing

    rwLast :: FuelMonad m => Insn O C -> Insn O C -> m (Maybe (Graph Insn O C))
    rwLast _old new = return (Just (mkLast new))

    rwInsn old l f | Just i <- insn l f = rwLast old i
                   | otherwise          = return Nothing

    insn l f | Just (PElem i) <- mapLookup l f = Just i
             | otherwise                       = Nothing

    label :: Label -> FactBase RBFact -> Maybe Label
    label l f | Just (PElem (Branch l')) <- mapLookup l f = Just l'
              | otherwise                                 = Nothing

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


