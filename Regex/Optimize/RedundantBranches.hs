{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantBranches (redundantBranchesPass) where

import Compiler.Hoopl as H

import Debug.Trace

import qualified CharMap as CM
import CharMap (CharMap)
import Regex.IR

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
    rw i@(IfBOL tl fl) f | Just tl' <- label tl f = rwLast i (IfBOL tl' fl)
                         | Just fl' <- label fl f = rwLast i (IfBOL tl fl')
    rw i@(CheckBounds n l1 l2) f
                         | Just l1' <- label l1 f = rwLast i (CheckBounds n l1' l2)
                         | Just l2' <- label l2 f = rwLast i (CheckBounds n l1 l2')
    rw i@(Switch cm l) f | CM.null cm             = rwLast i (Branch l)
                         | Just l'  <- label l f  = rwLast i (Switch cm l')
                         -- Single target label matches the default-branch
                         | Just l == oneLabel cm  = rwLast i (Branch l)
                         | Just cm' <- mapLabels cm f = rwLast i (Switch cm' l)
    rw i@(TotalSwitch m) f
                         | Just l' <- oneLabel m  = rwLast i (Branch l')
                         | Just m' <- mapLabels m f = rwLast i (TotalSwitch m')
    rw i@(Branch t)    f                          = rwInsn i t f
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

    -- Doesn't seem to ever actually do anything?
    mapLabels :: CharMap Label -> FactBase RBFact -> Maybe (CharMap Label)
    mapLabels cm f | cm' == cm = Nothing
                   | otherwise = trace ("Found switch label rewrite! " ++ show cm ++ " -> " ++ show cm') $ Just cm'
      -- TODO Add map function instead of using traverse
      where Just cm' = CM.traverse fun cm
            fun l | Just l' <- label l f = trace ("Found switch label rewrite! " ++ show l ++ " -> " ++ show l') $ Just l'
                  -- The SameResult optimization produces this case now, so
                  -- skip tracing.
                  -- | Just _  <- insn l f  = trace ("can't have instruction in switch, but: " ++ show l ++ " -> " ++ show i) $ Just l
                  | otherwise            = Just l

    oneLabel cm | [(_,label)] <- CM.toRanges cm = Just label
                | otherwise                     = Nothing

simplifySameIfs :: FuelMonad m => BwdRewrite m Insn RBFact
simplifySameIfs = deepBwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw (IfBOL tl fl)         f | tl == fl = rwLast (Branch tl)
                               | Just i' <- same tl fl f = rwLast i'
    rw (CheckBounds _ tl fl) f | tl == fl = rwLast (Branch tl)
                               | Just i' <- same tl fl f = rwLast i'
    rw _ _ = return Nothing

    same l1 l2 f | Just i1 <- insn l1 f, Just i2 <- insn l2 f,
                   i1 == i2  = Just i1
                 | otherwise = Nothing

    insn l f | Just (PElem i) <- mapLookup l f = Just i
             | otherwise                       = Nothing

    rwLast new = return (Just (mkLast new))

redundantBranchesPass :: FuelMonad m => BwdPass m Insn RBFact
redundantBranchesPass = BwdPass
  { bp_lattice = lattice
  , bp_transfer = transfer
  , bp_rewrite = rewrite `thenBwdRw` simplifySameIfs }

