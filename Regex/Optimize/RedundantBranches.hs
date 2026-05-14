{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantBranches (redundantBranchesPass) where

import Compiler.Hoopl as H

import Data.Bits
import Data.Word

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
    rw i@(IfBOL tl fl) f
        | Just tl' <- label tl f     = rwLast i (IfBOL tl' fl)
        | Just fl' <- label fl f     = rwLast i (IfBOL tl fl')
    rw i@(CheckBounds n l1 l2) f
        | Just l1' <- label l1 f     = rwLast i (CheckBounds n l1' l2)
        | Just l2' <- label l2 f     = rwLast i (CheckBounds n l1 l2')
    rw i@(Switch offset cm l) f
        | CM.null cm                 = rwLast i (Branch l)
        | Just l'  <- label l f      = rwLast i (Switch offset cm l')
        -- Single target label matches the default-branch
        | Just l == oneLabel cm      = rwLast i (Branch l)
        | Just cm' <- mapLabels cm f = rwLast i (Switch offset cm' l)
    rw i@(TotalSwitch offset m) f
        | Just l' <- oneLabel m      = rwLast i (Branch l')
        | Just m' <- mapLabels m f   = rwLast i (TotalSwitch offset m')
    rw i@(CmpByte p c tl fl) f
        | Just tl' <- label tl f     = rwLast i (CmpByte p c tl' fl)
        | Just fl' <- label fl f     = rwLast i (CmpByte p c tl fl')
    rw i@(CmpWord p c tl fl) f
        | Just tl' <- label tl f     = rwLast i (CmpWord p c tl' fl)
        | Just fl' <- label fl f     = rwLast i (CmpWord p c tl fl')
    rw i@(CmpDWord p c tl fl) f
        | Just tl' <- label tl f     = rwLast i (CmpDWord p c tl' fl)
        | Just fl' <- label fl f     = rwLast i (CmpDWord p c tl fl')
    rw i@(Branch t) f                = rwInsn i t f
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

    mapLabels :: CharMap Label -> FactBase RBFact -> Maybe (CharMap Label)
    mapLabels cm f | cm' == cm = Nothing
                   | otherwise = Just cm'
      -- TODO Add map function instead of using traverse
      where Just cm' = CM.traverse fun cm
            fun l | Just l' <- label l f = Just l'
                  | otherwise            = Just l

    oneLabel cm | [(_,label)] <- CM.toRanges cm = Just label
                | otherwise                     = Nothing

simplifySameIfs :: FuelMonad m => BwdRewrite m Insn RBFact
simplifySameIfs = deepBwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw (IfBOL tl fl)         f = rwSame tl fl f
    rw (CheckBounds _ tl fl) f = rwSame tl fl f
    rw (CmpByte _ _ tl fl)   f = rwSame tl fl f
    rw (CmpWord _ _ tl fl)   f = rwSame tl fl f
    rw (CmpDWord _ _ tl fl)  f = rwSame tl fl f
    rw _                     _ = return Nothing

    rwSame tl fl f | tl == fl = rwLast (Branch tl)
                   | Just i' <- same tl fl f = rwLast i'
                   | otherwise = return Nothing

    same l1 l2 f | Just i1 <- insn l1 f, Just i2 <- insn l2 f,
                   i1 == i2  = Just i1
                 | otherwise = Nothing

    insn l f | Just (PElem i) <- mapLookup l f = Just i
             | otherwise                       = Nothing

    rwLast new = return (Just (mkLast new))

w16 :: Word8 -> Word16
w16 = toEnum . fromEnum
w32 :: Word16 -> Word32
w32 = toEnum . fromEnum
-- Assumes little-endian output.
combine8 :: Word8 -> Word8 -> Word16
combine8 i j = (w16 j `shiftL` 8) .|. w16 i
combine16 :: Word16 -> Word16 -> Word32
combine16 i j = (w32 j `shiftL` 16) .|. w32 i

combineCompares :: FuelMonad m => BwdRewrite m Insn RBFact
combineCompares = deepBwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x RBFact -> m (Maybe (Graph Insn e x))
    rw i@(CmpByte _ _ t _) f
      | Just (PElem j@(CmpByte _ _ _ _)) <- mapLookup t f = tryCombine i j
    rw i@(CmpWord _ _ t _) f
      | Just (PElem j@(CmpWord _ _ _ _)) <- mapLookup t f = tryCombine i j
    rw _                   _ = return Nothing

    -- Only handle adjacent positions (in order for now - flipping would be
    -- trivial though).
    -- The not-equal label has to be the same.
    tryCombine :: FuelMonad m => Insn O C -> Insn O C -> m (Maybe (Graph Insn O C))
    tryCombine (CmpByte p1 c1 _ f1) (CmpByte p2 c2 t2 f2)
      | p2 == p1 + 1, f1 == f2 = rwLast (CmpWord p1 (combine8 c1 c2) t2 f1)
    tryCombine (CmpWord p1 w1 _ f1) (CmpWord p2 w2 t2 f2)
      | p2 == p1 + 2, f1 == f2 = rwLast (CmpDWord p1 (combine16 w1 w2) t2 f1)
    tryCombine _ _ = return Nothing

    rwLast new = return (Just (mkLast new))

redundantBranchesPass :: FuelMonad m => BwdPass m Insn RBFact
redundantBranchesPass = BwdPass
  { bp_lattice = lattice
  , bp_transfer = transfer
  , bp_rewrite = rewrite `thenBwdRw` simplifySameIfs `thenBwdRw` combineCompares }

