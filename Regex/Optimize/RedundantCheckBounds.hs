{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantCheckBounds (redundantCheckBoundsPass) where

import Compiler.Hoopl as H hiding (joinMaps)

import Debug.Trace

import Regex.IR
import Collections

-- Lt x = Less than x characters remain  => len < x
-- GE x = At least x characters remain   => x <= len
-- Between lb ub = At least lb and less than ub characters remain
--    Between lb ub <=> Lt ub ^ GE lb    => lb <= len < ub
data Bounds = Lt Int | GE Int | Between Int Int deriving (Show,Ord,Eq)

-- Result of checking a bounds-check against known bounds
data Check
  = Unknown  -- ^ Can't tell which way the branch goes
  | EOF      -- ^ We know too few characters remain so EOF
  | Cont     -- ^ Check successful, not at EOF yet
  deriving (Show,Ord,Eq)

checkBound n (Lt m)          | n >= m  = EOF
checkBound n (GE m)          | n <= m  = Cont
checkBound n (Between lb ub) | n < lb  = Cont
                             | n >= ub = EOF
checkBound _ _                         = Unknown

-- Produce a bound that satisfies both conditions
-- Produce Top if the bounds are in conflict
joinBounds (Lt m) (Lt n)                   = PElem (Lt (min m n))
joinBounds (Lt m) (GE n)          | n < m  = PElem (Between n m)
joinBounds (Lt m) (Between lb ub) | lb < m = PElem (Between lb (min m ub))
joinBounds (GE m) (Lt n)          | m < n  = PElem (Between m n)
joinBounds (GE m) (GE n)                   = PElem (GE (max m n))
joinBounds (GE m) (Between lb ub) | m < ub = PElem (Between (max m lb) ub)
joinBounds (Between l1 u1) (Between l2 u2)
                   | max l1 l2 < min u1 u2 = PElem (Between (max l1 l2) (min u1 u2))
joinBounds (Between lb ub) (Lt n) | lb < n = PElem (Between lb (min ub n))
joinBounds (Between lb ub) (GE n) | n < ub = PElem (Between (max lb n) ub)
joinBounds lhs rhs = Top

offsetBound :: Bounds -> Int -> Bounds
offsetBound b n = case b of
  Lt m -> Lt (max 0 (m - n))
  GE m -> GE (max 0 (m - n))
  Between lb ub -> Between (max 0 (lb - n)) (max 0 (ub - n))

-- Combination of checked bounds on all incoming paths, not present if no bounds
-- have been checked yet, Top if the register has changed without getting
-- checked or on conflicting incoming information.
type RedundantBoundsFact = WithTopAndBot Bounds

redundantBoundsLattice :: DataflowLattice RedundantBoundsFact
redundantBoundsLattice = addPoints' "Redundant bounds check" add
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = joinBounds old new
              ch = changeIf (j /= PElem old)

redundantCheckBoundsTransfer :: FwdTransfer Insn RedundantBoundsFact
redundantCheckBoundsTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> RedundantBoundsFact -> RedundantBoundsFact
    first _ f = f
    middle :: Insn O O -> RedundantBoundsFact -> RedundantBoundsFact
    middle (MoveCursor n) (PElem b) = PElem (offsetBound b n)
    middle (LoadCursor _) f = Top
    middle _              f = f
    last :: Insn O C -> RedundantBoundsFact -> FactBase RedundantBoundsFact
    last (CheckBounds n eof cont) (PElem b) =
        factBase [(eof, joinBounds (Lt n) b), (cont, joinBounds (GE n) b)]
    last (CheckBounds n eof cont) _ =
        factBase [(eof, PElem (Lt n)), (cont, PElem (GE n))]
    last insn f = boringFactBase f (successors insn)

    factBase = mkFactBase redundantBoundsLattice
    boringFactBase f ls = factBase [(l, f) | l <- ls]

redundantCheckBounds :: FuelMonad m => FwdRewrite m Insn RedundantBoundsFact
redundantCheckBounds = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> RedundantBoundsFact -> m (Maybe (Graph Insn e x))
    rw orig@(CheckBounds n eof cont) (PElem b) = case checkBound n b of
          EOF ->  rwLast orig (Branch eof)
          Cont -> rwLast orig (Branch cont)
          _ -> return Nothing
    rw _ _ = return Nothing

    rwLast orig insn = trace ("rewrite: " ++ show orig ++ "  -->  " ++ show insn) $ return (Just (mkLast insn))

enableTrace = False

interesting (CheckBounds _ _ _) = True
interesting (MoveCursor _) = True
interesting (LoadCursor _) = True
interesting _ = False

ifChanged SomeChange = True
ifChanged NoChange = False

limitedShow :: Show a => a -> String
limitedShow = take 100 . show

addTracing
  | enableTrace = debugFwdJoins trace ifChanged . debugFwdTransfers trace limitedShow (\insn _ -> interesting insn)
  | otherwise = id

redundantCheckBoundsPass :: FuelMonad m => FwdPass m Insn RedundantBoundsFact
redundantCheckBoundsPass = addTracing $ FwdPass
  { fp_lattice = redundantBoundsLattice
  , fp_transfer = redundantCheckBoundsTransfer
  , fp_rewrite = redundantCheckBounds }
