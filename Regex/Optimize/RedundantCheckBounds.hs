{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.RedundantCheckBounds (redundantCheckBoundsPass) where

import Compiler.Hoopl as H

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
joinBounds (Lt m) (Lt n)                   = Just (Lt (min m n))
joinBounds (Lt m) (GE n)          | n < m  = Just (Between n m)
joinBounds (Lt m) (Between lb ub) | lb < m = Just (Between lb (min m ub))
joinBounds (GE m) (Lt n)          | m < n  = Just (Between m n)
joinBounds (GE m) (GE n)                   = Just (GE (max m n))
joinBounds (GE m) (Between lb ub) | m < ub = Just (Between (max m lb) ub)
joinBounds (Between l1 u1) (Between l2 u2)
                   | max l1 l2 < min u1 u2 = Just (Between (max l1 l2) (min u1 u2))
joinBounds (Between lb ub) (Lt n) | lb < n = Just (Between lb (min ub n))
joinBounds (Between lb ub) (GE n) | n < ub = Just (Between (max lb n) ub)
joinBounds lhs rhs = Nothing

offsetBound :: Bounds -> Int -> Bounds
offsetBound b n = case b of
  Lt m -> Lt (max 0 (m - n))
  GE m -> GE (max 0 (m - n))
  Between lb ub -> Between (max 0 (lb - n)) (max 0 (ub - n))

-- Lower bound of checked bounds on all incoming paths, not present if no bounds
-- have been checked yet, Top if the register has changed without getting
-- checked or on conflicting incoming information.
type RedundantBoundsFact = RegMap Bounds

redundantBoundsLattice :: DataflowLattice RedundantBoundsFact
redundantBoundsLattice = DataflowLattice
 { fact_name = "Redundant bounds check"
 , fact_bot  = mapEmpty
 , fact_join = joinIntersectMaps add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = joinBounds old new
              ch = changeIf (j /= Just old)

type MaybeJoinFun a = Label -> OldFact a -> NewFact a -> (ChangeFlag, Maybe a)

-- JoinMaps where not present means the same as Top
-- Which is probably wrong too! fact_bot is mapEmpty so we just get nothing out.
joinIntersectMaps :: IsMap m => MaybeJoinFun v -> JoinFun (m v)
joinIntersectMaps eltJoin l (OldFact old) (NewFact new) = mapFoldWithKey add (NoChange, mapIntersection old new) (mapIntersection new old)
  where
    add k new_v (ch, joinmap) =
      case mapLookup k joinmap of
        Nothing    -> (SomeChange, mapInsert k new_v joinmap)
        Just old_v -> case eltJoin l (OldFact old_v) (NewFact new_v) of
                        (SomeChange, Just v') -> (SomeChange, mapInsert k v' joinmap)
                        (SomeChange, Nothing) -> (SomeChange, mapDelete k joinmap)
                        (NoChange,   _)  -> (ch, joinmap)

insertOrDelete :: IsMap m => KeyOf m -> Maybe a -> m a -> m a
insertOrDelete k Nothing m  = mapDelete k m
insertOrDelete k (Just v) m = mapInsert k v m

redundantCheckBoundsTransfer :: FwdTransfer Insn RedundantBoundsFact
redundantCheckBoundsTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> RedundantBoundsFact -> RedundantBoundsFact
    first _ f = f
    middle :: Insn O O -> RedundantBoundsFact -> RedundantBoundsFact
    middle (Set dst (src, n)) f
      | Just b <- mapLookup src f = mapInsert dst (offsetBound b n) f
      | otherwise                 = mapDelete dst f
    middle (Copy dst src)     f
      | Just b <- mapLookup src f = mapInsert dst b f
      | otherwise                 = mapDelete dst f
    middle (Clear dst)        f   = mapDelete dst f
    middle (InitCursor dst)   f   = mapDelete dst f
    middle _                  f   = f
    last :: Insn O C -> RedundantBoundsFact -> FactBase RedundantBoundsFact
    last (CheckBounds (r, n) eof cont) f
      | Just b <- mapLookup r f =
        factBase [(eof, insertOrDelete r (joinBounds (Lt n) b) f),
                  (cont, insertOrDelete r (joinBounds (GE n) b) f)]
      | otherwise =
        factBase [(eof, mapInsert r (Lt n) f),
                  (cont, mapInsert r (GE n) f)]
    last insn f = boringFactBase f (successors insn)

    factBase = mkFactBase redundantBoundsLattice
    boringFactBase f ls = factBase [(l, f) | l <- ls]

redundantCheckBounds :: FuelMonad m => FwdRewrite m Insn RedundantBoundsFact
redundantCheckBounds = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> RedundantBoundsFact -> m (Maybe (Graph Insn e x))
    rw (CheckBounds (r, n) eof cont) f
      | Just b <- mapLookup r f = case checkBound n b of
          EOF ->  rwLast (Branch eof)
          Cont -> rwLast (Branch cont)
          _ -> return Nothing
    rw _ _ = return Nothing

    rwLast insn = return (Just (mkLast insn))

enableTrace = True

interesting (CheckBounds _ _ _) = True
interesting (Set _ _) = True
interesting (Copy _ _) = True
interesting (Clear _) = True
interesting (InitCursor _) = True
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
