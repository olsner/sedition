{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, ScopedTypeVariables, FlexibleContexts #-}

module Optimize where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace

import Parser

import qualified AST

import Compiler.Hoopl

import IR

import ConstPred (constPredPass)
import RedundantBranches (redundantBranchesPass)

-- More passes:
--  dead pred elimination, as Ifs get removed some predicates become unused too
--    and could be removed
--  line number counting
--

--debugBwd = debugBwdJoins trace (const True)
--debugBwd = debugBwdTransfers trace showInsn (\n f -> True)

stripUnused :: Graph Insn e x -> Graph Insn e x
stripUnused g = deleteLabels g (labelsDefined g `setDifference` labelsUsed g)

deleteLabels :: Graph Insn e x -> LabelSet -> Graph Insn e x
deleteLabels GNil ls = GNil
deleteLabels g@(GUnit {}) ls = g
deleteLabels (GMany e body f) ls = GMany e body' f
  where
    body' = mapDeleteList (setElems ls) body

-- Since redundantBranches may produce more opportunities for const predicates
-- (and vice versa), run this at least twice. (Could run to fixpoint instead?)
optimizeOnce :: (CheckpointMonad m, FuelMonad m) => Graph Insn O C -> m (Graph Insn O C)
optimizeOnce program = do
  (program,_,_) <- analyzeAndRewriteFwdOx constPredPass program M.empty
  (program,_,_) <- analyzeAndRewriteBwdOx redundantBranchesPass program mapEmpty
  return (stripUnused program)

optimize' :: (CheckpointMonad m, FuelMonad m) => Graph Insn O C -> m (Graph Insn O C)
optimize' = optimizeOnce >=> optimizeOnce

runSFM :: Fuel -> SimpleFuelMonad a -> a
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel m)

optimize fuel p = runSFM fuel (optimize' p)
