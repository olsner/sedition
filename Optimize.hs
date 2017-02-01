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
  return program

optToFix :: (CheckpointMonad m, FuelMonad m) => (Graph Insn O C -> m (Graph Insn O C)) -> Graph Insn O C -> m (Graph Insn O C)
optToFix f original = do
  oldFuel <- fuelRemaining
  optimized <- f original
  newFuel <- fuelRemaining
  trace ("optToFix: " ++ show newFuel ++ " remaining") $ return ()
  trace ("optToFix: " ++ showGraph showInsn optimized) $ return ()
  -- TODO Looks like we're consuming fuel despite not actually optimizing
  -- anything, somewhere, so a plain "newFuel == oldFuel" check doesn't work.
  if oldFuel == newFuel
    then return optimized
    else optToFix f optimized

optimize' :: (CheckpointMonad m, FuelMonad m) => Graph Insn O C -> m (Graph Insn O C)
optimize' = optToFix optimizeOnce

runSFM :: Fuel -> SimpleFuelMonad a -> a
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel m)

optimize p = runSFM (500 -32) (optimize' p)
