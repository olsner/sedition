{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, ScopedTypeVariables, FlexibleContexts #-}

module Optimize (optimize) where

import Compiler.Hoopl as H hiding ((<*>))

--import Data.Map (Map)
--import qualified Data.Map as M
--import Debug.Trace

import IR

import ConstPred (constPredPass)
import LivePred (livePredPass)
import LiveString (liveStringPass)
import SameString (sameStringPass)
import RedundantBranches (redundantBranchesPass)

--debugBwd = debugBwdJoins trace (const True)
--debugBwd = debugBwdTransfers trace showInsn (\n f -> True)
--debugBwd = id

optimizeOnce :: (CheckpointMonad m, FuelMonad m) => Label -> Graph Insn C C -> m (Graph Insn C C)
optimizeOnce entry program = do
  let entries = JustC [entry]
  (program,_,_) <- analyzeAndRewriteBwd livePredPass entries program mapEmpty
  (program,_,_) <- analyzeAndRewriteFwd constPredPass entries program mapEmpty
  (program,_,_) <- analyzeAndRewriteBwd redundantBranchesPass entries program mapEmpty
  -- Realized this isn't safe yet, it doesn't track modifications to variables
  -- it is optimizing other variables to. (e.g. the hold/pattern swap would
  -- optimize down to everything getting set to either of the inputs).
  -- (program,_,_) <- analyzeAndRewriteFwd sameStringPass entries program mapEmpty
  (program,_,_) <- analyzeAndRewriteBwd liveStringPass entries program mapEmpty
  return program

optToFix f original = do
  oldFuel <- fuelRemaining
  -- If we've already ran out of fuel, the optimizations will run but do
  -- nothing, which we'll consider a fixpoint since oldFuel == newFuel == 0.
  optimized <- f original
  newFuel <- fuelRemaining
  --trace ("optToFix: " ++ show (oldFuel - newFuel) ++ " fuel consumed") $ return ()
  -- Ugly workaround, but compare the optimized text program to see if optimization changed something.
  -- Looks like we have optimizations that toggle and consume fuel to produce the same output.
  if oldFuel == newFuel || show original == show optimized
    then return optimized
    else optToFix f optimized

optimize' :: (CheckpointMonad m, FuelMonad m) => (Label, Graph Insn C C) -> m (Graph Insn C C)
optimize' (entry, program) = optToFix (optimizeOnce entry) program

runSFM :: Fuel -> SimpleFuelMonad a -> (a, Fuel)
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel ((,) <$> m <*> fuelRemaining))

optimize fuel p = runSFM fuel (optimize' p)
