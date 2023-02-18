{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, ScopedTypeVariables, FlexibleContexts #-}

module Optimize (optimize) where

import Compiler.Hoopl as H hiding ((<*>))

import Debug.Trace

import IR

import ConstPred (constPredPass)
import LivePred (livePredPass)
import LiveString (liveStringPass)
--import SameString (sameStringPass)
import RedundantBranches (redundantBranchesPass)
-- TODO Add liveness pass for match registers
import LiveLastRegex (liveLastRegexPass, constLastRegexPass)

--debugBwd = debugBwdJoins trace (const True)
--debugBwd = debugBwdTransfers trace showInsn (\n f -> True)
--debugBwd = id

doTrace = False

traceFuel :: FuelMonad m => Int -> m ()
traceFuel oldFuel = do
  fuel <- fuelRemaining
  trace (show (oldFuel - fuel) ++ " fuel consumed") (return ())

tracePass name pass | doTrace = do
  oldFuel <- fuelRemaining
  (program,_,_) <- trace ("Optimizing program: " ++ show name ++ "...") pass
  traceFuel oldFuel
  trace (show (setSize (labelsDefined program)) ++ " labels defined, " ++
         show (setSize (labelsUsed program)) ++ " labels used") $ return ()
  trace (show (length (show program))) $ return ()
  return program
                    | otherwise = do
  (program,_,_) <- pass
  return program

optimizeOnce :: (CheckpointMonad m, FuelMonad m) => Label -> Graph Insn C C -> m (Graph Insn C C)
optimizeOnce entry program = do
  let entries = JustC [entry]
  -- If this can eliminate something, constPred should have fewer predicates to
  -- worry about.
  program <- tracePass "livePred" $
    analyzeAndRewriteBwd livePredPass entries program mapEmpty
  program <- tracePass "constPred" $
    analyzeAndRewriteFwd constPredPass entries program mapEmpty
  program <- tracePass "livePred" $
    analyzeAndRewriteBwd livePredPass entries program mapEmpty
  program <- tracePass "redundantBranches" $
    analyzeAndRewriteBwd redundantBranchesPass entries program mapEmpty
  program <- tracePass "liveString" $
    analyzeAndRewriteBwd liveStringPass entries program mapEmpty
  program <- tracePass "constLastRegex" $
    analyzeAndRewriteFwd constLastRegexPass entries program mapEmpty
  program <- tracePass "liveLastRegex" $
    analyzeAndRewriteBwd liveLastRegexPass entries program mapEmpty
  -- This doesn't seem to do much for runtime, so skip it. Should be more
  -- relevant when we try to analyze the contents of strings though.
  --(program,_,_) <- analyzeAndRewriteFwd sameStringPass entries program mapEmpty
  return program

optToFix f original = do
  oldFuel <- fuelRemaining
  -- If we've already ran out of fuel, the optimizations will run but do
  -- nothing, which we'll consider a fixpoint since oldFuel == newFuel == 0.
  optimized <- f original
  newFuel <- fuelRemaining
  -- Ugly workaround, but compare the optimized text program to see if
  -- optimization changed something.
  -- Hoopl passes may consume fuel on speculative rewrites that won't stick
  -- around in the final output.
  if oldFuel == newFuel || newFuel == 0 || show original == show optimized
    then return optimized
    else optToFix f optimized

optimize' :: (CheckpointMonad m, FuelMonad m) => (Label, Graph Insn C C) -> m (Graph Insn C C)
optimize' (entry, program) = optToFix (optimizeOnce entry) program

runSFM :: Fuel -> SimpleFuelMonad a -> (a, Fuel)
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel ((,) <$> m <*> fuelRemaining))

optimize fuel p = runSFM fuel (optimize' p)
