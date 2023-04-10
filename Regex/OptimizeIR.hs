{-# LANGUAGE FlexibleContexts, RecordWildCards #-}

module Regex.OptimizeIR (optimize) where

import Compiler.Hoopl as H hiding ((<*>))

import Debug.Trace

import Regex.IR

import Regex.Optimize.RedundantBranches (redundantBranchesPass)
import Regex.Optimize.PossibleFallback (possibleFallbackPass)
import Regex.Optimize.LiveSetFallback (liveSetFallbackPass)
import Regex.Optimize.LiveSaveCursor (liveSaveCursorPass)

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
  trace (show program) $ return ()
  return program
                    | otherwise = do
  (program,_,_) <- pass
  return program

optimizeOnce :: (CheckpointMonad m, FuelMonad m) => Label -> Graph Insn C C -> m (Graph Insn C C)
optimizeOnce entry program = do
  let entries = JustC [entry]
  program <- tracePass "redundantBranches" $
    analyzeAndRewriteBwd redundantBranchesPass entries program mapEmpty
  program <- tracePass "liveSetFallback" $
    analyzeAndRewriteBwd liveSetFallbackPass entries program mapEmpty
  program <- tracePass "liveSaveCursor" $
    analyzeAndRewriteBwd liveSaveCursorPass entries program mapEmpty
  program <- tracePass "possibleFallback" $
    analyzeAndRewriteFwd possibleFallbackPass entries program mapEmpty
  return program

optToFix f entry original = do
  oldFuel <- fuelRemaining
  -- If we've already ran out of fuel, the optimizations will run but do
  -- nothing, which we'll consider a fixpoint since oldFuel == newFuel == 0.
  optimized <- f entry original
  newFuel <- fuelRemaining
  -- Ugly workaround, but compare the optimized text program to see if
  -- optimization changed something.
  -- Hoopl passes may consume fuel on speculative rewrites that won't stick
  -- around in the final output.
  if oldFuel == newFuel || newFuel == 0 || show original == show optimized
    then return (finishProgram entry optimized)
    else optToFix f entry (updateFallbackLabels optimized)

optimize' :: (CheckpointMonad m, FuelMonad m) => Program -> m Program
optimize' Program{..} = optToFix optimizeOnce entryPoint programGraph

runSFM :: Fuel -> SimpleFuelMonad a -> (a, Fuel)
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel ((,) <$> m <*> fuelRemaining))

optimize :: Fuel -> Program -> (Program, Fuel)
optimize fuel p = runSFM fuel (optimize' p)

-- TODO, optimizations:
-- * Dead register (backwards)
--
-- * switch with everything to the same target
-- * labels with equivalent blocks? (backwards)
-- * redundant bounds checks
--   forwards:
--   - record largest previously checked bound
--   - reduce by one after YYNEXT
--   - remove any lower or equal bound checks
--   backwards too? It's useless to check bounds for 2 if all successors check
--   for 3 or more. OTOH, the failure path matters so this should track the
--   failure label and only optimize out if we go to the same place.
