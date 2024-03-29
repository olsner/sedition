{-# LANGUAGE FlexibleContexts, RecordWildCards #-}

module Regex.OptimizeIR (optimize) where

import Compiler.Hoopl as H hiding ((<*>))

import Debug.Trace

import Regex.IR

import Regex.Optimize.IdenticalBlocks (mergeIdenticalBlocks)
import Regex.Optimize.LiveRegister (liveRegisterPass)
import Regex.Optimize.LiveSaveCursor (liveSaveCursorPass)
import Regex.Optimize.LiveSetFallback (liveSetFallbackPass)
import Regex.Optimize.PossibleFallback (possibleFallbackPass)
import Regex.Optimize.RedundantBranches (redundantBranchesPass)
import Regex.Optimize.RedundantCheckBounds (redundantCheckBoundsPass)
import Regex.Optimize.RedundantRestoreCursor (redundantRestoreCursorPass)
import Regex.Optimize.SameResult (sameResultPass)

--debugBwd = debugBwdJoins trace (const True)
--debugBwd = debugBwdTransfers trace showInsn (\n f -> True)
--debugBwd = id

doTrace = False

traceFuel :: FuelMonad m => Int -> m ()
traceFuel oldFuel = do
  fuel <- fuelRemaining
  traceM (show (oldFuel - fuel) ++ " fuel consumed, " ++ show fuel ++ " remaining")

tracePass name pass | doTrace = do
  oldFuel <- fuelRemaining
  (program,_,_) <- trace ("Optimizing program: " ++ show name ++ "...") pass
  traceFuel oldFuel
  traceM (show (setSize (labelsDefined program)) ++ " labels defined, " ++
          show (setSize (labelsUsed program)) ++ " labels used")
  traceM (show (length (show program)))
  return program
                    | otherwise = do
  (program,_,_) <- pass
  return program

optimizeOnce :: (CheckpointMonad m, FuelMonad m) => Label -> Graph Insn C C -> m (Label, Graph Insn C C)
optimizeOnce entry program = do
  (entry,program) <- return (mergeIdenticalBlocks entry program)
  let entries = JustC [entry]
  program <- tracePass "redundantBranches" $
    analyzeAndRewriteBwd redundantBranchesPass entries program mapEmpty
  program <- tracePass "liveSetFallback" $
    analyzeAndRewriteBwd liveSetFallbackPass entries program mapEmpty
  program <- tracePass "redundantRestoreCursor" $
    analyzeAndRewriteFwd redundantRestoreCursorPass entries program mapEmpty
  program <- tracePass "liveSaveCursor" $
    analyzeAndRewriteBwd liveSaveCursorPass entries program mapEmpty
  program <- tracePass "possibleFallback" $
    analyzeAndRewriteFwd possibleFallbackPass entries program mapEmpty
  program <- tracePass "liveRegister" $
    analyzeAndRewriteBwd liveRegisterPass entries program mapEmpty
  program <- tracePass "redundantCheckBounds" $
    analyzeAndRewriteFwd redundantCheckBoundsPass entries program mapEmpty
  program <- tracePass "sameResult" $
    analyzeAndRewriteBwd sameResultPass entries program mapEmpty
  return (entry, program)

optToFix f entry original = do
  oldFuel <- fuelRemaining
  -- If we've already ran out of fuel, the optimizations will run but do
  -- nothing, which we'll consider a fixpoint since oldFuel == newFuel == 0.
  (entry, optimized) <- f entry original
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
-- * beginning-of-line checks
--   - unknown on entry (since we may have entered through next_match)
--   - false after reaching a Next
-- * labels with equivalent blocks? (backwards)
-- * duplicate basic blocks to expose unnecessary bounds checks
--   e.g. checkbounds -> L1: some code -> checkbounds, where L1 is used
--   elsewhere (so that it might have different incoming bounds, preventing
--   the normal bounds-check optimization)
--   but only do this if the checkbounds overlap?
--   and maybe do some thinking on a higher level to avoid emitting IR that
--   has code like this?
