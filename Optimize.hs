{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, ScopedTypeVariables, FlexibleContexts #-}

module Optimize (optimize) where

import Compiler.Hoopl as H hiding ((<*>))

import Control.Monad

--import Data.Map (Map)
--import qualified Data.Map as M
--import Debug.Trace

import IR

import ConstPred (constPredPass)
import LivePred (livePredPass)
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
  return program

rep :: Monad m => Int -> (a -> m a) -> (a -> m a)
rep 0 _ = return
rep n f = f >=> rep (n-1) f

optimize' :: (CheckpointMonad m, FuelMonad m) => (Label, Graph Insn C C) -> m (Graph Insn C C)
optimize' (entry, program) = rep 5 (optimizeOnce entry) program

runSFM :: Fuel -> SimpleFuelMonad a -> (a, Fuel)
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel ((,) <$> m <*> fuelRemaining))

optimize fuel p = runSFM fuel (optimize' p)
