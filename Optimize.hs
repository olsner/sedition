{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, ScopedTypeVariables, FlexibleContexts #-}

module Optimize (optimize) where

import Compiler.Hoopl as H hiding ((<*>))

import Control.Monad

--import Data.Map (Map)
import qualified Data.Map as M
--import Debug.Trace

import IR

import ConstPred (constPredPass)
import LivePred (livePredPass)
import RedundantBranches (redundantBranchesPass)

--debugBwd = debugBwdJoins trace (const True)
--debugBwd = debugBwdTransfers trace showInsn (\n f -> True)

stripUnused :: Graph Insn e x -> Graph Insn e x
stripUnused g = deleteLabels g (labelsDefined g `setDifference` labelsUsed g)

deleteLabels :: Graph Insn e x -> LabelSet -> Graph Insn e x
deleteLabels g ls = case g of
    GNil -> g
    GUnit {} -> g
    GMany e body f -> GMany e body' f
      where
        body' = mapDeleteList (setElems ls) body

-- Since redundantBranches may produce more opportunities for const predicates
-- (and vice versa), run this at least twice. (Could run to fixpoint instead?)
optimizeOnce :: (CheckpointMonad m, FuelMonad m) => Graph Insn O C -> m (Graph Insn O C)
optimizeOnce program = do
  (program,_,_) <- analyzeAndRewriteFwdOx constPredPass program M.empty
  (program,_,_) <- analyzeAndRewriteBwdOx redundantBranchesPass program mapEmpty
  --(program,_,_) <- analyzeAndRewriteBwdOx livePredPass program mapEmpty
  return (stripUnused program)

rep :: Monad m => Int -> (a -> m a) -> (a -> m a)
rep 0 _ = return
rep n f = f >=> rep (n-1) f

optimize' :: (CheckpointMonad m, FuelMonad m) => Graph Insn O C -> m (Graph Insn O C)
optimize' = rep 5 optimizeOnce

runSFM :: Fuel -> SimpleFuelMonad a -> (a, Fuel)
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel ((,) <$> m <*> fuelRemaining))

optimize fuel p = runSFM fuel (optimize' p)
