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

-- More passes:
--  branch-to-branch
--  dead pred elimination, as Ifs get removed some predicates become unused too
--    and could be removed
--  line number counting

openEntry :: LabelsPtr [Label] => MaybeC O [Label]
openEntry = NothingC

optimize' :: (CheckpointMonad m, FuelMonad m) => Graph Insn O C -> m (Graph Insn O C)
optimize' program = do
  (program,_,_) <- analyzeAndRewriteFwd constPredPass openEntry program M.empty
  return program

runSFM :: Fuel -> SimpleFuelMonad a -> a
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel m)

optimize fuel p = runSFM fuel (optimize' p)
