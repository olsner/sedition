{-# LANGUAGE RecordWildCards #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"

module TDFA2C where

import Control.Monad.Trans.State.Strict

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import Regex (Regex)
import qualified Regex

import TaggedRegex
import TNFA
import SimulateTNFA

tdfa2c :: Regex -> String
tdfa2c = show . genTNFA . fixTags . tagRegex

type RegId = Int
data RegVal = Nil | Pos deriving (Show, Ord, Eq)
data RegOp
  = SetReg RegId RegVal -- ^ Set register to nil or current position
  | CopyReg RegId RegId -- ^ CopyReg i j => i <- j
  | CopyAppend RegId [RegVal] -- ^ i <- j <> h
  deriving (Show, Ord, Eq)

type RegOps = [RegOp]

data TDFA = TDFA {
    tdfaStartState :: StateId,
    tdfaFinalStates :: Set StateId,
    tdfaFinalRegisters :: Map TagId RegId,
    tdfaFinalFunction :: Map StateId RegOps
    -- Transition table?
  }
  deriving (Show, Ord, Eq)

type GenTDFA a = State Int a


