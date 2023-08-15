{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

-- Minimize a completed TDFA

module Regex.Minimize where

import Control.Monad.Trans.State.Strict hiding (mapState)
import Control.Monad

-- import Data.ByteString.Char8 (ByteString)
-- import qualified Data.ByteString.Char8 as C
import Data.List (elemIndex, find, intercalate, sort, sortOn)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Either (partitionEithers)

--import Debug.Trace

import qualified CharMap as CM
import CharMap (CharMap)
import Regex.TDFA

data StateKey = StateKey {
  stateEOLRegOps :: Maybe RegOps,
  stateFinalRegOps :: Maybe RegOps,
  stateTrans :: TDFATransTable } deriving (Show,Eq,Ord)

type StateMap = Map StateId StateId
type TransMap = Map StateKey StateId

stateKey TDFA{..} s = StateKey {
  stateEOLRegOps = M.lookup s tdfaEOL,
  stateFinalRegOps = M.lookup s tdfaFinalFunction,
  stateTrans = M.findWithDefault CM.empty s tdfaTrans }

translateStateKey :: StateMap -> StateKey -> StateKey
translateStateKey m k@StateKey{..} = k { stateTrans = tTable m stateTrans }

tTable :: StateMap -> TDFATransTable -> TDFATransTable
tTable m | M.null m  = id
         | otherwise = CM.map (\(s,o) -> (tState m s, o))

mergeStates :: TDFA -> Set StateId -> StateMap -> (Bool, StateMap)
mergeStates tdfa ss sm = go False M.empty sm (S.toList ss)
  where
    go new tm sm []     = (new, sm)
    go new tm sm (s:ss) = case M.lookup k tm of
        Just s' -> go True tm (M.insert s s' sm) ss
        Nothing -> go new (M.insert k s tm) sm ss
      where k = translateStateKey sm (stateKey tdfa s)

tState m s = M.findWithDefault s s m
tStateSet m = S.map (tState m)
tStateMap m = M.mapKeys (tState m)

translateTDFA tdfa@TDFA{..} m = tdfa {
    tdfaStartState = tState m tdfaStartState
  , tdfaStartStateNotBOL = tState m tdfaStartStateNotBOL
  , tdfaFinalFunction = tStateMap m tdfaFinalFunction
  , tdfaFallbackFunction = tStateMap m tdfaFallbackFunction
  , tdfaTrans = M.map (tTable m) (tStateMap m tdfaTrans)
  , tdfaEOL = tStateMap m tdfaEOL
  , tdfaMinLengths = tStateMap m tdfaMinLengths
  -- Debugging/printout related data, not used for execution
  , tdfaTagRegMap = tStateMap m tdfaTagRegMap
  , tdfaStateMap = tStateMap m tdfaStateMap
  }

minimize :: TDFA -> TDFA
minimize tdfa = go (S.fromList (tdfaStates tdfa)) M.empty
  where
    go ss m | new       = go (tStateSet m ss) m'
            | M.null m' = tdfa
            | otherwise = translateTDFA tdfa m'
      where (new, m') = mergeStates tdfa ss m
