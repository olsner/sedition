{-# LANGUAGE RecordWildCards #-}

module SimulateTDFA where

import Control.Monad.Trans.State.Strict
import Control.Monad

-- import Data.ByteString.Char8 (ByteString)
-- import qualified Data.ByteString.Char8 as C
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import qualified CharMap as CM
import CharMap (CharMap)
import TaggedRegex
import TNFA (genTNFA, testTNFA)
import SimulateTNFA (testTNFASimulation, tnfaSimulation)
import TDFA

regexFind :: String -> String -> Maybe TagMap
regexFind = runTDFA . genTDFA . genTNFA . testTagRegexFind

regexMatch :: String -> String -> Maybe TagMap
regexMatch = runTDFA . genTDFA . genTNFA . testTagRegex

{-data TDFA = TDFA {
    tdfaStartState :: StateId,
    tdfaFinalStates :: Set StateId,
    tdfaFinalRegisters :: Map TagId RegId,
    tdfaFinalFunction :: Map StateId RegOps,
    tdfaTrans :: Map StateId [TDFATrans],
    tdfaFixedTags :: FixedTagMap,
    tdfaTagRegMap :: Map StateId (Map TNFA.StateId (Map TagId RegId)),
    tdfaStateMap :: Map StateId (Set TNFA.StateId)
  }
  deriving (Show, Ord, Eq)
-}

type RegMap = Map RegId Int

runTDFA :: TDFA -> String -> Maybe TagMap
runTDFA tdfa@TDFA{..} = go' tdfaStartState M.empty 0
  where
    go :: StateId -> RegMap -> Int -> String -> Maybe TagMap
    go s regs pos [] = applyFinalState s regs pos
    go s regs pos (x:xs)
      | Just (s',o) <- next s x = go' s' (applyRegOps' o regs pos) (pos + 1) xs
      | otherwise               = Nothing

    debug = True

    go' s regs pos xs
        | debug     = trace (unwords ["go", show pos, show xs, show s, show (M.toList regs)]) (go s regs pos xs)
        | otherwise = go s regs pos xs

    next :: StateId -> Char -> Maybe (StateId, RegOps)
    next s x = CM.lookup x (M.findWithDefault CM.empty s tdfaTrans)

    applyFinalState s regs pos
      | S.member s tdfaFinalStates = Just (fixedTags pos $ tagsFromRegs regs')
      | otherwise                  = trace "non-accepting state at end" Nothing
      where
        regs' = applyRegOps' (M.findWithDefault [] s tdfaFinalFunction) regs pos

    tagsFromRegs :: RegMap -> TagMap
    tagsFromRegs rs = M.mapMaybe (\r -> M.lookup r rs) tdfaFinalRegisters

    fixedTags :: Int -> TagMap -> TagMap
    fixedTags = resolveFixedTags tdfaFixedTags

    applyRegOps' xs rs pos | False = trace (unwords ["applyRegOps{", show xs, show rs, show pos, "}"]) $ applyRegOps xs rs pos
                           | otherwise = applyRegOps xs rs pos

    applyRegOps :: RegOps -> RegMap -> Int -> RegMap
    applyRegOps xs rs pos = foldr f rs xs
      where
        f :: RegOp -> RegMap -> RegMap
        f (dst, CopyReg src) rs = M.alter (\_ -> M.lookup src rs) dst rs
        f (dst, SetReg Nil) rs = M.delete dst rs
        f (dst, SetReg Pos) rs = M.insert dst pos rs
