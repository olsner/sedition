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
import SimulateTNFA (testTNFASimulation, testTNFASimulationFind)
import TDFA hiding (initState)

regexFind :: String -> String -> Maybe TagMap
regexFind = runTDFA True . genTDFA . genTNFA . testTagRegex

regexMatch :: String -> String -> Maybe TagMap
regexMatch = runTDFA False . genTDFA . genTNFA . testTagRegex

type RegMap = Map RegId Int

data RunState = RunState {
    sFallback :: Maybe (Int, StateId),
    sPos :: Int,
    sRegs :: RegMap,
    sRetryPos :: Int
  } deriving (Show, Ord, Eq)

initState = RunState { sFallback = Nothing, sPos = 0, sRegs = M.empty, sRetryPos = 0 }

getPos = gets sPos
incPos = modify $ \s@RunState{..} -> s { sPos = succ sPos }
setPos new = modify $ \s@RunState{..} -> s { sPos = new }
getRegs = gets sRegs
modifyRegs f = modify $ \s@RunState{..} -> s { sRegs = f sRegs }
setFallback fs = modify $ \s@RunState{..} -> s { sFallback = Just (sPos, fs) }

type RunTDFA a = State RunState a

runTDFA :: Bool -> TDFA -> String -> Maybe TagMap
runTDFA search tdfa@TDFA{..} xs = evalState (go' tdfaStartState xs) initState
  where
    orig_xs = xs

    go :: StateId -> String -> RunTDFA (Maybe TagMap)
    go s [] = applyFinalState s
    go s (x:xs)
      | Just (s',o) <- next s x = applyRegOps o >> incPos >> maybeSetFallback s' >> go' s' xs
      | otherwise               = applyFallbackState s

    debug = True

    go' s xs = do
      pos <- getPos
      regs <- getRegs
      when debug (trace (unwords ["go", show pos, show xs, show s, show (M.toList regs)]) (return ()))
      go s xs

    retry = do
      pos <- gets (succ . sRetryPos)
      put (initState { sPos = pos, sRetryPos = pos})
      go' tdfaStartState (drop pos orig_xs)

    next :: StateId -> Char -> Maybe (StateId, RegOps)
    next s x = CM.lookup x (M.findWithDefault CM.empty s tdfaTrans)

    maybeSetFallback s | s `M.member` tdfaFinalFunction = trace "setting fallback!" (setFallback s)
                       | otherwise                      = trace ("no fallback for " ++ show s) (return ())

    applyFallbackState s = do
      maybeFallback <- gets sFallback
      case maybeFallback of
        -- found accepting state at EOF
        _ | M.member s tdfaFinalFunction -> outTags s tdfaFinalFunction
        Just (pos, fs) ->
            trace ("fallback at end to " ++ show pos ++ " " ++ show fs) $
                (setPos pos >> outTags fs tdfaFallbackFunction)
        _ | search -> trace "no match, retry" retry
        _ -> trace "no match for character" (return Nothing)

    applyFinalState s = do
      maybeFallback <- gets sFallback
      case maybeFallback of
        _ | M.member s tdfaFinalFunction -> outTags s tdfaFinalFunction
        _ | M.member s tdfaEOL           -> outTags s tdfaEOL
        Just (pos, fs) -> setPos pos >> outTags fs tdfaFallbackFunction
        _ -> trace "non-accepting state at end" (return Nothing)

    -- Takes position to handle fallback to a previous match
    outTags s opfun | ops <- fromJust (M.lookup s opfun) = do
      applyRegOps ops
      pos <- getPos
      gets (Just . fixedTags pos . tagsFromRegs . sRegs)

    tagsFromRegs :: RegMap -> TagMap
    tagsFromRegs rs = M.mapMaybe (\r -> M.lookup r rs) tdfaFinalRegisters

    fixedTags :: Int -> TagMap -> TagMap
    fixedTags = resolveFixedTags tdfaFixedTags

applyRegOps xs = do
  pos <- getPos
  modifyRegs (applyRegOps' xs pos)

applyRegOps' :: RegOps -> Int -> RegMap -> RegMap
applyRegOps' xs pos rs = foldr f rs xs
  where
    f :: RegOp -> RegMap -> RegMap
    f (dst, CopyReg src) rs = M.alter (\_ -> M.lookup src rs) dst rs
    f (dst, SetReg Nil) rs = M.delete dst rs
    f (dst, SetReg Pos) rs = M.insert dst pos rs
