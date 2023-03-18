{-# LANGUAGE RecordWildCards #-}

module Regex.SimulateTDFA where

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
import Regex.TaggedRegex
import Regex.TNFA (genTNFA, testTNFA)
import Regex.SimulateTNFA (testTNFASimulation, testTNFASimulationFind)
import Regex.TDFA hiding (initState)

regexFind :: String -> String -> Maybe TagMap
regexFind = runTDFA True . genTDFA . genTNFA . testTagRegex

regexMatch :: String -> String -> Maybe TagMap
regexMatch = runTDFA False . genTDFA . genTNFA . testTagRegex

type RegMap = Map RegId Int

data RunState = RunState {
    sFallback :: Maybe (Int, StateId),
    sPos :: Int,
    sRegs :: RegMap,
    sRetryPos :: Int,
    sRetryString :: String
  } deriving (Show, Ord, Eq)

initState p s = RunState { sFallback = Nothing, sPos = p, sRegs = M.empty, sRetryPos = p, sRetryString = s }

getPos = gets sPos
incPos = modify $ \s@RunState{..} -> s { sPos = succ sPos }
setPos new = modify $ \s@RunState{..} -> s { sPos = new }
getRegs = gets sRegs
modifyRegs f = modify $ \s@RunState{..} -> s { sRegs = f sRegs }
setFallback fs = modify $ \s@RunState{..} ->
    trace ("setting fallback! " ++ show fs ++ " @" ++ show sPos) $
    s { sFallback = Just (sPos, fs) }

type RunTDFA a = State RunState a

runTDFA :: Bool -> TDFA -> String -> Maybe TagMap
runTDFA search tdfa@TDFA{..} xs =
  evalState (go' tdfaStartState xs) (initState 0 xs)
  where
    go :: StateId -> String -> RunTDFA (Maybe TagMap)
    go s [] = applyFinalState True s
    go s (x:xs)
      | Just (s',o) <- next s x = applyRegOps o >> incPos >> maybeSetFallback s' >> go' s' xs
      | otherwise               = trace ("default-transition from " ++ show s) $ applyFinalState False s

    debug = True

    go' s xs = do
      pos <- getPos
      regs <- getRegs
      when debug (trace (unwords ["go", show pos, show xs, show s, show (M.toList regs)]) (return ()))
      go s xs

    retry = do
      pos <- gets sRetryPos
      str <- gets sRetryString
      if null str
        then return Nothing
        else do
          put (initState (succ pos) (tail str))
          go' tdfaStartState (tail str)

    next :: StateId -> Char -> Maybe (StateId, RegOps)
    next s x = CM.lookup x (M.findWithDefault CM.empty s tdfaTrans)

    -- This also means "last accepting state", not just fallback. E.g. if there
    -- are no clobbered registers then the fallback function is the same as the
    -- final function and there are no backup regops.
    maybeSetFallback s | s `M.member` tdfaFinalFunction = setFallback s
                       | otherwise                      = trace ("no fallback for " ++ show s) (return ())

    applyFinalState eol s = do
      maybeFallback <- gets sFallback
      pos <- getPos
      case maybeFallback of
        _ | M.member s tdfaFinalFunction -> trace ("at final state " ++ show s ++ ", pos=" ++ show pos) outTags s tdfaFinalFunction
        _ | eol && M.member s tdfaEOL    -> trace "at EOL-only final state" outTags s tdfaEOL
        Just (pos, fs) -> trace ("falling back to " ++ show fs ++ " @" ++ show pos) (setPos pos) >> outTags fs (tdfaFallbackFunction `M.union` tdfaFinalFunction)
        _ | search -> trace "no match, retry" retry
        _ | eol -> trace "non-accepting state at end" (return Nothing)
        _ -> trace "non-accepting state in middle" (return Nothing)

    -- Takes position to handle fallback to a previous match
    outTags s opfun | Just ops <- M.lookup s opfun = do
      applyRegOps ops
      pos <- getPos
      gets (Just . fixedTags pos . tagsFromRegs . sRegs)
                    | otherwise = error ("Missing final function for " ++ show s)

    tagsFromRegs :: RegMap -> TagMap
    tagsFromRegs rs = M.map (\r -> M.findWithDefault (-1) r rs) tdfaFinalRegisters

    fixedTags :: Int -> TagMap -> TagMap
    fixedTags = resolveFixedTags tdfaFixedTags

applyRegOps xs = do
  pos <- getPos
  modifyRegs (applyRegOps' xs pos)

applyRegOps' :: RegOps -> Int -> RegMap -> RegMap
applyRegOps' xs pos rs = foldl (flip tf) rs xs
  where
    tf :: RegOp -> RegMap -> RegMap
    tf (dst, val) rs = trace (show dst ++ " <- " ++ show val ++ " == " ++ show (M.lookup dst (f (dst,val) rs))) $ f (dst,val) rs
    f :: RegOp -> RegMap -> RegMap
    f (dst, CopyReg src) rs = M.alter (\_ -> M.lookup src rs) dst rs
    f (dst, SetReg Nil) rs = M.delete dst rs
    f (dst, SetReg Pos) rs = M.insert dst pos rs
