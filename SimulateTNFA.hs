{-# LANGUAGE RecordWildCards #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Simulate TNFA matching on strings.

module SimulateTNFA where

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

testTNFASimulation :: String -> String -> Maybe TagMap
testTNFASimulation = tnfaSimulation . genTNFA . testTagRegex

type ConfigMap = Map StateId TagMap

tnfaSimulation :: TNFA -> String -> Maybe TagMap
tnfaSimulation tnfa as =     initSimulation tnfa (M.singleton (tnfaStartState tnfa) M.empty) as

finalSimulatedState :: TNFA -> Int -> ConfigMap -> Maybe TagMap
finalSimulatedState TNFA{..} k c = go (M.toList c)
  where
    go [] = Nothing
    go ((q, m):xs)
      | q == tnfaFinalState = Just (resolveFixedTags tnfaTagMap k m)
      | otherwise = go xs

initSimulation :: TNFA -> ConfigMap -> String -> Maybe TagMap
initSimulation tnfa c xs = trace simTrace $ simulation tnfa c' 0 xs
  where c' = epsilonClosure tnfa c 0 (null xs)
        simTrace = "Init: " ++ show c ++ " -> " ++ show c'

simulation :: TNFA -> ConfigMap -> Int -> String -> Maybe TagMap
simulation tnfa c k [] =
    trace simTrace $ finalSimulatedState tnfa k c'
  where c' = epsilonClosure tnfa c k True
        simTrace = "Ending at " ++ show k ++ ": " ++ show c ++ " -> " ++ show c'
simulation tnfa c k (x:xs) | M.null c'' = trace "Out of states: No match" $ Nothing
                           | otherwise  = trace simTrace $ simulation tnfa c'' (k + 1) xs
  where c' = epsilonClosure tnfa c k False
        c'' = stepOnSymbol tnfa c' x
        simTrace = "Continuing at " ++ show k ++ " (" ++ show x ++ "): " ++ show c ++ " -> " ++ show c' ++ " -> " ++ show c''

matchTerm :: TNFATrans -> Char -> Bool
matchTerm Any _ = True
matchTerm (Eps _ _) _ = False
matchTerm (Symbol x) y = x == y
matchTerm (CClass xs) y = y `elem` xs
matchTerm (CNotClass xs) y = not (y `elem` xs)
matchTerm BOL _ = False
matchTerm EOL _ = False

symbolTrans :: TNFATrans -> Bool
symbolTrans (Eps _ _) = False
symbolTrans BOL = False
symbolTrans EOL = False
symbolTrans _ = True

stepOnSymbol :: TNFA -> ConfigMap -> Char -> ConfigMap
stepOnSymbol tnfa c x = M.fromList c'
  where c' = [(p, m) | (s,m) <- M.toList c, (q,a,p) <- tnfaTrans tnfa,
                       s == q, matchTerm a x]

epsilonClosure :: TNFA -> ConfigMap -> Int -> Bool -> ConfigMap
epsilonClosure tnfa c k eol = M.fromList $ go (M.toList c) M.empty
  where
    bol = k == 0
    fin = tnfaFinalState tnfa
    ts = tnfaTrans tnfa
    go :: [(StateId, TagMap)] -> ConfigMap -> [(StateId, TagMap)]
    go [] c' = possibleStates c'
    go ((q,m):xs) c' = go (ys ++ xs) c''
      where
        c'' = M.insert q m c'
        ts = tnfaTrans tnfa
        tagops = sort [(prio,t,p) | (s,Eps prio t,p) <- ts, s == q]
        ys = [ (p,m') | (_,t,p) <- tagops,
                        not (M.member p c''),
                        let m' = updateTag t m ] ++
             [ (p,m) | p <- anchors, not (M.member p c'') ]
        updateTag (Tag t) m = M.insert t k m
        updateTag (UnTag t) m = M.delete t m
        updateTag NoTag m = m
        anchors = [p | eol, (s,EOL,p) <- ts, s == q] ++
                  [p | bol, (s,BOL,p) <- ts, s == q]
    possibleStates c' = [y | y@(q,_) <- M.toList c', q == fin || possibleState q]
    possibleState q = or [symbolTrans t | (s,t,_) <- ts, s == q]

