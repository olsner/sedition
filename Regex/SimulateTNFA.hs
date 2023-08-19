{-# LANGUAGE RecordWildCards,TupleSections, BangPatterns #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Simulate TNFA matching on strings.

module Regex.SimulateTNFA where

import Control.Applicative

import Data.List (find, intercalate, sort)
-- import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import Regex.TaggedRegex hiding (Term(..))
import Regex.TNFA

testTNFASimulation :: String -> String -> Maybe TagMap
testTNFASimulation = tnfaMatch . genTNFA . testTagRegex
testTNFASimulationFind = testTNFASimulation

data Config = Config {
  configState :: StateId,
  configGeneration :: Int,
  configTagMap :: TagMap } deriving (Show, Ord, Eq)

data ConfigMap = ConfigMap [Config]
data FinalState = NoMatch | Match Int Config deriving (Show, Ord, Eq)

instance Semigroup FinalState where
  NoMatch <> x = x
  x <> NoMatch = x
  m1@(Match _ c1) <> m2@(Match _ c2)
    | configGeneration c1 <= configGeneration c2 = m1
    | otherwise = m2

emptyCM = ConfigMap []
nullCM (ConfigMap xs) = null xs
uncons (ConfigMap []) = Nothing
uncons (ConfigMap (x:xs)) = Just (x, ConfigMap xs)
singleton x = ConfigMap [x]
filterCM f (ConfigMap xs) = ConfigMap (filter f xs)
elemCM s (ConfigMap xs) = s `elem` map configState xs
maxGeneration (ConfigMap []) = -1
maxGeneration (ConfigMap xs) = maximum (map configGeneration xs)

instance Semigroup ConfigMap where
  ConfigMap xs <> ConfigMap ys = ConfigMap (xs <> ys)

showC :: ConfigMap -> String
showC (ConfigMap cs) = intercalate "; " (map showConfig cs)

showConfig Config{..}
  | M.null configTagMap = prefix
  | otherwise = prefix ++ ": " ++ showTags configTagMap
  where prefix = show configState ++ "_" ++ show configGeneration

showTag (t, val) = show t ++ "=" ++ show val
showTags = intercalate "," . map showTag . M.toList

showF :: FinalState -> String
showF NoMatch = "@@"
showF (Match x c) = "@" ++ show x ++ ";" ++ showConfig c

tnfaMatch tnfa = initSimulation tnfa (initState tnfa 0) NoMatch 0

initState TNFA{..} start = singleton (Config tnfaStartState start M.empty)

-- Unless we've found some final state, re-add the initial state at each
-- iteration. This corresponds to restarting the search at the next starting
-- position (but only if there will be no match at the current position).
-- Note that the conditional addition is unnecessary if we also have the
-- correct stopping condition below to avoid scanning past the first match.
reinit :: TNFA -> FinalState -> ConfigMap -> ConfigMap
reinit tnfa NoMatch c | not (tnfaFinalState tnfa `elemCM` c) =
  addStates c (initState tnfa (maxGeneration c + 1))
reinit _ _ c = c

-- TODO When adding a Set of states, make this part of <>
addStates (ConfigMap cs) (ConfigMap xs) = ConfigMap (go cs xs)
  where
    go cs [] = cs
    go cs (x:xs) | configState x `elem` map configState cs = go cs xs
                 | otherwise   = go (cs ++ [x]) xs

finalSimulatedState :: TNFA -> FinalState -> Maybe TagMap
finalSimulatedState TNFA{..} f = case f of
  NoMatch            -> Nothing
  Match x Config{..} -> Just (resolveFixedTags tnfaTagMap x configTagMap)

initSimulation :: TNFA -> ConfigMap -> FinalState -> Int -> String -> Maybe TagMap
initSimulation tnfa c f k xs = trace simTrace $ simulation tnfa c' f' k xs
  where c' = epsilonClosure tnfa c k (null xs)
        f' = finalState tnfa k c' <> f
        simTrace = "Init: " ++ showC c ++ " -> " ++ showC c' ++ " | " ++ showF f'

simulation :: TNFA -> ConfigMap -> FinalState -> Int -> String -> Maybe TagMap
simulation tnfa c f k [] = trace simTrace $ finalSimulatedState tnfa f'
  where -- TODO Should we really be doing "epsilon closure" here? May be doing
        -- something around matching EOL since that isn't a "symbol" though.
        cI = reinit tnfa f c
        c' = epsilonClosure tnfa cI k True
        f' = finalState tnfa k c' <> f
        simTrace = "Ending at " ++ show k ++ ": " ++ showF f ++ " | " ++ showC cI ++ " -> " ++ showC c' ++ " | " ++ showF f'
simulation tnfa c f k (x:xs)
  | nullCM c = trace simTrace $ finalSimulatedState tnfa f
  | otherwise = trace simTrace $ simulation tnfa c3 f3 (k + 1) xs
  where
    c1 = stepOnSymbol tnfa c x
    f1 = finalState tnfa (k + 1) c1 <> f

    c2 = reinit tnfa f c1
    f2 = finalState tnfa (k + 1) c2 <> f1

    c3 = epsilonClosure tnfa c2 (k + 1) False
    f3 = finalState tnfa (k + 1) c3 <> f2

    simTrace = "Continuing at " ++ show k ++ " (" ++ show x ++ "): " ++ showF f ++ " | " ++ showC c1 ++ " -> " ++ showC c2 ++ " -> " ++ showC c3 ++ " | " ++ showF f3

matchTerm :: TNFATrans -> Char -> Bool
matchTerm Any _ = True
matchTerm (Eps _ _) _ = False
matchTerm (Symbol x) y = x == y
matchTerm (CClass xs) y = y `elem` xs
matchTerm (CNotClass xs) y = not (y `elem` xs)
matchTerm BOL _ = False
matchTerm EOL _ = False

stepOnSymbol :: TNFA -> ConfigMap -> Char -> ConfigMap
stepOnSymbol TNFA{..} (ConfigMap cs) x = ConfigMap $
  [c { configState = p } | c@Config{..} <- cs,
                          (a,p) <- M.findWithDefault [] configState tnfaTrans,
                          matchTerm a x]

-- Depth-first search of the epsilon closure(s) of incoming states. Intuitively
-- this is because of priority - we visit the highest-priority states first and
-- keep the first reached copy of each NFA state.
epsilonClosure :: TNFA -> ConfigMap -> Int -> Bool -> ConfigMap
epsilonClosure TNFA{..} (ConfigMap cs) k eol = go cs S.empty emptyCM
  where
    bol = k == 0
    go :: [Config] -> Set StateId -> ConfigMap -> ConfigMap
    go [] _ c = finalGeneration (possibleStates c)
    go (x@(Config q _ m):xs) added c =
      go (ys ++ xs) (S.insert q added) (c <> singleton x)
      where
        epsts = sort [(prio,t,p) | (Eps prio t,p) <- transFrom q]
        ys = [ x { configState = p, configTagMap = m' }
               | (_,t,p) <- epsts,
                 not (S.member p added),
                 let m' = updateTag t m ] ++
             [ x { configState = p } | p <- anchors, not (S.member p added) ]
        updateTag (Tag t) m = M.insert t k m
        updateTag (UnTag t) m = M.delete t m
        updateTag NoTag m = m
        anchors = [p | eol, (EOL,p) <- transFrom q] ++
                  [p | bol, (BOL,p) <- transFrom q]
    possibleStates = filterCM ((`S.member` tnfaClosedStates) . configState)
    transFrom s = M.findWithDefault [] s tnfaTrans
    -- If we reach a final state, remove all states with a higher generation
    -- from the closure. We keep lower generation states for potential longer
    -- matches starting earlier, and same generation states for finding a
    -- potential longer match starting at the same place.
    finalGeneration c | Just g <- minFinalGeneration c = filterCM ((<= g) . configGeneration) c
                      | otherwise = c
    minFinalGeneration (ConfigMap xs) =
      maybeMinimum . map configGeneration . filter ((== tnfaFinalState) . configState) $ xs

maybeMinimum [] = Nothing
maybeMinimum xs = Just (minimum xs)

finalState :: TNFA -> Int -> ConfigMap -> FinalState
finalState TNFA{..} k (ConfigMap xs) =
  case find (\c -> configState c == tnfaFinalState) xs of
    Nothing -> NoMatch
    Just c  -> Match k c
