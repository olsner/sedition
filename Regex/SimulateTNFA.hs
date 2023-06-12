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
testTNFASimulationFind = tnfaSearch 0 . genTNFA . testTagRegex

type ConfigMap = [(StateId, TagMap)]
type FinalState = Maybe (Int, TagMap)

showC :: ConfigMap -> String
showC = intercalate "; " . map showState
  where
    showState (s, ts) = show s ++ ": " ++ intercalate "," (map showTag (M.toList ts))
    showTag (t, val) = show t ++ "=" ++ show val

tnfaSearch :: Int -> TNFA -> String -> Maybe TagMap
tnfaSearch k tnfa as
  | match@(Just _) <- initSimulation tnfa (initState tnfa) Nothing k as = match
  | null as   = Nothing
  | otherwise = tnfaSearch (k + 1) tnfa (tail as)

tnfaMatch tnfa = initSimulation tnfa (initState tnfa) Nothing 0

initState TNFA{..} = [(tnfaStartState, M.empty)]

finalSimulatedState :: TNFA -> FinalState -> Maybe TagMap
finalSimulatedState TNFA{..} f = uncurry (resolveFixedTags tnfaTagMap) <$> f

initSimulation :: TNFA -> ConfigMap -> FinalState -> Int -> String -> Maybe TagMap
initSimulation tnfa c f k xs = trace simTrace $ simulation tnfa c' f' k xs
  where c' = epsilonClosure tnfa c k (null xs)
        f' = finalState tnfa k c' <|> f
        simTrace = "Init: " ++ showC c ++ " -> " ++ showC c'

simulation :: TNFA -> ConfigMap -> FinalState -> Int -> String -> Maybe TagMap
simulation tnfa c f k [] = trace simTrace $ finalSimulatedState tnfa f'
  where c' = epsilonClosure tnfa c k True
        f' = finalState tnfa k c' <|> f
        simTrace = "Ending at " ++ show k ++ ": " ++ showC c ++ " -> " ++ showC c'
simulation tnfa c f k (x:xs) | null c''  = trace simTrace $ finalSimulatedState tnfa f''
                             | otherwise = trace simTrace $ simulation tnfa c'' f'' (k + 1) xs
  where c' = epsilonClosure tnfa c k False
        f' = finalState tnfa k c' <|> f
        c'' = stepOnSymbol tnfa c' x
        f'' = finalState tnfa (k + 1) c'' <|> f'
        simTrace = "Continuing at " ++ show k ++ " (" ++ show x ++ "): " ++ show f ++ " " ++ showC c ++ " -> " ++ showC c' ++ " -> " ++ showC c'' ++ " " ++ show f''

matchTerm :: TNFATrans -> Char -> Bool
matchTerm Any _ = True
matchTerm (Eps _ _) _ = False
matchTerm (Symbol x) y = x == y
matchTerm (CClass xs) y = y `elem` xs
matchTerm (CNotClass xs) y = not (y `elem` xs)
matchTerm BOL _ = False
matchTerm EOL _ = False

stepOnSymbol :: TNFA -> ConfigMap -> Char -> ConfigMap
stepOnSymbol tnfa c x = [(p, m) | (s,m) <- c,
                                  (q,a,p) <- tnfaTrans tnfa,
                                  s == q, matchTerm a x]

-- Depth-first search of the epsilon closure(s) of incoming states. Intuitively
-- this is because of priority - we visit the highest-priority states first and
-- keep the first reached copy of each NFA state.
epsilonClosure :: TNFA -> ConfigMap -> Int -> Bool -> ConfigMap
epsilonClosure TNFA{..} c k eol = go c S.empty []
  where
    bol = k == 0
    go :: ConfigMap -> Set StateId -> ConfigMap -> ConfigMap
    go [] _ c = possibleStates c
    go ((q,m):xs) added c = go (ys ++ xs) (S.insert q added) (c ++ [(q,m)])
      where
        epsts = sort [(prio,t,p) | (s,Eps prio t,p) <- tnfaTrans, s == q]
        ys = [ (p,m') | (_,t,p) <- epsts,
                        not (S.member p added),
                        let !m' = updateTag t m ] ++
             [ (p,m) | p <- anchors, not (S.member p added) ]
        updateTag (Tag t) m = M.insert t k m
        updateTag (UnTag t) m = M.delete t m
        updateTag NoTag m = m
        anchors = [p | eol, (s,EOL,p) <- tnfaTrans, s == q] ++
                  [p | bol, (s,BOL,p) <- tnfaTrans, s == q]
    possibleStates = filter ((`S.member` tnfaClosedStates) . fst)

finalState :: TNFA -> Int -> ConfigMap -> FinalState
finalState TNFA{..} k = ((k,) <$> snd <$>) . find (\(q,_) -> q == tnfaFinalState)
