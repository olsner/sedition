{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances #-}

-- Type for NFA automaton without tags, e.g. generated with Glushkov's
-- construction. Can also be converted to bitwise NFA.

module Regex.NFA.Type where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import Regex.TNFA (StateId(..))

-- TODO Change data type
-- Term or something?
data NFATrans
  = C Char
  | CS (Set Char)
  | Any
  deriving (Show, Ord, Eq)

type TransMap k = Map StateId (Map k (Set StateId))
-- tmUnion :: Ord k => TransMap k -> TransMap k -> TransMap k
-- tmUnion = M.unionWith (M.unionWith S.union)
tmFromList :: Ord k => [(StateId, k, StateId)] -> TransMap k
tmFromList [] = M.empty
tmFromList ((k1,k2,v):xs) = tmInsert1 k1 k2 v (tmFromList xs)
tmToList :: Ord k => TransMap k -> [(StateId, k, StateId)]
tmToList m = [(k1,k2,v) | (k1,m2) <- M.toList m
                        , (k2,s) <- M.toList m2
                        , v <- S.toList s ]

tmInsert1 k1 k2 v = tmInsert k1 (M.singleton k2 (S.singleton v))
tmInsert k v = M.insertWith (M.unionWith S.union) k v
tmLookup k1 k2 m = M.findWithDefault S.empty k2 (M.findWithDefault M.empty k1 m)
tmReach :: TransMap k -> Map StateId (Set StateId)
tmReach = M.map (S.unions . M.elems)

data NFA = NFA
  { nfaFinalStates :: Set StateId
  , nfaTrans :: TransMap NFATrans
  , nfaNumStates :: Int
  } deriving (Show, Ord, Eq)
nfaStartState = S 0

-- API?
-- TODO Move optimization functions out of this module

mapKeysMaybe :: (Ord k, Ord l) => (k -> Maybe l) -> Map k a -> Map l a
mapKeysMaybe f = M.fromList . mapMaybe g . M.toList
  where g (k,v) = case f k of Just k' -> Just (k', v)
                              Nothing -> Nothing

invertMap :: (Ord k, Ord v) => Map k (Set v) -> Map v (Set k)
invertMap m = M.unionsWith S.union [M.fromSet (const (S.singleton k)) vs | (k,vs) <- M.toList m]

compact nfa@NFA{..} = NFA {
    nfaFinalStates = mapStateSet nfaFinalStates,
    nfaTrans = mapStateTM nfaTrans,
    nfaNumStates = M.size stateMap }
  where
    s0 = nfaStartState
    originalStates = S.fromList (nfaStates nfa)
    -- Don't care about the symbols/characters for these, just reachability
    -- Remove normal final states from transitions - we've already matched so
    -- we shouldn't keep going from those.
    forwards = trace ("final states: " ++ show nfaFinalStates) $ tmReach nfaTrans `M.withoutKeys` nfaFinalStates
    backwards = trace ("forwards map: " ++ show forwards) $ invertMap forwards
    -- Find all final states reachable from the start state
    liveFromStart = close originalStates forwards S.empty [s0]
    allFinalStates = nfaFinalStates
    keptFinalStates = trace ("live from start: " ++ show liveFromStart) liveFromStart `S.intersection` allFinalStates
    -- Keep any states that can eventually reach a kept final state
    kept = trace ("kept final states: " ++ show keptFinalStates) $ close liveFromStart backwards S.empty (S.toList keptFinalStates)
    stateMap | not (s0 `S.member` kept) = trace "s0 not reachable - will always fail" M.empty
             | otherwise = trace ("kept: " ++ show kept) $ M.fromList (zip (S.toList kept) (S <$> [0..]))

    close limit trans = go
      where
        go done [] = done
        go done (x:xs) | x `S.member` done = go done xs
                       | not (x `S.member` limit) = go done xs
                       | otherwise = go (S.insert x done) (xs ++ S.toList new)
          where new = M.findWithDefault S.empty x trans

    mapState s = M.lookup s stateMap
    mapStateSet = S.fromList . mapMaybe mapState . S.toList
    mapStateTM = mapKeysMaybe mapState . M.map (M.map mapStateSet)


searchNFA nfa@NFA{..} = nfa { nfaTrans = addRetries s0 origStates nfaTrans }
  where
    s0 = nfaStartState
    origStates = nfaStates nfa
    addRetries _ [] = id
    addRetries x (y:ys) = tmInsert1 y Any x . addRetries x ys

-- Helpers and testing functions

nfaStates :: NFA -> [StateId]
nfaStates nfa = map S [0..nfaNumStates nfa - 1]

nfaNumTrans = length . tmToList . nfaTrans

-- Minimum length from the initial state to any final state.
nfaMinLength :: NFA -> Int
nfaMinLength NFA{..} = M.findWithDefault 0 nfaStartState (go M.empty 0 nfaFinalStates)
  where
    -- States in "new" are newly discovered states at distance "dist" from a
    -- final state. Start at dist = 0 with the final states, than increase
    -- distance by one and add all previous states (that we haven't already
    -- seen).
    go res dist new | S.null new = res
                    | otherwise  = go res' (dist + 1) new'
      where
        res' = res `M.union` M.fromSet (const dist) new
        new' = S.unions (map ps (S.toList new)) `S.difference` M.keysSet res'
        ps s = M.findWithDefault S.empty s allPrevStates

    allPrevStates = invertMap (tmReach nfaTrans)

prettyStates :: NFA -> String
prettyStates nfa@NFA{..} = foldMap showState ss <> "\n"
  where
    ss = nfaStates nfa
    showState s = showHeader s <> showTrans s
    showStart s = if s == nfaStartState then "START " else ""
    showFinal s | S.member s nfaFinalStates = "[" <> show s <> "]"
                | otherwise = show s
    showHeader s = showStart s <> showFinal s <> ":\n"
    showTrans s = concat ["  " ++ showT t ++ " => " ++ show p ++ "\n"
                         | let ts = M.findWithDefault M.empty s nfaTrans
                         , (t,ps) <- M.toList ts
                         , p <- S.toList ps ]
    showT Any = " . "
    showT (C c) = show c
    showT (CS cs) = show (S.toList cs)
