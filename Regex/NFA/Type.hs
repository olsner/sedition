{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances #-}

-- Type for NFA automaton without tags, and possible with BOL and EOL
-- transitions although Glushkov's construction will not use them.

module Regex.NFA.Type where

import Control.Monad

import Data.Array.Unboxed
import Data.Array.ST
import Data.Bits
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
  = BOL
  | C Char
  | CS (Set Char)
  | Any
  | EOL
  deriving (Show, Ord, Eq)

type TransMap k = Map StateId (Map k (Set StateId))
-- tmUnion :: Ord k => TransMap k -> TransMap k -> TransMap k
-- tmUnion = M.unionWith (M.unionWith S.union)
tmFromList :: Ord k => [(StateId, k, StateId)] -> TransMap k
tmFromList [] = M.empty
tmFromList ((k1,k2,v):xs) = tmInsert1 k1 k2 v (tmFromList xs)
tmInsert1 k1 k2 v = tmInsert k1 (M.singleton k2 (S.singleton v))
tmInsert k v = M.insertWith (M.unionWith S.union) k v
tmLookup k1 k2 m = M.findWithDefault S.empty k2 (M.findWithDefault M.empty k1 m)
tmReach :: TransMap k -> Map StateId (Set StateId)
tmReach = M.map (S.unions . M.elems)

data NFA = NFA
  { nfaFinalStates :: Set StateId
  , nfaFinalStatesEOL :: Set StateId
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

-- TODO I think there are more opportunities here.
-- Transitions out of a final state are pointless since we've already matched
-- at that point, for example.
-- The basic elimination of states unreachable from the start and the final
-- states does seem to work though.
compact nfa@NFA{..} = NFA {
    nfaFinalStates = mapStateSet nfaFinalStates,
    nfaFinalStatesEOL = mapStateSet nfaFinalStatesEOL,
    nfaTrans = mapStateTM nfaTrans,
    nfaNumStates = M.size stateMap }
  where
    s0 = nfaStartState
    originalStates = S.fromList (nfaStates nfa)
    -- Don't care about the symbols/characters for these, just reachability
    -- Remove normal final states from transitions - we've already matched so
    -- we shouldn't keep going from those. But keep EOL final states since
    -- those only sometimes match.
    forwards = trace ("final states: " ++ show nfaFinalStates) $ tmReach nfaTrans `M.withoutKeys` nfaFinalStates
    backwards = trace ("forwards map: " ++ show forwards) $ invertMap forwards
    -- Find all final states reachable from the start state
    liveFromStart = close originalStates forwards S.empty [s0]
    allFinalStates = S.union nfaFinalStates nfaFinalStatesEOL
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


searchNFA nfa@NFA{..} = nfa { nfaTrans = updatedTransMap,
                              nfaNumStates = newNumStates }
  where
    s0 = nfaStartState
    sT = M.findWithDefault M.empty s0 nfaTrans
    hasBOL = M.member BOL sT
    newNumStates | hasBOL = 1 + nfaNumStates
                 | otherwise = nfaNumStates
    sNotBOL | hasBOL = S nfaNumStates
            | otherwise = s0

    origStates = S <$> [0..nfaNumStates - 1]
    addRetries _ [] = id
    addRetries x (y:ys) = tmInsert1 y Any x . addRetries x ys

    bol_closure = S.toList (S.delete s0 (close S.empty [s0]))
    notBOLTrans = M.map (M.delete BOL) nfaTrans

    trans_bol :: Map NFATrans (Set StateId)
    trans_bol = M.unionsWith S.union [ M.findWithDefault M.empty s notBOLTrans | s <- bol_closure]
    updatedTransMap = addRetries sNotBOL origStates . tmInsert s0 trans_bol $ notBOLTrans
    close :: Set StateId -> [StateId] -> Set StateId
    close done [] = done
    close done (s:ss)
      | s `S.member` done = close done ss
      | otherwise = close (S.insert s done) (ss ++ S.toList (tmLookup s BOL nfaTrans))


-- Stuff
-- TODO Move bit NFA construction to separate module

data BitNFA w = BitNFA
  { bitInitStates :: w
  , bitFinalStates :: w
  , bitFinalStatesEOL :: w
  , bitNumStates :: Int
  -- Used for reverse matching
  -- , bitFollows :: Array w w
  , bitT :: UArray w w
  -- For compact printing etc, but expected to be a 256-word array in the
  -- end.
  , bitCommonB :: w
  , bitB :: Map Char w
  }

deriving instance Show (BitNFA Word)

bitwiseNFA :: NFA -> Maybe (BitNFA Word)
bitwiseNFA nfa@NFA{..} | nfaNumStates > finiteBitSize commonB || nfaHasAnchors nfa = Nothing
                       | otherwise = Just $ BitNFA {
    bitInitStates = bit nfaStartState,
    bitFinalStates = bits nfaFinalStates,
    bitFinalStatesEOL = bits nfaFinalStatesEOL,
    bitT = t, bitCommonB = commonB, bitB = bmap,
    bitNumStates = nfaNumStates }
  where
    or = foldr (.|.) zeroBits
    and = foldr (.&.) oneBits
    bit (S i) = 1 `shiftL` i
    bits s = or (map bit (S.toList s))
    follow = tmReach nfaTrans
    fbits = M.map bits follow
    -- b = listArray (0, 255) (map getB ['\000'..'\255'])
    bmap = M.fromList [(c,b) | c <- ['\000'..'\255'], let b = getB c .&. (complement commonB), b /= 0]
    charsets = M.map bits (M.unionsWith S.union (M.elems nfaTrans))
    anyB = M.findWithDefault 0 Any charsets
    getB c = M.findWithDefault 0 (C c) charsets
    commonB = and (map getB ['\000'..'\255']) .|. anyB

    t = runSTUArray $ do
      arr <- newArray (0, 1 `shiftL` nfaNumStates - 1) 0
      forM_ (nfaStates nfa) $ \s ->
        forM_ [0 .. bit s - 1] $ \j -> do
          t_j <- readArray arr j
          writeArray arr (bit s + j) (t_j .|. M.findWithDefault 0 s fbits)
      return arr

-- Helpers and testing functions

nfaStates :: NFA -> [StateId]
nfaStates nfa = map S [0..nfaNumStates nfa - 1]

nfaHasAnchors NFA{..} = any (`S.member` allTrans) [BOL, EOL]
  where allTrans = S.unions (map M.keysSet (M.elems nfaTrans))

prettyStates :: NFA -> String
prettyStates nfa@NFA{..} = foldMap showState ss <> "\n"
  where
    ss = nfaStates nfa
    showState s = showHeader s <> showTrans s
    showStart s = if s == nfaStartState then "START " else ""
    showEOL s   = if S.member s nfaFinalStatesEOL then "EOL " else ""
    showFinal s | S.member s nfaFinalStates = "[" <> show s <> "]"
                | otherwise = show s
    showHeader s = showStart s <> showEOL s <> showFinal s <> ":\n"
    showTrans s = concat ["  " ++ showT t ++ " => " ++ show p ++ "\n"
                         | let ts = M.findWithDefault M.empty s nfaTrans
                         , (t,ps) <- M.toList ts
                         , p <- S.toList ps ]
    showT BOL = " ^ "
    showT EOL = " $ "
    showT Any = " . "
    showT (C c) = show c
    showT (CS cs) = show (S.toList cs)
