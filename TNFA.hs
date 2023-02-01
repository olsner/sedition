{-# LANGUAGE RecordWildCards #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Conversion of tagged regex to Tagged Non-Deterministic Finite Automata.

module TNFA where

import Control.Monad.Trans.State.Strict

import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

-- import Debug.Trace

import TaggedRegex

newtype StateId = S Int deriving (Ord, Eq)
instance Show StateId where
  show (S x) = 'q' : show x

data TNFA = TNFA {
    tnfaStartState :: StateId,
    tnfaFinalState :: StateId,
    tnfaTrans :: [(StateId, TNFATrans, StateId)],
    -- TODO This is just attached after construction. We want to bundle it for
    -- following steps, but maybe that means the construction should stop using
    -- the same data type?
    tnfaTagMap :: FixedTagMap
  }
  deriving (Show, Ord, Eq)

allTags :: TNFA -> Set TagId
allTags TNFA{..} = S.fromList (mapMaybe tag tnfaTrans)
  where
    tag (_,Eps _ (Tag t),_) = Just t
    tag (_,Eps _ (UnTag t),_) = Just t
    tag _ = Nothing

instance Semigroup TNFA where
  -- Doesn't add a transition from final a -> start b, assume that's already
  -- done?
  a <> b = TNFA (tnfaStartState a) (tnfaFinalState b) (tnfaTrans a ++ tnfaTrans b) M.empty

type GenTNFA a = State Int a

-- For each tag mentioned in m, add one state and one negative tag operation
-- such that going from start state to the final state unsets all tags and
-- matches no input. This will then be concatenated into the "negative" branch
-- of an alternative.
ntags :: StateId -> TNFA -> GenTNFA TNFA
ntags finalState tnfa = go (tnfaTrans tnfa)
  where
    go []     = return (TNFA finalState finalState [] M.empty)
    go ((_,Eps p (Tag tag),_):xs) = do
        q2 <- go xs
        q1 <- trans (Eps p (UnTag tag)) (tnfaStartState q2)
        return (q1 <> q2)
    go (_:xs) = go xs

tag :: StateId -> Prio -> TagId -> GenTNFA TNFA
tag s p n = trans (Eps p (Tag n)) s

trans :: TNFATrans -> StateId -> GenTNFA TNFA
trans t p = newState >>= \q -> return (trans' q t p)

trans' :: StateId -> TNFATrans -> StateId -> TNFA
trans' q t p = TNFA q p [(q, t, p)] M.empty
eps :: StateId -> StateId -> Prio -> TNFA
eps q s p = trans' q (Eps p NoTag) s

newState :: GenTNFA StateId
newState = gets S <* modify succ

concatTNFA :: StateId -> [TaggedRegex] -> GenTNFA TNFA
concatTNFA finalState xs =
  case xs of
    [] -> error "concatTNFA requires at least one item in list"
    [x] -> tnfa finalState x
    (x:xs) -> do
      q2 <- concatTNFA finalState xs
      q1 <- tnfa (tnfaStartState q2) x
      return (q1 <> q2)

orTNFA :: StateId -> TaggedRegex -> TaggedRegex -> GenTNFA TNFA
orTNFA finalState x y = do
  -- Build start -> q1 -> q2' -> final and start -> q1' -> q2 -> final.
  q2 <- tnfa finalState y
  q2' <- ntags finalState q2
  q1 <- tnfa (tnfaStartState q2') x
  q1' <- ntags (tnfaStartState q2) q1
  let qN = q1 <> q2 <> q1' <> q2'
  s0 <- newState
  return (eps s0 (tnfaStartState q1) (P 1) <>
          eps s0 (tnfaStartState q1') (P 2) <>
          qN)

tnfa :: StateId -> TaggedRegex -> GenTNFA TNFA
tnfa finalState re =
  case re of
    Empty -> return (TNFA finalState finalState [] M.empty)
    Term term -> trans term finalState
    TagTerm t -> tag finalState (P 1) t
    Cat x y -> do
      q2 <- tnfa finalState y
      q1 <- tnfa (tnfaStartState q2) x
      return (q1 <> q2)
    (Or x y) -> orTNFA finalState x y
    (Repeat 0 m x) -> do
        m1@(TNFA q1 _ _ _) <- tnfa finalState (Repeat 1 m x)
        m1'@(TNFA q1' _ _ _) <- ntags finalState m1
        q0 <- newState
        return (eps q0 q1 (P 1) <> eps q0 q1' (P 2) <> m1' <> m1)
    (Repeat 1 Nothing x) -> do
        q1 <- newState
        m1@(TNFA q0 _ _ _) <- tnfa q1 x
        return (m1 <> eps q1 q0 (P 1) <> eps q1 finalState (P 2))
    (Repeat 1 (Just 1) x) -> tnfa finalState x
    (Repeat 1 (Just m) x) -> do
        m2@(TNFA q1 _ _ _) <- tnfa finalState (Repeat 1 (Just (pred m)) x)
        m1@(TNFA _ q2 _ _) <- tnfa q1 x
        return (m1 <> m2 <>
                eps q1 q2 (P 2) <>
                eps q1 finalState (P 1))
    (Repeat n m x) -> do
        q2 <- tnfa finalState (Repeat (pred n) (pred <$> m) x)
        q1 <- tnfa (tnfaFinalState q2) x
        return (q1 <> q2)

-- API?

genTNFA :: (TaggedRegex, FixedTagMap) -> TNFA
genTNFA (re, m) = (evalState (tnfa (S 0) re) 1) { tnfaTagMap = m }

tnfaStates TNFA{..} = go S.empty [tnfaStartState]
  where
    go seen (s:ss)
        | not (S.member s seen) = s : go (S.insert s seen) (ss ++ nextStates s)
        | otherwise = go seen ss
    go _ [] = []
    nextStates s = [p | (q,_,p) <- tnfaTrans, q == s]

-- Test functions

prettyStates :: TNFA -> String
prettyStates tnfa@TNFA{..} = foldMap showState ss <> fixedTags <> "\n"
  where
    ss = tnfaStates tnfa
    showState s = showHeader s <> showTrans s
    showHeader s | s == tnfaStartState = "START " ++ show s ++ ":\n"
    showHeader s | s == tnfaFinalState = "FINAL " ++ show s ++ ":\n"
    showHeader s = "State " ++ show s ++ ":\n"
    showTrans s = concat ["  " ++ show t ++ " => " ++ show p ++ "\n"
                            | (q,t,p) <- tnfaTrans, q == s]
    fixedTags | M.null tnfaTagMap = "(No fixed tags)"
              | otherwise = "Fixed tags:\n" ++
        concat [ "  " ++ show t ++ " <- " ++ show ft ++ "\n"
                 | (t,ft) <- M.toList tnfaTagMap ]

testTNFA :: String -> IO ()
testTNFA = putStr . prettyStates . genTNFA . testTagRegex
