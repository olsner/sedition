{-# LANGUAGE RecordWildCards #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Conversion of tagged regex to Tagged Non-Deterministic Finite Automata.

module TNFA where

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

type StateId = Int

data TNFA = TNFA {
    tnfaStartState :: StateId,
    tnfaFinalState :: StateId,
    tnfaTrans :: [(StateId, TNFATrans, StateId)]
  }
  deriving (Show, Ord, Eq)

instance Semigroup TNFA where
  -- Doesn't add a transition from final a -> start b, assume that's already
  -- done?
  a <> b = TNFA (tnfaStartState a) (tnfaFinalState b) (tnfaTrans a ++ tnfaTrans b)

type GenTNFA a = State Int a

-- For each tag mentioned in m, add one state and one negative tag operation
-- such that going from start state to the final state unsets all tags and
-- matches no input. This will then be concatenated into the "negative" branch
-- of an alternative.
ntags :: StateId -> TNFA -> GenTNFA TNFA
ntags finalState tnfa = go (tnfaTrans tnfa)
  where
    go []     = return (TNFA finalState finalState [])
    go ((_,Eps p (Tag tag),_):xs) = do
        q2 <- go xs
        q1 <- trans (Eps p (UnTag tag)) (tnfaStartState q2)
        return (q1 <> q2)
    go (_:xs) = go xs

tag :: StateId -> Prio -> TagId -> GenTNFA TNFA
tag s p n = trans (Eps p (Tag n)) s

trans :: TNFATrans -> StateId -> GenTNFA TNFA
trans t p = newState >>= \q -> return (trans' q t p)

trans' q t p = TNFA q p [(q, t, p)]
eps q s p = trans' q (Eps p NoTag) s

newState = get <* modify succ

concatTNFA :: StateId -> [TaggedRegex] -> GenTNFA TNFA
concatTNFA finalState xs =
  case xs of
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
  return (eps s0 (tnfaStartState q1) 1 <>
          eps s0 (tnfaStartState q1') 2 <>
          qN)

tnfa :: StateId -> TaggedRegex -> GenTNFA TNFA
tnfa finalState re =
  case re of
    Empty -> return (TNFA finalState finalState [])
    Term term -> trans term finalState
    TagTerm t -> tag finalState 1 t
    Cat x y -> do
      q2 <- tnfa finalState y
      q1 <- tnfa (tnfaStartState q2) x
      return (q1 <> q2)
    (Or x y) -> orTNFA finalState x y
    (Repeat 0 m x) -> do
        m1@(TNFA q1 _ _) <- tnfa finalState (Repeat 1 m x)
        m1'@(TNFA q1' _ _) <- ntags finalState m1
        q0 <- newState
        return (eps q0 q1 1 <> eps q0 q1' 2 <> m1' <> m1)
    (Repeat 1 Nothing x) -> do
        q1 <- newState
        m1@(TNFA q0 _ _) <- tnfa q1 x
        return (m1 <> eps q1 q0 1 <> eps q1 finalState 2)
    (Repeat 1 (Just 1) x) -> tnfa finalState x
    (Repeat 1 (Just m) x) -> do
        m2@(TNFA q1 _ _) <- tnfa finalState (Repeat 1 (Just (pred m)) x)
        m1@(TNFA _ q2 _) <- tnfa q1 x
        return (m1 <> m2 <>
                eps q1 q2 2 <>
                eps q1 finalState 1)
    (Repeat n m x) -> do
        q2 <- tnfa finalState (Repeat (pred n) (pred <$> m) x)
        q1 <- tnfa (tnfaFinalState q2) x
        return (q1 <> q2)

-- API?

genTNFA :: TaggedRegex -> TNFA
genTNFA re = evalState (tnfa 0 re) 1

-- Test functions

prettyStates :: TNFA -> String
prettyStates TNFA{..} = go S.empty [tnfaStartState]
  where
    go seen (s:ss)
        | not (S.member s seen) =
            showState s <> showTrans s <>
            go (S.insert s seen) (ss ++ nextStates s)
        | otherwise = go seen ss
    go seen [] = []
    nextStates s = [p | (q,_,p) <- tnfaTrans, q == s]
    showState s | s == tnfaStartState = "START " ++ show s ++ ":\n"
    showState s | s == tnfaFinalState = "FINAL " ++ show s ++ ":\n"
    showState s = "State " ++ show s ++ ":\n"
    showTrans s = concat ["  " ++ show t ++ " => " ++ show p ++ "\n"
                            | (q,t,p) <- tnfaTrans, q == s]

testTNFA :: String -> IO ()
testTNFA = putStr . prettyStates . genTNFA . testTagRegex
