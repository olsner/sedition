{-# LANGUAGE RecordWildCards #-}

module TDFA2C where

import Control.Monad.Trans.State.Strict

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import Data.Set (Set)
import qualified Data.Set as S

import Regex (Regex)
import qualified Regex

type StateId = Int
type TagId = Int
type Prio = Int

data Tag = NoTag | UnTag TagId | Tag TagId deriving (Show, Ord, Eq)

data TNFATrans
  = BOL
  | Any
  | EOL
  | Symbol Char
  | CClass [Char]
  | CNotClass [Char]
  | Eps Prio Tag
  deriving (Show, Ord, Eq)

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
  return (qN { tnfaStartState = s0 } <>
          eps s0 (tnfaStartState q1) 1 <>
          eps s0 (tnfaStartState q1') 2)

tnfa :: StateId -> TaggedRegex -> GenTNFA TNFA
tnfa finalState re =
  case re of
    Empty -> return (TNFA finalState finalState [])
    Term term -> trans term finalState
    Cat x y -> do
      q2 <- tnfa finalState y
      q1 <- tnfa (tnfaStartState q2) x
      return (q1 <> q2)
    -- Number groups outside of the TNFA generation machine so that they are
    -- consistently numbered from where their left-hand parenthesis is.
    (Group t1 x t2) -> do
        q3 <- tag finalState 1 t2
        q2 <- tnfa (tnfaStartState q3) x
        q1 <- tag (tnfaStartState q2) 1 t1
        return (q1 <> q2 <> q3)
    (Or x y) -> orTNFA finalState x y

data TaggedRegex
  = Empty
  | Term TNFATrans
  | Group TagId TaggedRegex TagId
  | Cat TaggedRegex TaggedRegex
  | Or TaggedRegex TaggedRegex
  | Repeat Int (Maybe Int) TaggedRegex
  deriving (Show, Ord, Eq)

tagRegex :: Regex -> TaggedRegex
tagRegex re = Group 0 (evalState (go re) 2) 1
  where
    go Regex.Empty = return Empty
    go Regex.Any = return (Term Any)
    go (Regex.Char c) = return (Term (Symbol c))
    go (Regex.CClass cs) = return (Term (CClass cs))
    go (Regex.CNotClass cs) = return (Term (CNotClass cs))
    go Regex.AnchorStart = return (Term BOL)
    go Regex.AnchorEnd = return (Term EOL)
    go (Regex.Concat xs) = foldr1 Cat <$> mapM go xs
    go (Regex.Or xs) = foldr1 Or <$> mapM go xs
    go (Regex.Group x) = Group <$> tag <*> go x <*> tag
    go (Regex.Repeat n m x) = Repeat n m <$> go x
    go (Regex.BackRef i) = error "Back-references not supported in TDFA"

    tag = get <* modify succ

-- tdfa re = determinize (tnfa re)
  -- | CClass [Char]
  -- | CNotClass [Char]
  -- -- Min repeats and max repeats (Nothing for unlimited)
  -- | Repeat Int (Maybe Int) Regex
  -- | AnchorStart
  -- | AnchorEnd
  -- | Empty
  -- | Or [Regex]
  -- | BackRef Int


genTNFA :: TaggedRegex -> TNFA
genTNFA re = evalState (tnfa 0 re) 1

tdfa2c :: Regex -> String
tdfa2c re = show (genTNFA (tagRegex re))

testTagRegex = tagRegex . Regex.parseString True . C.pack

testTNFA :: String -> String
testTNFA = prettyStates . genTNFA . testTagRegex

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
