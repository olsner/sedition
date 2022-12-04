module TDFA2C where

import Control.Monad.Trans.State.Strict

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C

import Regex hiding (Any, Char, CClass, CNotClass)
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

type GenTNFA a = State (Int, Int) a

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

newState = do
  res <- gets snd
  modify (\(tag,state) -> (tag, state + 1))
  return res
newTag = do
  res <- gets snd
  modify (\(tag,state) -> (res + 1, state))
  return res

concatTNFA finalState xs =
  case xs of
    [x] -> tnfa finalState x
    (x:xs) -> do
      q2 <- concatTNFA finalState xs
      q1 <- tnfa (tnfaStartState q2) x
      return (q1 <> q2)

orTNFA :: StateId -> [Regex] -> GenTNFA TNFA
orTNFA finalState xs =
  case xs of
    [x] -> tnfa finalState x
    (x:xs) -> do
      q2 <- orTNFA finalState xs
      q2' <- ntags finalState q2
      q1 <- tnfa (tnfaStartState q2') x
      q1' <- ntags (tnfaStartState q2) q1
      let qN = q1 <> q2 <> q1' <> q2'
      s0 <- newState
      return (qN <>
              eps s0 (tnfaStartState q1) 1 <>
              eps s0 (tnfaStartState q1') 2)

tnfa :: StateId -> Regex -> GenTNFA TNFA
tnfa finalState re =
  case re of
    Regex.Empty -> return (TNFA finalState finalState [])
    Regex.Any -> trans Any finalState
    (Regex.Char c) -> trans (Symbol c) finalState
    (Regex.CClass cs) -> trans (CClass cs) finalState
    (Regex.CNotClass cs) -> trans (CNotClass cs) finalState
    AnchorStart -> trans BOL finalState
    AnchorEnd -> trans EOL finalState
    (Concat xs) -> concatTNFA finalState xs
    -- Number groups outside of the TNFA generation machine so that they are
    -- consistently numbered from where their left-hand parenthesis is.
    (Group x) -> do
        t1 <- newTag
        t2 <- newTag
        q3 <- tag finalState 1 t1
        q2 <- tnfa (tnfaStartState q3) x
        q1 <- tag (tnfaStartState q2) 1 t2
        return (q1 <> q2 <> q3)
    (Or xs) -> orTNFA finalState xs

{-
data TaggedRegex
  = Empty
  | Term TNFATrans
  | Group TagId TaggedRegex TagId
  | Concat TaggedRegex TaggedRegex
  | Or TaggedRegex TaggedRegex
  | Repeat Int (Maybe Int) TaggedRegex
  deriving (Show, Ord, Eq)

tagRegex :: Regex -> TaggedRegex
tagRegex re = Group 0 (go re 2) 1
  where
    go Regex.Empty = Empty
-}

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


genTNFA :: Regex -> TNFA
genTNFA re = evalState (tnfa 0 re) (0, 1)

tdfa2c :: Regex -> String
tdfa2c re = show (genTNFA re)

testTNFA :: String -> String
testTNFA = tdfa2c . Regex.parseString True . C.pack
