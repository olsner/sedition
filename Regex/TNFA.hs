{-# LANGUAGE RecordWildCards,RecursiveDo #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Conversion of tagged regex to Tagged Non-Deterministic Finite Automata.

module Regex.TNFA where

import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

-- import Debug.Trace

import Regex.TaggedRegex hiding (Term(..))
import qualified Regex.TaggedRegex as TR

newtype Prio = P Int deriving (Show, Ord, Eq)

data Tag = NoTag | UnTag TagId | Tag TagId deriving (Ord, Eq)
instance Show Tag where
  show NoTag = "e"
  show (Tag (T x)) = 't' : show x
  show (UnTag (T x)) = '-' : 't' : show x

data TNFATrans
  = BOL
  | Any
  | EOL
  | Symbol Char
  | CClass [Char]
  | CNotClass [Char]
  | Eps Prio Tag
  deriving (Show, Ord, Eq)

newtype StateId = S Int deriving (Ord, Eq)
instance Show StateId where
  show (S x) = 'q' : show x

symbolTrans :: TNFATrans -> Bool
symbolTrans (Eps _ _) = False
symbolTrans BOL = False
symbolTrans EOL = True -- symbol in TDFA, epsilon in SimulateTNFA
symbolTrans _ = True

tnfaTransFromTerm TR.BOL = BOL
tnfaTransFromTerm TR.Any = Any
tnfaTransFromTerm TR.EOL = EOL
tnfaTransFromTerm (TR.Symbol c) = Symbol c
tnfaTransFromTerm (TR.CClass cs) = CClass cs
tnfaTransFromTerm (TR.CNotClass cs) = CNotClass cs
tnfaTransFromTerm (TR.Literal _) = error "Need to expand literals before here!"

data TNFA = TNFA {
    tnfaStartState :: StateId,
    tnfaFinalState :: StateId,
    tnfaTrans :: Map StateId [(TNFATrans, StateId)],
    -- TODO This is just attached after construction. We want to bundle it for
    -- following steps, but maybe that means the construction should stop using
    -- the same data type?
    tnfaTagMap :: FixedTagMap,
    -- States that are allowed to remain after epsilon closure, i.e. that have
    -- any outgoing non-epsilon transitions or are the final state.
    -- States not in this set only have epsilon transitions from them so they
    -- should only be "intermediate" steps within epsilonClosure, not included
    -- in the output.
    tnfaClosedStates :: Set StateId
  }
  deriving (Show, Ord, Eq)

data NFA = NFA { nfaStartState :: StateId, nfaFinalState :: StateId,
                 nfaTrans :: [(StateId, TNFATrans, StateId)] }
           deriving (Show, Ord, Eq)

allTags :: TNFA -> Set TagId
allTags TNFA{..} = S.fromList (concatMap (mapMaybe tag) (M.elems tnfaTrans))
  where
    tag (Eps _ (Tag t),_) = Just t
    tag (Eps _ (UnTag t),_) = Just t
    tag _ = Nothing

instance Semigroup NFA where
  -- Doesn't add a transition from final a -> start b, assume that's already
  -- done?
  a <> b = NFA (nfaStartState a) (nfaFinalState b) (nfaTrans a ++ nfaTrans b)

type GenTNFA a = State Int a

-- For each tag mentioned in m, add one state and one negative tag operation
-- such that going from start state to the final state unsets all tags and
-- matches no input. This will then be concatenated into the "negative" branch
-- of an alternative.
ntags :: StateId -> NFA -> GenTNFA NFA
ntags finalState nfa = go (nfaTrans nfa)
  where
    go []     = return (emptyNFA finalState)
    go ((_,Eps p (Tag tag),_):xs) = do
        q2 <- go xs
        q1 <- trans (Eps p (UnTag tag)) (nfaStartState q2)
        return (q1 <> q2)
    go (_:xs) = go xs

tag :: StateId -> Prio -> TagId -> GenTNFA NFA
tag s p n = trans (Eps p (Tag n)) s

trans :: TNFATrans -> StateId -> GenTNFA NFA
trans t p = newState >>= \q -> return (trans' q t p)

trans' :: StateId -> TNFATrans -> StateId -> NFA
trans' q t p = NFA q p [(q, t, p)]
eps :: StateId -> StateId -> Prio -> NFA
eps q s p = trans' q (Eps p NoTag) s

newState :: GenTNFA StateId
newState = gets S <* modify succ

concatNFA :: StateId -> [TaggedRegex] -> GenTNFA NFA
concatNFA finalState xs =
  case xs of
    [] -> error "concatTNFA requires at least one item in list"
    [x] -> nfa finalState x
    (x:xs) -> do
      q2 <- concatNFA finalState xs
      q1 <- nfa (nfaStartState q2) x
      return (q1 <> q2)

orNFA :: StateId -> TaggedRegex -> TaggedRegex -> GenTNFA NFA
orNFA finalState x y = do
  -- Build start -> q1 -> q2' -> final and start -> q1' -> q2 -> final.
  q2 <- nfa finalState y
  q2' <- ntags finalState q2
  q1 <- nfa (nfaStartState q2') x
  q1' <- ntags (nfaStartState q2) q1
  let qN = q1 <> q2 <> q1' <> q2'
  s0 <- newState
  return (eps s0 (nfaStartState q1) (P 1) <>
          eps s0 (nfaStartState q1') (P 2) <>
          qN)

emptyNFA :: StateId -> NFA
emptyNFA s = NFA s s []

nfa :: StateId -> TaggedRegex -> GenTNFA NFA
nfa finalState re =
  case re of
    Empty -> return (emptyNFA finalState)
    TR.Term (TR.Literal []) -> return (emptyNFA finalState)
    TR.Term (TR.Literal (x:xs)) ->
      nfa finalState (Cat (TR.Term (TR.Symbol x))
                          (TR.Term (TR.Literal xs)))
    TR.Term term -> trans (tnfaTransFromTerm term) finalState
    TagTerm t -> tag finalState (P 1) t
    Cat x y -> mdo
      q1 <- nfa (nfaStartState q2) x
      q2 <- nfa finalState y
      return (q1 <> q2)
    (Or x y) -> orNFA finalState x y
    (Repeat 0 m x) -> mdo
        m1@(NFA q1 _ _) <- nfa finalState (Repeat 1 m x)
        m1'@(NFA q1' _ _) <- ntags finalState m1
        q0 <- newState
        return (eps q0 q1 (P 1) <> eps q0 q1' (P 2) <> m1' <> m1)
    (Repeat 1 Nothing x) -> mdo
        m1@(NFA q0 _ _) <- nfa q1 x
        q1 <- newState
        return (m1 <> eps q1 q0 (P 1) <> eps q1 finalState (P 2))
    (Repeat 1 (Just 1) x) -> nfa finalState x
    (Repeat 1 (Just m) x) -> mdo
        m1@(NFA _ q2 _) <- nfa q1 x
        m2@(NFA q1 _ _) <- nfa finalState (Repeat 1 (Just (pred m)) x)
        return (m1 <> m2 <>
                eps q1 q2 (P 2) <>
                eps q1 finalState (P 1))
    (Repeat n m x) -> mdo
        q1 <- nfa (nfaStartState q2) x
        q2 <- nfa finalState (Repeat (pred n) (pred <$> m) x)
        return (q1 <> q2)

-- API?

genTNFA :: (TaggedRegex, FixedTagMap) -> TNFA
genTNFA (re, m) = TNFA {
    tnfaStartState = nfaStartState,
    tnfaFinalState = nfaFinalState,
    tnfaTrans = multiMapFromList [(s,(t,p)) | (s,t,p) <- nfaTrans],
    tnfaTagMap = m,
    tnfaClosedStates = closedStates }
  where
    NFA{..} = evalState (mdo { m <- nfa f re ; f <- newState; return m }) 0
    closedStates = S.insert nfaFinalState $
        S.fromList [s | (s,t,_) <- nfaTrans, symbolTrans t]

multiMapFromList :: Ord a => [(a,b)] -> Map a [b]
multiMapFromList ts = foldr prepend M.empty ts
  where
    prepend (s,t) m = M.insert s (t : M.findWithDefault [] s m) m

tnfaStates TNFA{..} = go S.empty [tnfaStartState]
  where
    go seen (s:ss)
        | not (S.member s seen) = s : go (S.insert s seen) (ss ++ nextStates s)
        | otherwise = go seen ss
    go _ [] = []
    nextStates s = [p | (_,p) <- M.findWithDefault [] s tnfaTrans]

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
                            | (t,p) <- M.findWithDefault [] s tnfaTrans]
    fixedTags | M.null tnfaTagMap = "(No fixed tags)"
              | otherwise = "Fixed tags:\n" ++
        concat [ "  " ++ show t ++ " <- " ++ show ft ++ "\n"
                 | (t,ft) <- M.toList tnfaTagMap ]

testTNFA :: String -> IO ()
testTNFA = putStr . prettyStates . genTNFA . testTagRegex
