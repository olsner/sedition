{-# LANGUAGE RecordWildCards #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"

module TDFA2C where

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

data TaggedRegex
  = Empty
  | Term TNFATrans
  | TagTerm TagId
  | Cat TaggedRegex TaggedRegex
  | Or TaggedRegex TaggedRegex
  | Repeat Int (Maybe Int) TaggedRegex
  deriving (Show, Ord, Eq)

tagRegex :: Regex -> TaggedRegex
tagRegex re = evalState (go (Regex.Group re)) 0
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
    go (Regex.Group x) = do
      tStart <- tag
      tEnd <- tag
      tre <- go x
      return (cat3 tStart tre tEnd)
    go (Regex.Repeat n m x) = Repeat n m <$> go x
    go (Regex.BackRef i) = error "Back-references not supported in TDFA"

    tag = gets TagTerm <* modify succ
    cat3 x y z = Cat x (Cat y z)

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

testTNFA :: String -> IO ()
testTNFA = putStr . prettyStates . genTNFA . testTagRegex

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

testTNFASimulation s = tnfaSimulation s . genTNFA . testTagRegex

type Matches = Map TagId Int
type ConfigMap = Map StateId Matches

tnfaSimulation :: String -> TNFA -> Maybe Matches
tnfaSimulation as tnfa =
    initSimulation tnfa (M.singleton (tnfaStartState tnfa) M.empty) as

finalSimulatedState fin c = go (M.toList c)
  where
      go [] = Nothing
      go ((q, m):xs) | q == fin = Just m
                     | otherwise = go xs

initSimulation :: TNFA -> ConfigMap -> String -> Maybe Matches
initSimulation tnfa c xs = trace simTrace $ simulation tnfa c' 0 xs
  where c' = epsilonClosure tnfa c 0 (null xs)
        simTrace = "Init: " ++ show c ++ " -> " ++ show c'

simulation :: TNFA -> ConfigMap -> Int -> String -> Maybe Matches
simulation tnfa c k [] =
    trace simTrace $ finalSimulatedState (tnfaFinalState tnfa) c'
  where c' = epsilonClosure tnfa c k True
        simTrace = "Ending at " ++ show k ++ ": " ++ show c ++ " -> " ++ show c'
simulation tnfa c k (x:xs) | M.null c'' = trace "Out of states: No match" $ Nothing
                           | otherwise  = trace simTrace $ simulation tnfa c'' (k + 1) xs
  where c' = epsilonClosure tnfa c k False
        c'' = stepOnSymbol tnfa c' x
        simTrace = "Continuing at " ++ show k ++ " (" ++ show x ++ "): " ++ show c ++ " -> " ++ show c' ++ " -> " ++ show c''

matchTerm Any _ = True
matchTerm (Eps _ _) _ = False
matchTerm (Symbol x) y = x == y
matchTerm (CClass xs) y = y `elem` xs
matchTerm (CNotClass xs) y = not (y `elem` xs)
matchTerm BOL _ = False
matchTerm EOL _ = False

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
    go :: [(StateId, Matches)] -> ConfigMap -> [(StateId, Matches)]
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
