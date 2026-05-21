{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances #-}

-- NFA construction from regular expressions:
-- https://en.wikipedia.org/wiki/Glushkov%27s_construction_algorithm
--
-- Accepts a "tagged regex" (for convenience versus the rest of the compiler)
-- but does not allow any tags to be used.

module Regex.NFA.Glushkov where

import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import qualified Regex.TaggedRegex as TR
import Regex.TNFA (StateId(..))

import Regex.NFA.Type

type LinTrans = (NFATrans, Int)

data LinearRegex
  = Empty
  | NoMatch
  | Term LinTrans
  | Cat LinearRegex LinearRegex
  | Or LinearRegex LinearRegex
  | Repeat Int (Maybe Int) LinearRegex
  deriving (Show, Ord, Eq)

allChars = S.fromList ['\000'..'\255']

transFromTerm :: LinTrans -> Set LinTrans
transFromTerm t = S.singleton t

-- TODO Instead of char+number, replace the alphabet and add a map from index
-- to real symbol/character. Then look into alphabet reduction and e.g. map
-- indices to disjoint sets of symbols.
linearize :: TR.TaggedRegex -> LinearRegex
linearize re = evalState (go re) 0
  where
    next = modify succ >> gets pred
    nexts f = return . f =<< next

    go :: TR.TaggedRegex -> State Int LinearRegex
    go TR.Empty = return Empty
    go TR.NoMatch = return NoMatch
    go (TR.Term t) = term t
    go (TR.TagTerm _) = error "Tags should not be present here"
    go (TR.Cat x y) = Cat <$> go x <*> go y
    go (TR.Or x y) = Or <$> go x <*> go y
    go (TR.Repeat n m x) = Repeat n m <$> go x

    mkt :: NFATrans -> State Int LinearRegex
    mkt t = nexts (\n -> Term (t, n))
    char :: Char -> State Int LinearRegex
    char c = mkt (C c)
    charSet cs = mkt (CS cs)

    term :: TR.Term -> State Int LinearRegex
    term (TR.Literal cs) = foldr1 Cat <$> mapM char cs
    term (TR.Symbol c) = char c
    term (TR.EOL) = mkt EOL
    term (TR.BOL) = mkt BOL
    term (TR.Any) = mkt Any
    term (TR.CClass cs) = charSet (S.fromList cs)
    term (TR.CNotClass cs) = charSet (allChars S.\\ S.fromList cs)

-- reduce :: Set (Set Char) -> (Map (Set Char) (Set Int), Map Int (Set Char))
-- reduce ss = go ss M.empty

-- TODO Could include no match perhaps?
data Nullable = NotNull | NullAtStart | NullEmpty | NullAtEnd | NullMiddle
  deriving (Show, Ord, Eq)

-- This implies a sequence between the two nullabilities, left leading into
-- the right, which I think changes the result? Might actually be
-- commutative though.
instance Semigroup Nullable where
  NotNull     <> _           = NotNull
  _           <> NotNull     = NotNull

  NullEmpty   <> _           = NullEmpty
  _           <> NullEmpty   = NullEmpty

  NullAtStart <> NullAtStart = NullAtStart
  NullAtStart <> NullAtEnd   = NullEmpty
  NullAtStart <> NullMiddle  = NullAtStart

  NullAtEnd   <> NullAtStart = NullEmpty
  NullAtEnd   <> NullAtEnd   = NullAtEnd
  NullAtEnd   <> NullMiddle  = NullAtEnd

  NullMiddle  <> NullAtStart = NullAtStart
  NullMiddle  <> NullAtEnd   = NullAtEnd
  NullMiddle  <> NullMiddle  = NullMiddle

orNullable x y | x == y = x
               | x > y = orNullable y x
orNullable NotNull x = x
orNullable NullAtStart NullEmpty = NullAtStart
-- This wants to return a status that means *either* at end or start but
-- *not* in the middle?
-- e.g. /(foo)?(^|$)(bar)?/ which is equivalent to /foo$|^bar/
orNullable NullAtStart NullAtEnd = trace "hmm?" NullMiddle
orNullable NullAtStart NullMiddle = NullMiddle
orNullable NullEmpty NullAtEnd = NullAtEnd
orNullable NullEmpty NullMiddle = NullMiddle
orNullable x y = error ("Missing case: " ++ show x ++ " or " ++ show y)

-- capital lambda == nullable
-- But extended to keep track of where in a string it is nullable, e.g. only
-- when the whole string is empty.
nullable2 Empty = NullMiddle
nullable2 NoMatch = NotNull
nullable2 (Term (BOL,_)) = NullAtStart
nullable2 (Term (EOL,_)) = NullAtEnd
nullable2 (Term _) = NotNull
nullable2 (Cat x y) = nullable2 x <> nullable2 y
nullable2 (Or x y) = nullable2 x `orNullable` nullable2 y
nullable2 (Repeat n _ x) | n == 0 = NullMiddle
                         | otherwise = nullable2 x

-- Set of terms in the expression that could match an empty string, left
-- decides which direction to look inside a Cat
emptyTerms _ Empty = S.empty
emptyTerms _ NoMatch = S.empty
emptyTerms _ (Term t@(BOL,_)) = S.singleton t
emptyTerms _ (Term t@(EOL,_)) = S.singleton t
emptyTerms _ (Term _) = S.empty
emptyTerms left (Cat x y) = case nullable2 (if left then x else y) of
    NotNull -> emptyTerms left (if left then x else y)
    _ -> S.union (emptyTerms left x) (emptyTerms left y)
emptyTerms left (Or x y) = S.union (emptyTerms left x) (emptyTerms left y)
emptyTerms left (Repeat _ _ x) = emptyTerms left x

-- B = alphabet
alphabet :: LinearRegex -> Set LinTrans
alphabet Empty = S.empty
alphabet NoMatch = S.empty
alphabet (Term t) = transFromTerm t
alphabet (Or x y) = S.union (alphabet x) (alphabet y)
alphabet (Cat x y) = S.union (alphabet x) (alphabet y)
alphabet (Repeat _ _ x) = alphabet x

-- P = initials
initials :: LinearRegex -> Set LinTrans
initials Empty = S.empty
initials NoMatch = S.empty
initials (Term t) = transFromTerm t
initials (Or x y) = S.union (initials x) (initials y)
initials (Repeat _ _ x) = initials x
initials (Cat x y) = case nullable2 x of
  NullAtStart -> S.union (initials x) (initials y)
  NullMiddle -> S.union (initials x) (initials y)
  NullAtEnd -> S.union (initials x) (emptyTerms True y)
  NullEmpty -> S.union (initials x) (emptyTerms True y)
  NotNull -> initials x

-- D = finals
finals :: LinearRegex -> Set LinTrans
finals Empty = S.empty
finals NoMatch = S.empty
finals (Term t) = transFromTerm t
finals (Or x y) = S.union (finals x) (finals y)
finals (Repeat _ _ x) = finals x
finals (Cat x y) = case nullable2 y of
  NullAtEnd -> S.union (finals x) (finals y)
  NullMiddle -> S.union (finals x) (finals y)
  -- if y only matches a whole empty string or at start, x must be empty
  -- to match.
  NullAtStart -> S.union (emptyTerms False x) (finals y)
  NullEmpty -> S.union (emptyTerms False x) (finals y)
  NotNull -> finals x

-- F = factors
type FactorMap = Map LinTrans (Set LinTrans)
fmEmpty = M.empty
fmUnion = M.unionWith S.union
fmToList :: FactorMap -> [(LinTrans,LinTrans)]
fmToList = concatMap (\(x,ys) -> [(x,y) | y <- S.toList ys]) . M.toList
fmCart x y | S.null y = M.empty
           | otherwise = M.fromSet (const y) x

cartesian :: Set LinTrans -> Set LinTrans -> FactorMap
cartesian x y = M.fromSet (const y) x
-- cartesian x y = fmCart x' y' `fmUnion` fmCart ybol xeol `fmUnion` fmCart x' ybol `fmUnion` fmCart xeol y'
--   where (xeol, x') = partition EOL x
--         (ybol, y') = partition BOL y
seams x y = cartesian (finals x) (initials y)

partition :: NFATrans -> Set LinTrans -> (Set LinTrans, Set LinTrans)
partition sym = S.partition (\(s,_) -> s == sym)

factors :: LinearRegex -> FactorMap
factors Empty = fmEmpty
factors NoMatch = fmEmpty
factors (Term _) = fmEmpty
factors (Or x y) = factors x `fmUnion` factors y
factors (Cat x y) = factors x `fmUnion` factors y `fmUnion` seams x y
factors (Repeat _ _ x) = factors x `fmUnion` seams x x

-- API?

addEOLState nfa@NFA{..} = nfa { nfaFinalStatesEOL = eolFinalStates,
                                nfaTrans = removeEOLTrans nfaTrans }
  where
    -- Find all final states that have incoming transitions on EOL, add the
    -- source states to eolFinalStates
    allEOLTrans :: Map StateId (Set StateId)
    allEOLTrans = M.filter (not . S.null) . M.map (S.intersection nfaFinalStates . M.findWithDefault S.empty EOL) $ nfaTrans

    removeEOLTrans = M.map (M.delete EOL)

    eolFinalStates = M.keysSet allEOLTrans `S.difference` nfaFinalStates

genNFA re = compact . addEOLState . searchNFA $
    NFA { nfaFinalStates = S.fromList finalStates,
          -- At this stage we still have explicit EOL transitions
          nfaFinalStatesEOL = S.fromList initEOL,
          nfaTrans = transMap,
          nfaNumStates = 1 + M.size stateMap }
  where
    s0 = S 0
    lre = linearize re
    d = S.toList (finals lre)
    az = S.toList (alphabet lre)
    stateMap = M.fromList (zip az (S <$> [1..]))
    get a = fromJust (M.lookup a stateMap)
    (initFinalState, initEOL) = case nullable2 lre of
      NotNull -> ([], [])
      NullAtEnd -> ([], [s0])
      NullEmpty -> ([], [s0])
      _ -> ([s0], [])
    finalStates = map get d ++ initFinalState
    transList = initTrans ++ factorsTrans
    initTrans = [(s0, fst q, get q) | q <- S.toList (initials lre)]
    factorsTrans = [(get p, fst q, get q) | (p,q) <- fmToList (factors lre)]
    transMap = tmFromList transList


-- TODO glushkovCompatible re = not (TR.hasAnchors re)
