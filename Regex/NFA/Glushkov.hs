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
  | Repeat LinearRegex -- 0 to Inf repetitions -- TODO Would it be better to treat this as 1 or more? Can always or with empty...
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
    go (TR.Repeat m n x) = rep m n x

    rep 0 Nothing x = Repeat <$> go x
    rep n Nothing x = Cat <$> go x <*> rep (pred n) Nothing x
    rep 0 (Just 0) _ = return Empty
    rep 0 (Just m) x = Or Empty <$> rep 1 (Just m) x
    rep n (Just m) x = Cat <$> go x <*> rep (pred n) (Just (pred m)) x

    mkt :: NFATrans -> State Int LinearRegex
    mkt t = nexts (\n -> Term (t, n))
    char :: Char -> State Int LinearRegex
    char c = mkt (C c)
    charSet cs = mkt (CS cs)

    term :: TR.Term -> State Int LinearRegex
    term (TR.Literal cs) = foldr1 Cat <$> mapM char cs
    term (TR.Symbol c) = char c
    term (TR.EOL) = error "$ anchor not supported here"
    term (TR.BOL) = error "^ anchor not supported here"
    term (TR.Any) = mkt Any
    term (TR.CClass cs) = charSet (S.fromList cs)
    term (TR.CNotClass cs) = charSet (allChars S.\\ S.fromList cs)

-- reduce :: Set (Set Char) -> (Map (Set Char) (Set Int), Map Int (Set Char))
-- reduce ss = go ss M.empty

-- capital lambda == nullable
nullable Empty = True
nullable NoMatch = False
nullable (Term _) = False
nullable (Cat x y) = nullable x && nullable y
nullable (Or x y) = nullable x || nullable y
nullable (Repeat _) = True

-- B = alphabet
alphabet :: LinearRegex -> Set LinTrans
alphabet Empty = S.empty
alphabet NoMatch = S.empty
alphabet (Term t) = transFromTerm t
alphabet (Or x y) = S.union (alphabet x) (alphabet y)
alphabet (Cat x y) = S.union (alphabet x) (alphabet y)
alphabet (Repeat x) = alphabet x

-- P = initials
initials :: LinearRegex -> Set LinTrans
initials Empty = S.empty
initials NoMatch = S.empty
initials (Term t) = transFromTerm t
initials (Or x y) = S.union (initials x) (initials y)
initials (Repeat x) = initials x
initials (Cat x y) | nullable x = S.union (initials x) (initials y)
                   | otherwise  = initials x

-- D = finals
finals :: LinearRegex -> Set LinTrans
finals Empty = S.empty
finals NoMatch = S.empty
finals (Term t) = transFromTerm t
finals (Or x y) = S.union (finals x) (finals y)
finals (Repeat x) = finals x
finals (Cat x y) | nullable y = S.union (finals x) (finals y)
                 | otherwise  = finals y

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
seams x y = cartesian (finals x) (initials y)

partition :: NFATrans -> Set LinTrans -> (Set LinTrans, Set LinTrans)
partition sym = S.partition (\(s,_) -> s == sym)

factors :: LinearRegex -> FactorMap
factors Empty = fmEmpty
factors NoMatch = fmEmpty
factors (Term _) = fmEmpty
factors (Or x y) = factors x `fmUnion` factors y
factors (Cat x y) = factors x `fmUnion` factors y `fmUnion` seams x y
factors (Repeat x) = factors x `fmUnion` seams x x

-- API?

genNFA re = NFA { nfaFinalStates = S.fromList finalStates, nfaTrans = transMap,
                  nfaNumStates = 1 + M.size stateMap }
  where
    s0 = S 0
    lre = linearize re
    d = S.toList (finals lre)
    az = S.toList (alphabet lre)
    stateMap = M.fromList (zip az (S <$> [1..]))
    get a = fromJust (M.lookup a stateMap)
    initFinalState = if nullable lre then [s0] else []
    finalStates = map get d ++ initFinalState
    transList = initTrans ++ factorsTrans
    initTrans = [(s0, fst q, get q) | q <- S.toList (initials lre)]
    factorsTrans = [(get p, fst q, get q) | (p,q) <- fmToList (factors lre)]
    transMap = tmFromList transList

-- Could be possible to do something with completely anchored regexes, where
-- there is a single BOL or EOL at the start/end of the whole pattern. In
-- particular when parsing BRE we know that's the only allowed places.
-- We can handle that outside of the "glushkov" automaton by adjusting how
-- we add searching transitions and by making all final states EOL states.
-- But: at least for start anchors that is pointless, the TNFA/TDFA mechanism
-- produces good enough matching when anchored at the start, and also handles
-- evil cases of mixing anchored and non-anchored subexpressions.

glushkovCompatible re = not (TR.hasAnchors re || TR.hasTags re)
