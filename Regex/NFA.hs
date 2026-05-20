{-# LANGUAGE RecordWildCards,RecursiveDo #-}

-- NFA construction from regular expressions:
-- https://en.wikipedia.org/wiki/Glushkov%27s_construction_algorithm
--
-- Accepts a "tagged regex" (for convenience versus the rest of the compiler)
-- but does not allow any tags to be used.

module Regex.NFA where

import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

-- import Debug.Trace

import qualified Regex.TaggedRegex as TR
import Regex.TNFA (StateId(..))

-- Term or something?
data NFATrans
  = C Char
  | Any
  | EOL
  deriving (Show, Ord, Eq)

type LinTrans = (NFATrans, Int)

data LinearRegex
  = Empty
  | NoMatch
  | CS (Set LinTrans)
  | Term LinTrans
  | Cat LinearRegex LinearRegex
  | Or LinearRegex LinearRegex
  | Repeat Int (Maybe Int) LinearRegex
  deriving (Show, Ord, Eq)

allChars = S.fromList ['\000'..'\255']

transFromTerm t = S.singleton t

type TransMap k = Map StateId (Map k (Set StateId))
-- tmUnion :: Ord k => TransMap k -> TransMap k -> TransMap k
-- tmUnion = M.unionWith (M.unionWith S.union)
tmFromList :: Ord k => [(StateId, k, StateId)] -> TransMap k
tmFromList [] = M.empty
tmFromList ((k1,k2,v):xs) = M.insertWith (M.unionWith S.union) k1 (M.singleton k2 (S.singleton v)) (tmFromList xs)

data NFA = NFA
  { nfaFinalStates :: Set StateId
  -- nfaStartStateNotBOL :: StateId
  -- , nfaFinalStatesEOL :: Set StateId
  , nfaTrans :: TransMap NFATrans
  , nfaNumStates :: Int
  } deriving (Show, Ord, Eq)
nfaStartState = S 0

-- TODO Handle anchors properly.
-- Since this will be used for untagged does-match queries, we know we are at
-- BOL in the original starting state and (probably) don't do repeat searches,
-- maybe we can process that during linearization and insert a .* before
-- initial states that are not anchored?
--
-- consider weird cases like (b|)(^|f)($|q)(z|)
-- and ^^^foo$$$ which should match foo
--
-- May be easier to deal with after we have constructed the NFA, but ideally
-- we would not have BOL/EOL at all present in the output type. Also somewhat
-- annoying to use an intermediate state machine type.
-- maybe: as long as the starting state has an outgoing BOL transition, remove
-- it and merge all of the target state's transitions with the starting state's.
-- For anchors at the end, find states that should accept at EOL and add them
-- to a separate set of EOL-final states.

-- Define NFA simulation for matching:
-- 1. Matching always starts at the beginning of the line, state set only
--    includes the starting state.
-- 2. Iterate through string and resolve outgoing states (Char -> Set StateId)
-- 3. If we ever reach a normal final state, return successful match
-- 4. When reaching the end of the string, look at the EOL-final state set

-- TODO Instead of char+number, replace the alphabet and add a map from index
-- to real symbol/character. Then look into alphabet reduction and e.g. map
-- indices to disjoint sets of symbols.
--
-- Reang
linearize :: TR.TaggedRegex -> LinearRegex
linearize re = evalState (go (TR.reanchor re)) 0
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
    charSet cs = nexts (\n -> CS (S.map (\c -> (C c, n)) cs))

    term :: TR.Term -> State Int LinearRegex
    term (TR.Literal cs) = foldr1 Cat <$> mapM char cs
    term (TR.Symbol c) = char c
    term (TR.EOL) = mkt EOL
    term (TR.BOL) = error "^ anchor left in regex"
    term (TR.Any) = mkt Any
    term (TR.CClass cs) = charSet (S.fromList cs)
    term (TR.CNotClass cs) = charSet (allChars S.\\ S.fromList cs)

-- capital lambda == nullable
nullable Empty = True
nullable NoMatch = False
nullable (Term (EOL,_)) = True
nullable (Term _) = False
nullable (CS _) = False
nullable (Cat x y) = nullable x && nullable y
nullable (Or x y) = nullable x || nullable y
nullable (Repeat n _ x) = n == 0 || nullable x

-- B = alphabet
alphabet :: LinearRegex -> Set LinTrans
alphabet Empty = S.empty
alphabet NoMatch = S.empty
alphabet (Term t) = transFromTerm t
alphabet (CS s) = s
alphabet (Or x y) = S.union (alphabet x) (alphabet y)
alphabet (Cat x y) = S.union (alphabet x) (alphabet y)
alphabet (Repeat _ _ x) = alphabet x

-- P = initials
initials :: LinearRegex -> Set LinTrans
initials Empty = S.empty
initials NoMatch = S.empty
initials (Term t) = transFromTerm t
initials (CS s) = s
initials (Cat x y) | nullable x = S.union (initials x) (initials y)
                   | otherwise  = initials x
initials (Or x y) = S.union (initials x) (initials y)
initials (Repeat _ _ x) = initials x

-- D = finals
finals :: LinearRegex -> Set LinTrans
finals Empty = S.empty
finals NoMatch = S.empty
finals (CS s) = s
finals (Term t) = transFromTerm t
finals (Or x y) = S.union (finals x) (finals y)
finals (Cat x y) | nullable y = S.union (finals x) (finals y)
                 | otherwise  = finals y
finals (Repeat _ _ x) = finals x

-- F = factors
type FactorMap = Map LinTrans (Set LinTrans)
fmEmpty = M.empty
fmUnion = M.unionWith S.union
fmToList :: FactorMap -> [(LinTrans,LinTrans)]
fmToList = concatMap (\(x,ys) -> [(x,y) | y <- S.toList ys]) . M.toList

cartesian :: Set LinTrans -> Set LinTrans -> FactorMap
cartesian x y = M.fromSet (const y) x
seams x y = cartesian (finals x) (initials y)

factors :: LinearRegex -> FactorMap
factors Empty = fmEmpty
factors NoMatch = fmEmpty
factors (Term _) = fmEmpty
factors (CS _) = fmEmpty
factors (Or x y) = factors x `fmUnion` factors y
factors (Cat x y) = factors x `fmUnion` factors y `fmUnion` seams x y
factors (Repeat _ _ x) = factors x `fmUnion` seams x x

-- API?

genNFA re = NFA { nfaFinalStates = S.fromList finalStates,
                  nfaTrans = transMap,
                  nfaNumStates = 1 + M.size stateMap }
  where
    s0 = S 0
    lre = linearize re
    d = S.toList (finals lre)
    az = S.toList (alphabet lre)
    stateMap = M.fromList (zip az (S <$> [1..]))
    get a = fromJust (M.lookup a stateMap)
    initFinalState | nullable lre = [s0]
                   | otherwise    = []
    finalStates = map get d ++ initFinalState
    transList = initTrans ++ factorsTrans
    initTrans = [(s0, fst q, get q) | q <- S.toList (initials lre)]
    factorsTrans = [(get p, fst q, get q) | (p,q) <- fmToList (factors lre)]
    transMap = tmFromList transList

simulateNFA :: NFA -> String -> (Bool, [String])
simulateNFA NFA{..} xs = runWriter (go (S.singleton nfaStartState) xs)
  where
    intersects x y = not (S.null (x `S.intersection` y))
    hasFinalState s = s `intersects` nfaFinalStates
    go s []     | hasFinalState s = logFinal s "EOL -> MATCH: final" >> return True
                -- | hasFinalStateEOL s = logFinal s "EOL" >> logFinal s "MATCH: EOL-final" >> return True
                | otherwise       = logFinal s "EOL -> NO MATCH" >> return False
    go s (x:xs) | hasFinalState s = logFinal s "MATCH: final state" >> return True
                | S.null s        = tell ["NO MATCH"] >> return False
                -- Special case only for prettier printouts.
                | S.null s'       = logTrans s x s' >> return False
                | otherwise       = logTrans s x s' >> go s' xs
                where s' = closeAll x s
    closeAll x ss = S.unions (map (close x) (S.toList ss))
    close :: Char -> StateId -> Set StateId
    close x s = findTrans x (M.findWithDefault M.empty s nfaTrans)
    findTrans x m = S.unions [exact, any]
      where
        exact = M.findWithDefault S.empty (C x) m
        any = M.findWithDefault S.empty Any m
    logTrans s x s' | S.null s' = tell [showStates s ++ " -> " ++ show x ++ " -> NO MATCH"]
                    | otherwise = tell [showStates s ++ " -> " ++ show x ++ " -> " ++ showStates s']
    logFinal s msg  = tell [showStates s ++ " -> " ++ msg]
    showStates = unwords . map show . S.toList

-- Test functions

nfaStates :: NFA -> [StateId]
nfaStates nfa = map S [0..nfaNumStates nfa - 1]

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
    showT EOL = " $ "
    showT Any = " . "
    showT (C c) = show c

removeTags = TR.selectTags (const False)

testLinearize :: String -> LinearRegex
testLinearize = linearize . removeTags . TR.testParseTagRegex

testNFA :: String -> IO ()
testNFA = putStr . prettyStates . genNFA . removeTags . TR.testParseTagRegex

testSimulate :: String -> String -> IO ()
testSimulate re s = putStr (prettyStates nfa) >> mapM_ putStrLn log >> print result
  where (result, log) = simulateNFA nfa s
        nfa = genNFA (removeTags (TR.testParseTagRegex re))

exampleRE = "(a(ab)*)*|(ba)*"
