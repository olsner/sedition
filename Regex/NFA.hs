{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances #-}

-- NFA construction from regular expressions:
-- https://en.wikipedia.org/wiki/Glushkov%27s_construction_algorithm
--
-- Accepts a "tagged regex" (for convenience versus the rest of the compiler)
-- but does not allow any tags to be used.

module Regex.NFA where

import Control.Monad
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer

import Data.Array.Unboxed
import Data.Array.ST
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Word

import Debug.Trace

import qualified Regex.TaggedRegex as TR
import Regex.TNFA (StateId(..))

-- Term or something?
data NFATrans
  = BOL
  | C Char
  | CS (Set Char)
  | Any
  | EOL
  deriving (Show, Ord, Eq)

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

-- capital lambda == nullable
nullable Empty = True
nullable NoMatch = False
nullable (Term (BOL,_)) = True
nullable (Term (EOL,_)) = True
nullable (Term _) = False
nullable (Cat x y) = nullable x && nullable y
nullable (Or x y) = nullable x || nullable y
nullable (Repeat n _ x) = n == 0 || nullable x

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
initials (Cat x y) | nullable x = S.union (initials x) (initials y)
                   | otherwise  = initials x
initials (Or x y) = S.union (initials x) (initials y)
initials (Repeat _ _ x) = initials x

-- D = finals
finals :: LinearRegex -> Set LinTrans
finals Empty = S.empty
finals NoMatch = S.empty
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
fmCart x y | S.null y = M.empty
           | otherwise = M.fromSet (const y) x

cartesian :: Set LinTrans -> Set LinTrans -> FactorMap
--cartesian x y = M.fromSet (const y) x
cartesian x y = fmCart x' y' `fmUnion` fmCart ybol xeol `fmUnion` fmCart x' ybol `fmUnion` fmCart xeol y'
  where (xeol, x') = partition EOL x
        (ybol, y') = partition BOL y
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

mapKeysMaybe :: (Ord k, Ord l) => (k -> Maybe l) -> Map k a -> Map l a
mapKeysMaybe f = M.fromList . mapMaybe g . M.toList
  where g (k,v) = case f k of Just k' -> Just (k', v)
                              Nothing -> Nothing

invertMap :: (Ord k, Ord v) => Map k (Set v) -> Map v (Set k)
invertMap m = M.unionsWith S.union [M.fromSet (const (S.singleton k)) vs | (k,vs) <- M.toList m]

compact NFA{..} = NFA {
    nfaFinalStates = mapStateSet nfaFinalStates,
    nfaFinalStatesEOL = mapStateSet nfaFinalStatesEOL,
    nfaTrans = mapStateTM nfaTrans,
    nfaNumStates = M.size stateMap }
  where
    s0 = nfaStartState
    -- Don't care about the symbols/characters for these, just reachability
    backwards = M.map S.toList (invertMap (tmReach nfaTrans))
    -- Keep any states that has edges going into a final state
    kept = close S.empty (S.toList (S.union nfaFinalStates nfaFinalStatesEOL))
    close done [] = done
    close done (x:xs) | x `S.member` done = close done xs
                      | otherwise = close (S.insert x done) (xs ++ M.findWithDefault [] x backwards)
    stateMap | not (s0 `S.member` kept) = trace "s0 not reachable - will always fail" M.empty
             | otherwise = M.fromList (zip (S.toList kept) (S <$> [0..]))

    mapState s = M.lookup s stateMap
    mapStateSet = S.fromList . mapMaybe mapState . S.toList
    mapStateTM = mapKeysMaybe mapState . M.map (M.map mapStateSet)

addEOLState nfa@NFA{..} = nfa { nfaFinalStatesEOL = eolFinalStates,
                                nfaTrans = removeEOLTrans nfaTrans }
  where
    -- Find all final states that have incoming transitions on EOL, add the
    -- source states to eolFinalStates
    allEOLTrans :: Map StateId (Set StateId)
    allEOLTrans = M.filter (not . S.null) . M.map (S.intersection nfaFinalStates . M.findWithDefault S.empty EOL) $ nfaTrans

    removeEOLTrans = M.map (M.delete EOL)

    eolFinalStates = M.keysSet allEOLTrans

searchNFA nfa@NFA{..} = nfa { nfaFinalStates = nfaFinalStates,
                              nfaTrans = updatedTransMap,
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

genNFA re = compact . addEOLState . searchNFA $
    NFA { nfaFinalStates = S.fromList finalStates,
          -- At this stage we still have explicit EOL transitions
          nfaFinalStatesEOL = S.empty,
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

-- Stuff

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
bitwiseNFA nfa@NFA{..} | nfaNumStates > finiteBitSize commonB = Nothing
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

-- Test functions

nfaStates :: NFA -> [StateId]
nfaStates nfa = map S [0..nfaNumStates nfa - 1]

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

removeTags = TR.selectTags (const False)

testLinearize :: String -> LinearRegex
testLinearize = linearize . removeTags . TR.testParseTagRegex

testNFA :: String -> IO ()
testNFA = putStr . prettyStates . genNFA . removeTags . TR.testParseTagRegex

testBitwise :: String -> IO ()
testBitwise = print . bitwiseNFA . genNFA . removeTags . TR.testParseTagRegex

testSimulate :: String -> String -> IO ()
testSimulate re s = putStr (prettyStates nfa) >> mapM_ putStrLn log >> print result
  where (result, log) = simulateNFA nfa s
        nfa = genNFA (removeTags (TR.testParseTagRegex re))

exampleRE = "(a(ab)*)*|(ba)*"
