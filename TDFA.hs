{-# LANGUAGE RecordWildCards #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Determinization, convert a TNFA to a TDFA state machine.

module TDFA where

import Control.Monad.Trans.State.Strict
import Control.Monad

-- import Data.ByteString.Char8 (ByteString)
-- import qualified Data.ByteString.Char8 as C
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import TaggedRegex hiding (Prio)
import TNFA (genTNFA, TNFA(..))
import qualified TNFA

newtype StateId = S Int deriving (Show, Ord, Eq)
newtype RegId = R Int deriving (Show, Ord, Eq)
data RegVal = Nil | Pos deriving (Show, Ord, Eq)
data RegOp
  = SetReg RegId RegVal -- ^ Set register to nil or current position
  | CopyReg RegId RegId -- ^ CopyReg i j => i <- j
  -- Assuming for now that this is re2c-specific, we only use single-value tags.
  -- | CopyAppend RegId [RegVal] -- ^ i <- j <> h
  deriving (Show, Ord, Eq)

type RegOps = [RegOp]
type TDFATrans = (TNFATrans, StateId, RegOps)

data TDFA = TDFA {
    tdfaStartState :: StateId,
    tdfaFinalStates :: Set StateId,
    tdfaFinalRegisters :: Map TagId RegId,
    tdfaFinalFunction :: Map StateId RegOps,
    tdfaTrans :: Map StateId [TDFATrans],
    tdfaTagMap :: FixedTagMap
  }
  deriving (Show, Ord, Eq)

type Prio = TNFA.StateId
type Prec = [Prio]
-- Output or intermediate data of epsilon closure calculation
type Closure = [(Prio, Map TagId RegId, [Tag], [Tag])]
type StateClosure = [(Prio, Map TagId RegId, [Tag])]

data DetState = DetState {
  maxTag :: Int,
  revStateMap :: Map (StateClosure, Prec) StateId,
  stateMap :: Map StateId (StateClosure, Prec),
  -- stateList :: [([(Prio,Map TagId RegId,[Tag])],Prec,StateId)],
  transitions :: [(StateId, TDFATrans)],
  nextState :: Int,
  nextReg :: Int
    }
  deriving (Show, Ord, Eq)

initState :: TNFA -> DetState
initState tnfa = DetState {
    maxTag = TNFA.maxTag tnfa,
    revStateMap = M.empty,
    stateMap = M.empty,
    nextState = 0, nextReg = 0, transitions = [] }

type GenTDFA a = State DetState a

newState :: GenTDFA StateId
newState = gets (S . nextState) <*
    modify (\s@DetState{..} -> s { nextState = nextState + 1 })

setState :: StateId -> (StateClosure, Prec) -> GenTDFA ()
setState k v =
    modify (\s@DetState{..} -> s {
        stateMap = M.insert k v stateMap,
        revStateMap = M.insert v k revStateMap })

getState :: StateId -> GenTDFA (StateClosure, Prec)
getState k = gets (fromJust . M.lookup k . stateMap)

newReg :: GenTDFA RegId
newReg = gets (R . nextReg) <*
    modify (\s@DetState{..} -> s { nextReg = nextReg + 1 })

emitTransition :: StateId -> TNFATrans -> StateId -> RegOps -> GenTDFA ()
emitTransition q t p o = do
    modify (\state@DetState{..} -> state{ transitions = (q, (t,p,o)) : transitions })

history :: [Tag] -> TagId -> [RegVal]
history []            _           = []
history (Tag t':ts)   t | t == t' = Pos : history ts t
history (UnTag t':ts) t | t == t' = Nil : history ts t
history (_:ts)        t           = history ts t

precedence :: Closure -> Prec
precedence = map (\(q,_,_,_) -> q)

stateClosure :: Closure -> StateClosure
stateClosure = map (\(q,s,_,l) -> (q,s,l))

-- Note: more complicated with support for multi-valued tags
regop_rhs :: Map TagId RegId -> [Tag] -> TagId -> [Tag]
-- regop_rhs r ht t | isMultiValuedTag t = M.lookup t r : ht
regop_rhs _ ht _ = [last ht]

findState :: Closure -> GenTDFA (Maybe StateId)
findState closure = gets (M.lookup (stateClosure closure, precedence closure) . revStateMap)

-- mapState :: StateClosure -> StateClosure -> Maybe RegOps
-- mapState s s' = 

addState :: Closure -> RegOps -> GenTDFA (StateId, RegOps)
addState closure ops = do
     s <- newState
     setState s (stateClosure closure, prec)
     return (s, ops)
  where
    prec = precedence closure

symbolTrans (Eps _ _) = False
symbolTrans BOL = False
-- TODO Handle end-of-line. Something like a final state that is only accepting
-- at the end of the line. (This would also not need fallbacks, since it
-- should have no outgoing edges. Except we do need to handle register setting.)
symbolTrans EOL = False
symbolTrans _ = True

-- TODO Accept starting-state flag (beginning of line), only include BOL
-- transitions if that is set.
-- BUT: This also requires that we include the states for an unmatched prefix
-- of an unanchored regular expression. A sed-specific trait is that we only
-- ever use "find", not "match" (which would have different behavior here).
-- EOL is different.
epsilonClosure :: Bool -> TNFA -> Closure -> Closure
epsilonClosure bol TNFA{..} = possibleStates . go S.empty
  where
    go :: Set TNFA.StateId -> Closure -> Closure
    go _ [] = []
    go seen (s@(q,r,h,l):xs) | not (q `S.member` seen) = s : go seen' (ys ++ xs)
                             | otherwise = go seen xs
      where
        seen' = S.insert q seen
        epst = sort [(prio,t,p) | (s,Eps prio t,p) <- tnfaTrans, s == q]
        ys = [ (p,r,h,l ++ [t]) | (_,t,p) <- epst,
                                   not (S.member p seen') ]
             ++ [ (p,r,h,l) | p <- anchors, not (S.member p seen') ]
        eol = False -- Should this really be handled here?
        anchors = [p | eol, (s,EOL,p) <- tnfaTrans, s == q] ++
                  [p | bol, (s,BOL,p) <- tnfaTrans, s == q]
    fin = tnfaFinalState
    possibleStates c = [y | y@(q,_,_,_) <- c, q == fin || possibleState q]
    possibleState q = or [symbolTrans t | (s,t,_) <- tnfaTrans, s == q]


newRegForEachTag = do
  maxTag <- gets maxTag
  regs <- replicateM (maxTag + 1) newReg
  return (M.fromList (zip [0..maxTag] regs))

generateInitialState q0 = do
  regs <- newRegForEachTag
  return [(q0, regs, [], [])]

concatMapM f xs = concat <$> mapM f xs

visitStates :: TNFA -> [StateId] -> GenTDFA ()
visitStates tnfa [] = return ()
visitStates tnfa ss = do
  newStates <- concatMapM (visitState tnfa) ss
  visitStates tnfa newStates

nextSymbols :: TNFA -> Set TNFA.StateId -> [TNFATrans]
nextSymbols TNFA{..} s = [t | (q,t,p) <- tnfaTrans, S.member q s]

visitState tnfa s = do
    (clos, prec) <- getState s
    prevStates <- gets (M.keysSet . stateMap)
    let as = nextSymbols tnfa (S.fromList [s | (s,_,_) <- clos])
    ss <- forM as $ \a -> do
        let b = stepOnSymbol tnfa prec a clos
        let c = epsilonClosure False tnfa b
        -- v is a map from tag and RHS to register, to deduplicate registers
        -- that will have the same value.
        --o <- transitionRegOps c {- r? -} v
        let o = []
        (s',o) <- addState c o
        emitTransition s a s' o
        return s'
    return [s | s <- ss, not (S.member s prevStates)]

sortByPrec :: Prec -> StateClosure -> StateClosure
sortByPrec prec = sortOn (\(x,_,_) -> x `elemIndex` prec)

stepOnSymbol :: TNFA -> Prec -> TNFATrans -> StateClosure -> Closure
stepOnSymbol tnfa@TNFA{..} prec t clos = go (sortByPrec prec clos)
  where
    go [] = []
    go ((q,r,l):xs) | Just p <- getTransition q t = (p,r,l,[]) : go xs
                      | otherwise = go xs
    getTransition q t
        | Just (_,_,p) <- find (isTransition q t) tnfaTrans = Just p
        | otherwise = Nothing
    isTransition q t (q', t', p) = q == q' && t == t'

determinize :: TNFA -> GenTDFA TDFA
determinize tnfa@TNFA{..} = do
  state0 <- generateInitialState tnfaStartState
  finRegs <- newRegForEachTag
  let c0 = epsilonClosure True tnfa state0
  (s0, _) <- addState c0 []
  visitStates tnfa [s0]
  ts <- gets transitions
  return (TDFA {
    tdfaStartState = s0,
    -- TODO All TDFA states where the contained TNFA states include the
    -- tnfa final state.
    tdfaFinalStates = S.empty,
    tdfaFinalRegisters = finRegs,
    tdfaFinalFunction = M.empty,
    tdfaTrans = multiMapFromList ts,
    tdfaTagMap = tnfaTagMap
    })

multiMapFromList :: Ord a => [(a,b)] -> Map a [b]
multiMapFromList ts = foldr prepend M.empty ts
  where
    prepend (s,t) m = M.insert s (t : M.findWithDefault [] s m) m


genTDFA :: TNFA -> TDFA
genTDFA tnfa = evalState (determinize tnfa) (initState tnfa)

prettyStates :: TDFA -> String
prettyStates TDFA{..} = go S.empty [tdfaStartState] <> fixedTags <> "\n"
  where
    go seen (s:ss)
        | not (S.member s seen) =
            showState s <> showTrans s <>
            go (S.insert s seen) (ss ++ nextStates s)
        | otherwise = go seen ss
    go seen [] = []
    nextStates s =  [t | (_,t,_) <- getTrans s]
    showState s | s == tdfaStartState = "START " ++ show s ++ ":\n"
    showState s | isFinalState s = "FINAL " ++ show s ++ ":\n"
    showState s = "State " ++ show s ++ ":\n"
    showTrans s = concat [ "  " ++ show t ++ " => " ++ show s' ++
                            " | " ++ regOps o ++ "\n"
                           | (t,s',o) <- getTrans s ]
    fixedTags | M.null tdfaTagMap = "(No fixed tags)"
              | otherwise = "Fixed tags:\n" ++
        concat [ "  t" ++ show t ++ " <- " ++ show ft ++ "\n"
                 | (t,ft) <- M.toList tdfaTagMap ]

    regOps ops = intercalate "; " (map show ops)

    getTrans :: StateId -> [TDFATrans]
    getTrans s = fromMaybe [] (M.lookup s tdfaTrans)

    isFinalState s = s `S.member` tdfaFinalStates

testTDFA :: String -> IO ()
testTDFA = putStr . prettyStates . genTDFA . genTNFA . testTagRegex
