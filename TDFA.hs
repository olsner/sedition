{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

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

-- instance Show StateId where
--   show (S x) = 's' : show x
-- instance Show RegId where
--   show (R x) = 'r' : show x

data RegVal = Nil | Pos deriving (Show, Ord, Eq)
data RegRHS
  = SetReg RegVal -- ^ i <- nil or position
  | CopyReg RegId -- ^ i <- j
  -- Assuming for now that this is re2c-specific, we only use single-value tags.
  | CopyAppend RegId [RegVal] -- ^ i <- j <>
  deriving (Show, Ord, Eq)
type RegOp = (RegId, RegRHS)

type RegOps = [RegOp]
type TDFATrans = (TNFATrans, StateId, RegOps)

data TDFA = TDFA {
    tdfaStartState :: StateId,
    tdfaFinalStates :: Set StateId,
    tdfaFinalRegisters :: Map TagId RegId,
    tdfaFinalFunction :: Map StateId RegOps,
    tdfaTrans :: Map StateId [TDFATrans],
    tdfaTagMap :: FixedTagMap,
    tdfaTagRegMap :: Map StateId (Map TNFA.StateId (Map TagId RegId))
  }
  deriving (Show, Ord, Eq)

type Prio = TNFA.StateId
type Prec = [Prio]
-- Output or intermediate data of epsilon closure calculation
type Closure = [(Prio, Map TagId RegId, [Tag], [Tag])]
type StateClosure = [(Prio, Map TagId RegId, [Tag])]

type TDFAState = (StateClosure, Prec)

-- State for determinization process
data DetState = DetState {
  tags :: Set TagId,
  revStateMap :: Map TDFAState StateId,
  stateMap :: Map StateId TDFAState,
  transitions :: [(StateId, TDFATrans)],
  tagRHSMap :: Map (TagId,RegRHS) RegId,
  nextState :: Int,
  nextReg :: Int
    }
  deriving (Show, Ord, Eq)

initState :: TNFA -> DetState
initState tnfa = DetState {
    tags = TNFA.allTags tnfa,
    revStateMap = M.empty,
    stateMap = M.empty,
    transitions = [],
    tagRHSMap = M.empty,
    nextState = 0,
    nextReg = 0 }

type GenTDFA a = State DetState a

newStateId :: GenTDFA StateId
newStateId = gets (S . nextState) <*
    modify (\s@DetState{..} -> s { nextState = nextState + 1 })

newState :: TDFAState -> GenTDFA StateId
newState state = newStateId >>= \s -> setState s state >> return s

setState :: StateId -> (StateClosure, Prec) -> GenTDFA ()
setState k v =
    modify (\s@DetState{..} -> s {
        stateMap = M.insert k v stateMap,
        revStateMap = M.insert v k revStateMap })

getState :: StateId -> GenTDFA TDFAState
getState k = gets (fromJust . M.lookup k . stateMap)

newReg :: GenTDFA RegId
newReg = gets (R . nextReg) <*
    modify (\s@DetState{..} -> s { nextReg = nextReg + 1 })

addTagRHS :: TagId -> RegRHS -> RegId -> GenTDFA ()
addTagRHS tag rhs reg =
    modify (\s@DetState{..} -> s {
        tagRHSMap = M.insert (tag,rhs) reg tagRHSMap })

clearTagRHSMap :: GenTDFA ()
clearTagRHSMap = modify (\s -> s { tagRHSMap = M.empty })

emitTransition :: StateId -> TNFATrans -> StateId -> RegOps -> GenTDFA ()
emitTransition q t p o = do
    modify (\state@DetState{..} -> state{ transitions = (q, (t,p,o)) : transitions })

history :: [Tag] -> TagId -> [RegVal]
history []            _           = []
history (Tag t':ts)   t | t == t' = Pos : history ts t
history (UnTag t':ts) t | t == t' = Nil : history ts t
history (_:ts)        t           = history ts t

tagsInHistory :: [Tag] -> [TagId]
tagsInHistory = S.toList . S.fromList . mapMaybe tag
  where
    tag (Tag t) = Just t
    tag (UnTag t) = Just t
    tag _ = Nothing

precedence :: Closure -> Prec
precedence = map (\(q,_,_,_) -> q)

stateClosure :: Closure -> StateClosure
stateClosure = map (\(q,r,_,l) -> (q,r,l))

stateRegMap :: TDFAState -> Map TNFA.StateId (Map TagId RegId)
stateRegMap (xs,_) = M.fromList . map (\(q,r,_) -> (q,r)) $ xs

tdfaState :: Closure -> TDFAState
tdfaState clos = (stateClosure clos, precedence clos)

regop_rhs :: Map TagId RegId -> [RegVal] -> TagId -> RegRHS
regop_rhs r ht t | isMultiValueTag t = CopyAppend (fromJust $ M.lookup t r) ht
regop_rhs _ ht t = trace (show ht ++ " " ++ show t ++ " <- " ++ show (last ht)) $
    SetReg (last ht)

isMultiValueTag :: TagId -> Bool
isMultiValueTag _ = False

findState :: (StateClosure, Prec) -> GenTDFA (Maybe StateId)
findState statePrec = gets (M.lookup statePrec . revStateMap)

mapState :: TDFAState -> TDFAState -> Maybe RegOps
mapState (s,_) (s',_) | s == s'   = Just []
                       | otherwise = Nothing

-- 1. Find exact match and return existing state id
-- 2. Look through all states to find mappable state
-- 3. Create new state
addState :: Closure -> RegOps -> GenTDFA (StateId, RegOps)
addState closure ops = do
     prev <- findState state
     case prev of
       Just p -> return (p, ops)
       Nothing -> do
         -- TODO Find a state that can be mapped and reuse it
         -- I think this is "optional", rather just results in adding more
         -- states than necessary. (Perhaps *many* more than necessary for
         -- complicated regexps...)
         -- states <- gets (M.toList . stateMap)
         addNewState state ops
  where
    state = tdfaState closure

addNewState :: TDFAState -> RegOps -> GenTDFA (StateId, RegOps)
addNewState state ops = do
    s <- newState state
    return (s, ops)

symbolTrans :: TNFATrans -> Bool
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
                             | otherwise = s : go seen xs
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


newRegForEachTag :: GenTDFA (Map TagId RegId)
newRegForEachTag = do
    ts <- gets (S.toList . tags)
    M.fromList <$> mapM (\t -> (t,) <$> newReg) ts

generateInitialState :: TNFA.StateId -> GenTDFA Closure
generateInitialState q0 = do
  regs <- newRegForEachTag
  return [(q0, regs, [], [])]

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> mapM f xs

visitStates :: TNFA -> [StateId] -> GenTDFA ()
visitStates tnfa [] = return ()
visitStates tnfa ss = do
  newStates <- concatMapM (visitState tnfa) ss
  visitStates tnfa newStates

nextSymbols :: TNFA -> Set TNFA.StateId -> [TNFATrans]
nextSymbols TNFA{..} s = [t | (q,t,p) <- tnfaTrans, S.member q s]

transitionRegRHSes :: Closure -> [(TagId, RegRHS)]
transitionRegRHSes = S.toList . S.fromList . concatMap stateRegOps
  where stateRegOps (q,r,h,l) =
          map (\t -> (t, regop_rhs r (history h t) t)) (tagsInHistory h)

updateTagMap :: Closure -> GenTDFA Closure
updateTagMap = mapM $ \(q,r,h,l) -> do
    let o = map (\t -> (t, regop_rhs r (history h t) t)) (tagsInHistory h)
    r' <- forM o $ \(t,rhs) -> gets ((t,) <$> fromJust . M.lookup (t,rhs) . tagRHSMap)
    return (q,M.fromList r',h,l)

assignReg :: (TagId, RegRHS) -> GenTDFA (Maybe RegOp)
assignReg (tag, rhs) = do
  existingReg <- gets (M.lookup (tag, rhs) . tagRHSMap)
  case existingReg of
    Just r -> return Nothing
    Nothing -> do
      r <- newReg
      addTagRHS tag rhs r
      return (Just (r, rhs))

visitState :: TNFA -> StateId -> GenTDFA [StateId]
visitState tnfa s = do
    (clos, prec) <- getState s
    prevStates <- gets (M.keysSet . stateMap)
    let as = nextSymbols tnfa (S.fromList [s | (s,_,_) <- clos])
    ss <- forM as $ \a -> do
        let b = stepOnSymbol tnfa prec a clos
        let c = epsilonClosure False tnfa b
        let rhses = transitionRegRHSes c
        o <- catMaybes <$> mapM assignReg rhses
        c' <- updateTagMap c
        (s',o) <- addState c o
        emitTransition s a s' o
        return s'
    clearTagRHSMap
    return [s | s <- ss, not (S.member s prevStates)]

sortByPrec :: Prec -> StateClosure -> StateClosure
sortByPrec prec = sortOn (\(x,_,_) -> x `elemIndex` prec)

stepOnSymbol :: TNFA -> Prec -> TNFATrans -> StateClosure -> Closure
stepOnSymbol TNFA{..} prec t clos = go (sortByPrec prec clos)
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
  tagRegMap <- gets (M.map stateRegMap . stateMap)
  return (TDFA {
    tdfaStartState = s0,
    -- TODO All TDFA states where the contained TNFA states include the
    -- tnfa final state.
    tdfaFinalStates = S.empty,
    tdfaFinalRegisters = finRegs,
    -- Related to final state calculation, collect the finalRegOps for each
    -- final state.
    tdfaFinalFunction = M.empty,
    tdfaTrans = multiMapFromList ts,
    tdfaTagMap = tnfaTagMap,
    tdfaTagRegMap = tagRegMap
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
            showState s <> showTrans s <> showTagMap s <>
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

    getTagRegMap s = M.toList $ fromJust $ M.lookup s tdfaTagRegMap
    showTagMap s = "  Regs:" <> showPrefix "\n   " (getTagRegMap s) <> "\n"
    showPrefix prefix xs = concat [ prefix ++ show x | x <- xs ]

    getTrans :: StateId -> [TDFATrans]
    getTrans s = fromMaybe [] (M.lookup s tdfaTrans)

    isFinalState s = s `S.member` tdfaFinalStates

testTDFA :: String -> IO ()
testTDFA = putStr . prettyStates . genTDFA . genTNFA . testTagRegex
