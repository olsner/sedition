{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Determinization, convert a TNFA to a TDFA state machine.

module TDFA where

import Control.Monad.Trans.State.Strict
import Control.Monad

-- import Data.ByteString.Char8 (ByteString)
-- import qualified Data.ByteString.Char8 as C
import Data.List (elemIndex, find, intercalate, nub, sort, sortOn)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

-- import Debug.Trace

import qualified CharMap as CM
import CharMap (CharMap)
import TaggedRegex hiding (Prio)
import TNFA (genTNFA, TNFA(..))
import qualified TNFA
import SimulateTNFA (matchTerm)

newtype StateId = S Int deriving (Ord, Eq)
newtype RegId = R Int deriving (Ord, Eq)

instance Show StateId where
  show (S x) = 's' : show x
instance Show RegId where
  show (R x) = 'r' : show x

data RegVal = Nil | Pos deriving (Show, Ord, Eq)
data RegRHS
  = SetReg RegVal -- ^ i <- nil or position
  | CopyReg RegId -- ^ i <- j
  deriving (Ord, Eq)
instance Show RegRHS where
  show (SetReg rv) = show rv
  show (CopyReg r) = show r
type RegOp = (RegId, RegRHS)

type RegOps = [RegOp]
type TDFATrans = (StateId, RegOps)
type TDFATransTable = CharMap TDFATrans

data TDFA = TDFA {
    tdfaStartState :: StateId,
    tdfaStartStateNotBOL :: StateId,
    tdfaFinalStates :: Set StateId,
    tdfaFinalRegisters :: Map TagId RegId,
    tdfaFinalFunction :: Map StateId RegOps,
    tdfaTrans :: Map StateId TDFATransTable,
    tdfaFixedTags :: FixedTagMap,
    -- For debugging (mostly)
    tdfaTagRegMap :: Map StateId (Map TNFA.StateId (Map TagId RegId)),
    tdfaStateMap :: Map StateId (Set TNFA.StateId),
    tdfaOriginalFinalState :: TNFA.StateId
  }
  deriving (Show, Ord, Eq)

type Prio = TNFA.StateId
type Prec = [Prio]
-- Output or intermediate data of epsilon closure calculation
type Closure = [(Prio, Map TagId RegId, History, History)]
type StateClosure = [(Prio, Map TagId RegId, History)]

type TDFAState = (StateClosure, Prec)

-- State for determinization process
data DetState = DetState {
  tags :: Set TagId,
  revStateMap :: Map TDFAState StateId,
  stateMap :: Map StateId TDFAState,
  transitions :: [(StateId, (Char, (StateId, RegOps)))],
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

emitTransition :: StateId -> Char -> StateId -> RegOps -> GenTDFA ()
emitTransition q c p o = do
    modify (\state@DetState{..} -> state{ transitions = (q, (c, (p,o))) : transitions })

type History = Map TagId RegVal

emptyHistory = M.empty

history :: History -> TagId -> [RegVal]
history hs t | Just rv <- M.lookup t hs = [rv]
             | otherwise                = []

tagsInHistory :: History -> [TagId]
tagsInHistory = M.keys

appendHistory :: History -> Tag -> History
appendHistory h (Tag t) = M.insert t Pos h
appendHistory h (UnTag t) = M.insert t Nil h
appendHistory h NoTag = h

precedence :: Closure -> Prec
precedence = map (\(q,_,_,_) -> q)

stateClosure :: Closure -> StateClosure
stateClosure = map (\(q,r,_,l) -> (q,r,l))

stateRegMap :: TDFAState -> Map TNFA.StateId (Map TagId RegId)
stateRegMap = M.fromList . map (\(q,r,_) -> (q,r)) . fst
stateStateIds :: TDFAState -> Set TNFA.StateId
stateStateIds = S.fromList . map (\(q,_,_) -> q) . fst

tdfaState :: Closure -> TDFAState
tdfaState clos = (stateClosure clos, precedence clos)

regop_rhs :: History -> TagId -> RegRHS
regop_rhs h t = SetReg (last (history h t))

findState :: TDFAState -> GenTDFA (Maybe StateId)
findState statePrec = gets (M.lookup statePrec . revStateMap)

-- First check if the states are compatible:
-- 1. same subset of TNFA states
-- 2. same precedence
-- 3. no "different lookahead tags for some TNFA state"? whatever that means,
--    perhaps that destination states for all outgoing transitions are the same
--
-- Then try to map registers and return new register operations.
mapState :: TDFAState -> TDFAState -> RegOps -> Maybe RegOps
mapState _ _ _ = Nothing
-- mapState (s,p) (s',p') ops = Nothing

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
         -- Actually does not seem to be optional after all, the example tagged
         -- regexp from the TDFA paper generates infinite states.
         -- states <- gets (M.toList . stateMap)
         addNewState state ops
  where
    state = tdfaState closure

-- Mainly to prevent runaway
maxStates = 10000

addNewState :: TDFAState -> RegOps -> GenTDFA (StateId, RegOps)
addNewState state ops = do
    ns <- gets (M.size . stateMap)
    when (ns > maxStates) $ error "Too many states, giving up"
    s <- newState state
    -- trace ("new state " ++ show s ++ ": " ++ show state ++ " " ++ show ops) $ return ()
    return (s, ops)

symbolTrans :: TNFATrans -> Bool
symbolTrans (Eps _ _) = False
symbolTrans BOL = False
-- TODO Handle end-of-line. Something like a final state that is only accepting
-- at the end of the line. (This would also not need fallbacks, since it
-- should have no outgoing edges. Except we do need to handle register setting.)
-- Treating EOL as a character will probably lead to loops when actually
-- matching on them using a TDFA? This is rather just to see how things work.
-- Probably need to understand the stuff like fallback transitions first. The
-- "normal" way is rather for every final state to implicitly only be accepting
-- when having reached the end of the string.
symbolTrans EOL = True
symbolTrans _ = True

epsilonClosure :: Bool -> TNFA -> Closure -> Closure
epsilonClosure bol TNFA{..} = possibleStates . go S.empty
  where
    go :: Set TNFA.StateId -> Closure -> Closure
    go _ [] = []
    go seen (s@(q,r,h,l):xs) = s : go seen' (reverse ys ++ xs)
      where
        seen' = S.insert q seen
        epst = sort [(prio,t,p) | (s,Eps prio t,p) <- tnfaTrans, s == q]
        ys = [ (p,r,h,appendHistory l t) | (_,t,p) <- epst,
                                           not (S.member p seen') ]
             ++ [ (p,r,h,l) | p <- anchors, not (S.member p seen') ]
        eol = False -- Should this really be handled here?
        anchors = [p | eol, (s,EOL,p) <- tnfaTrans, s == q] ++
                  [p | bol, (s,BOL,p) <- tnfaTrans, s == q]
    fin = tnfaFinalState
    possibleStates c = [y | y@(q,_,_,_) <- c, q == fin || possibleState q]
    possibleState q = or [symbolTrans t | (s,t,_) <- tnfaTrans, s == q]


forEachTag :: (TagId -> GenTDFA a) -> GenTDFA [a]
forEachTag f = do
    ts <- gets (S.toList . tags)
    mapM f ts

newRegForEachTag :: GenTDFA (Map TagId RegId)
newRegForEachTag = M.fromList <$> forEachTag (\t -> (t,) <$> newReg)

generateInitialState :: TNFA.StateId -> GenTDFA Closure
generateInitialState q0 = do
  --regs <- newRegForEachTag
  return [(q0, M.empty, emptyHistory, emptyHistory)]

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> mapM f xs

visitStates :: TNFA -> [StateId] -> GenTDFA ()
visitStates _    [] = return ()
visitStates tnfa ss = do
  newStates <- concatMapM (visitState tnfa) ss
  visitStates tnfa newStates

nextSymbols :: TNFA -> Set TNFA.StateId -> [Char]
nextSymbols TNFA{..} s = collectSymbols [t | (q,t,_) <- tnfaTrans, S.member q s]

collectSymbols :: [TNFATrans] -> [Char]
collectSymbols ts = S.toList . S.unions $ map chars ts
  where
    allChars = S.fromList ['\0'..'\255']
    chars :: TNFATrans -> Set Char
    chars Any = S.delete '\n' allChars
    chars (Symbol c) = S.singleton c
    chars (CClass cs) = S.fromList cs
    chars (CNotClass cs) = allChars S.\\ S.fromList cs
    chars EOL = S.empty
    chars BOL = S.empty
    chars x = error ("Unhandled case " ++ show x)

transitionRegRHSes :: Closure -> [(TagId, RegRHS)]
transitionRegRHSes = S.toList . S.fromList . concatMap stateRegOps
  where stateRegOps (_,_,h,_) =
          map (\t -> (t, regop_rhs h t)) (tagsInHistory h)

updateTagMap :: Closure -> GenTDFA Closure
updateTagMap = mapM $ \(q,r,h,l) -> do
    let o = map (\t -> (t, regop_rhs h t)) (tagsInHistory h)
    r' <- forM o $ \(t,rhs) -> gets ((t,) <$> fromJust . M.lookup (t,rhs) . tagRHSMap)
    return (q,M.union (M.fromList r') r,h,l)

assignReg :: (TagId, RegRHS) -> GenTDFA (Maybe RegOp)
assignReg (tag, rhs) = do
  existingReg <- gets (M.lookup (tag, rhs) . tagRHSMap)
  case existingReg of
    Just r -> return (Just (r, rhs))
    Nothing -> do
      r <- newReg
      addTagRHS tag rhs r
      return (Just (r, rhs))

visitState :: TNFA -> StateId -> GenTDFA [StateId]
visitState tnfa s = do
    -- trace ("visitState " ++ show s) $ return ()
    (clos, prec) <- getState s
    prevStates <- gets (M.keysSet . stateMap)
    let as = nextSymbols tnfa (S.fromList [q | (q,_,_) <- clos])
    ss <- forM as $ \a -> do
        let b = stepOnSymbol tnfa prec a clos
        let c = epsilonClosure False tnfa b
        let rhses = transitionRegRHSes c
        o <- catMaybes <$> mapM assignReg rhses
        c' <- updateTagMap c
        (s',o) <- addState c' o
        --trace (show s ++ "[" ++ show a ++ "] -> " ++ show s' ++ ": " ++ show c' ++ " | " ++
        --       show o) $ return ()
        emitTransition s a s' o
        return s'
    -- Cheating, without this it should all be wrong but it terminates at least
    --clearTagRHSMap
    return (S.toList (S.fromList ss S.\\ prevStates))

sortByPrec :: Prec -> StateClosure -> StateClosure
sortByPrec prec = sortOn (\(x,_,_) -> x `elemIndex` prec)

stepOnSymbol :: TNFA -> Prec -> Char -> StateClosure -> Closure
stepOnSymbol TNFA{..} prec c clos = go (sortByPrec prec clos)
  where
    go [] = []
    go ((q,r,l):xs) = [(p,r,l,emptyHistory) | (_,_,p) <- transitions q] ++ go xs
    transitions q = filter (isTransition q) tnfaTrans
    isTransition q (q', t, _) = q == q' && matchTerm t c

finalRegOps TNFA{..} outRegs s = do
  (state,_) <- getState s
  let Just (_,r,l) = find (\(q,_,_) -> q == tnfaFinalState) state
  --trace (show r ++ " " ++ show l) $ return ()
  let ts = tagsInHistory l
  o <- forEachTag $ \t -> do
    let rhs | t `elem` ts              = regop_rhs l t
            | Just src <- M.lookup t r = CopyReg src
            | otherwise                = error "Missing either register or RHS for tag in finalRegOps"
    let Just dst = M.lookup t outRegs
    return (dst,rhs)
  return (s,o)

determinize :: TNFA -> GenTDFA TDFA
determinize tnfa@TNFA{..} = do
  state0 <- generateInitialState tnfaStartState
  (s0, _) <- addState (epsilonClosure True tnfa state0) []
  (s1, _) <- addState (epsilonClosure False tnfa state0) []
  -- s0 and s1 could be the same if there are no edges on BOL
  visitStates tnfa (nub [s0, s1])

  ts <- gets transitions
  tagRegMap <- gets (M.map stateRegMap . stateMap)
  stateIdMap <- gets (M.map stateStateIds . stateMap)
  let hasFinalState (s,m) | S.member tnfaFinalState m = Just s
                          | otherwise                 = Nothing
      finalStates = mapMaybe hasFinalState (M.toList stateIdMap)
  finRegs <- newRegForEachTag
  finRegOps <- M.fromList <$> forM finalStates (finalRegOps tnfa finRegs)
  return (TDFA {
    tdfaStartState = s0,
    tdfaStartStateNotBOL = s1,
    tdfaFinalStates = S.fromList finalStates,
    tdfaFinalRegisters = finRegs,
    tdfaFinalFunction = finRegOps,
    tdfaTrans = M.map CM.fromList (multiMapFromList ts),
    tdfaFixedTags = tnfaTagMap,
    -- Debugging stuff:
    tdfaTagRegMap = tagRegMap,
    tdfaStateMap = stateIdMap,
    tdfaOriginalFinalState = tnfaFinalState
    })

multiMapFromList :: Ord a => [(a,b)] -> Map a [b]
multiMapFromList ts = foldr prepend M.empty ts
  where
    prepend (s,t) m = M.insert s (t : M.findWithDefault [] s m) m


genTDFA :: TNFA -> TDFA
genTDFA tnfa = evalState (determinize tnfa) (initState tnfa)

tdfaStates :: TDFA -> [StateId]
tdfaStates TDFA{..} = go S.empty [tdfaStartState, tdfaStartStateNotBOL]
  where
    go seen (s:ss)
      | not (S.member s seen) = s : go (S.insert s seen) (ss ++ nextStates s)
      | otherwise = go seen ss
    go _ [] = []
    nextStates s = map fst (CM.elems (getTrans s))
    getTrans :: StateId -> TDFATransTable
    getTrans s = M.findWithDefault CM.empty s tdfaTrans

tdfaRegisters :: TDFA -> [RegId]
tdfaRegisters TDFA{..} = nub (M.elems tdfaFinalRegisters ++ usedRegs)
  where
    usedRegs :: [RegId]
    usedRegs = concatMap (\(_,ops) -> regs ops) (concatMap CM.elems $ M.elems tdfaTrans)
    regs :: RegOps -> [RegId]
    regs = map fst
    nub = S.toList . S.fromList

prettyStates :: TDFA -> String
prettyStates tdfa@TDFA{..} = foldMap showState ss <> fixedTags <> "\n"
  where
    ss = tdfaStates tdfa
    showState s = statePrefix s ++ " " ++ showState' s <> showTrans s <> showTagMap s <> showFinalRegOps s
    statePrefix s = concat
        [ if s == tdfaStartState then "START " else ""
        , if s == tdfaStartStateNotBOL then "MID " else ""
        , if isFinalState s then "FINAL " else "" ]
    showState' s = show s ++ ": " ++ showStateIds s ++ "\n"
    showTrans s = concat [ "  " ++ showRanges rs ++ " => " ++
                           show s' ++ regOps o (getTagRegMap s') ++ "\n"
                           | (rs,(s',o)) <- getTrans s ]
    fixedTags | M.null tdfaFixedTags = "(No fixed tags)"
              | otherwise = "Fixed tags:\n" ++
        concat [ "  " ++ show t ++ " <- " ++ show ft ++ "\n"
                 | (t,ft) <- M.toList tdfaFixedTags ]

    showRanges = intercalate ", " . map showRange
    showRange (min,max) | min == max = show min
                        | otherwise  = show min ++ ".." ++ show max

    regOps [] _ = ""
    regOps ops regMap = prefix "\n    " (map regOp ops)
      where
        getTags reg = [show s ++ ":" ++ show t |
                         (s,ts) <- regMap,
                         (t,r) <- M.toList ts,
                         r == reg ]
        regOp (r,val) = intercalate "," (getTags r) ++ " " ++ show r ++ " <- " ++ show val

    getTagRegMap s = M.toList $ fromJust $ M.lookup s tdfaTagRegMap
    showTagMap s = "  Regs:" <> showPrefix "\n   " (getTagRegMap s) <> "\n"
    showPrefix prefix xs = concat [ prefix ++ show x | x <- xs ]
    prefix p xs = concat [p ++ x | x <- xs ]

    showStateIds s = intercalate ", " . map showStateId . S.toList . fromJust $ M.lookup s tdfaStateMap
      where 
        showStateId s | s == tdfaOriginalFinalState = "[" ++ show s ++ "]"
                      | otherwise               = show s

    getTrans :: StateId -> [([(Char,Char)],TDFATrans)]
    getTrans s = CM.toRanges (M.findWithDefault CM.empty s tdfaTrans)

    isFinalState s = s `S.member` tdfaFinalStates
    finalRegOps s = "  Final reg ops:" ++
        concat ["\n    " ++ show r ++ " <- " ++ show val | (r,val) <- ops] ++
        concat ["\n    " ++ show t ++ " <- " ++ show r  |
                 (t,r) <- M.toList tdfaFinalRegisters ] ++ "\n"
      where ops = fromJust $ M.lookup s tdfaFinalFunction

    showFinalRegOps s | isFinalState s = finalRegOps s
                      | otherwise = ""

testTDFA :: String -> IO ()
testTDFA = putStr . prettyStates . genTDFA . genTNFA . testTagRegex
testTDFAFind = putStr . prettyStates . genTDFA . genTNFA . testTagRegexFind
