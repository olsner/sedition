{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Determinization, convert a TNFA to a TDFA state machine.

module TDFA where

import Control.Monad.Trans.State.Strict hiding (mapState)
import Control.Monad

-- import Data.ByteString.Char8 (ByteString)
-- import qualified Data.ByteString.Char8 as C
import Data.List (elemIndex, find, intercalate, nub, sort, sortOn)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import Data.Either (partitionEithers)

import Debug.Trace

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
  show (SetReg rv) = "set" ++ show rv
  show (CopyReg r) = "copy " ++ show r
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
    tdfaFallbackFunction :: Map StateId RegOps,
    tdfaTrans :: Map StateId TDFATransTable,
    -- StateId to regops to perform at EOL. But only if a final state?
    tdfaEOL :: Map StateId RegOps,
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
  finalRegisters :: Map TagId RegId,
  revStateMap :: Map TDFAState StateId,
  stateMap :: Map StateId TDFAState,
  transitions :: [(StateId, (Char, (StateId, RegOps)))],
  eolTransitions :: [(StateId, RegOps)],
  tagRHSMap :: Map (TagId,RegRHS) RegId,
  nextState :: Int,
  nextReg :: Int
    }
  deriving (Show, Ord, Eq)

initState :: TNFA -> DetState
initState tnfa = DetState {
    tags = tags,
    finalRegisters = M.fromList (zip (S.toList tags) (map R [0..])),
    revStateMap = M.empty,
    stateMap = M.empty,
    transitions = [],
    eolTransitions = [],
    tagRHSMap = M.empty,
    nextState = 0,
    nextReg = succ (S.size tags) }
  where tags = TNFA.allTags tnfa

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

emitEOLTransition :: StateId -> RegOps -> GenTDFA ()
emitEOLTransition q o = do
    modify (\state@DetState{..} -> state{ eolTransitions = (q, o) : eolTransitions })

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
stateStateIds (c, _) = tnfaStatesInClosure c
tnfaStatesInClosure = S.fromList . map (\(q,_,_) -> q)

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
--    Something about tags can be different though - two states at the end of
--    ((a)|(b)) would have different outgoing tags for the (a) and (b).
--
-- Then try to map registers and return modified register operations.
mapState :: RegOps -> TDFAState -> TDFAState -> Maybe RegOps
mapState ops (s,p) (s',p')
    | mappableStates s s', p == p' = do
        -- TODO
        trace ("possibly mappable: " ++ show (s,p) ++ " <> " ++ show (s',p')
               ++ " | " ++ show ops) $ return ()
        Nothing
    | otherwise = Nothing

mappableStates s t = tnfaStatesInClosure s == tnfaStatesInClosure t

-- mapMaybeM f = liftM catMaybes . mapM f
maybeHead (x:_) = Just x
maybeHead [] = Nothing

findMapState :: TDFAState -> RegOps -> GenTDFA (Maybe (StateId, RegOps))
findMapState new ops = do
  states <- gets (M.toList . stateMap)
  return (maybeHead (mapMaybe tryMapState states))
  where
    tryMapState (id, s) = do
      (id,) <$> mapState ops new s

-- 1. Find exact match and return existing state id
-- 2. Look through all states to find mappable state
-- 3. Create new state
addState :: Closure -> RegOps -> GenTDFA (StateId, RegOps)
addState closure ops = do
  prev <- findState state
  case prev of
    Just p -> return (p, ops)
    Nothing -> do
      mapped <- findMapState state ops
      case mapped of
        Just (p, ops') -> return (p, ops')
        Nothing -> addNewState state ops
  where
    state = tdfaState closure

-- Mainly to prevent runaway
maxStates = 1000

addNewState :: TDFAState -> RegOps -> GenTDFA (StateId, RegOps)
addNewState state ops = do
    ns <- gets (M.size . stateMap)
    when (ns > maxStates) $ error "Too many states, giving up"
    s <- newState state
    trace ("new state " ++ show s ++ ": " ++ show state ++ " " ++ show ops) $ return ()
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
    chars (Eps _ _) = S.empty

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

addStateForReach :: TNFA -> Closure -> GenTDFA (Closure, RegOps)
addStateForReach tnfa b = do
    let c = epsilonClosure False tnfa b
    let rhses = transitionRegRHSes c
    o <- catMaybes <$> mapM assignReg rhses
    c' <- updateTagMap c
    return (c', o)

visitState :: TNFA -> StateId -> GenTDFA [StateId]
visitState tnfa s = do
    -- trace ("visitState " ++ show s) $ return ()
    (clos, prec) <- getState s
    prevStates <- gets (M.keysSet . stateMap)
    let as = nextSymbols tnfa (S.fromList [q | (q,_,_) <- clos])
    ss <- forM as $ \a -> do
        (c', o) <- addStateForReach tnfa (stepOnSymbol tnfa prec a clos)
        (s', o) <- addState c' o
        -- trace (show s ++ "[" ++ show a ++ "] -> " ++ show s' ++ ": "  ++
        --        show c' ++ " | " ++ show o) $ return ()
        emitTransition s a s' o
        return s'

    -- Annoyingly complicated and duplicatey. stepOnSymbol only looks for
    -- character transitions, and treating EOL as a character is ugly?
    do
        (c', o) <- addStateForReach tnfa (stepOnEOL tnfa prec clos)
        when (containsFinalState tnfa c') $ do
            -- trace (show s ++ "[EOL] -> " ++ show c' ++ " | " ++ show o) $ return ()
            let fin = tnfaFinalState tnfa
            let Just (_,r,_,l) = find (\(q,_,_,_) -> q == fin) c'
            fo <- finalRegOps' tnfa r l
            emitEOLTransition s (o ++ fo)

    -- This seems to cause the generation to loop for some regexps, presumably
    -- because mapState is not yet implemented?
    clearTagRHSMap

    -- Deduplicate and remove any reused existing states
    return (S.toList (S.fromList ss S.\\ prevStates))

containsFinalState TNFA{..} = or . map (\(q,_,_,_) -> q == tnfaFinalState)

sortByPrec :: Prec -> StateClosure -> StateClosure
sortByPrec prec = sortOn (\(x,_,_) -> x `elemIndex` prec)

stepOnSymbol :: TNFA -> Prec -> Char -> StateClosure -> Closure
stepOnSymbol TNFA{..} prec c clos = go (sortByPrec prec clos)
  where
    go [] = []
    go ((q,r,l):xs) = [(p,r,l,emptyHistory) | (_,_,p) <- transitions q] ++ go xs
    transitions q = filter (isTransition q) tnfaTrans
    isTransition q (q', t, _) = q == q' && matchTerm t c

stepOnEOL :: TNFA -> Prec -> StateClosure -> Closure
stepOnEOL TNFA{..} prec clos = go (sortByPrec prec clos)
  where
    go [] = []
    go ((q,r,l):xs) = [(p,r,l,emptyHistory) | (_,_,p) <- transitions q] ++ go xs
    transitions q = filter (isTransition q) tnfaTrans
    isTransition q (q', t, _) = q == q' && t == EOL

finalRegOps tnfa s = do
  (state,_) <- getState s
  let Just (_,r,l) = find (\(q,_,_) -> q == tnfaFinalState tnfa) state
  o <- finalRegOps' tnfa r l
  return (s, o)

finalRegOps' TNFA{..} r l = do
  outRegs <- gets finalRegisters
  --trace (show r ++ " " ++ show l) $ return ()
  let ts = tagsInHistory l
  forEachTag $ \t -> do
    let rhs | t `elem` ts              = regop_rhs l t
            | Just src <- M.lookup t r = CopyReg src
            | otherwise                = error "Missing either register or RHS for tag in finalRegOps"
    let Just dst = M.lookup t outRegs
    return (dst,rhs)


-- For each final state that is a fallback state, return a set of clobbered
-- registers that need backup.
-- Fallback states:
-- * Identify states that have a transition to the default state (= any gaps
--   in their TDFATransTable).
-- * Add states that have transitions to those states, record their register
--   set operations, continue to fixpoint
fallbackStates :: Set StateId -> DetState -> Map StateId (Set RegId)
fallbackStates finalStates s = defaultable
  where
    ts = M.map CM.fromList . multiMapFromList . transitions $ s
    defaultable :: Map StateId (Set RegId)
    defaultable = go M.empty (zip statesWithDefaultTransitions (repeat S.empty))
    go :: Map StateId (Set RegId) -> [(StateId, Set RegId)] -> Map StateId (Set RegId)
    go def     [] = def
    go def ((s,rs):ss)
      | s `M.member` def || s `S.member` finalStates = go def' ss
      | otherwise = go def' (reaches s ++ ss)
      where def' = M.insertWith S.union s rs def
    reaches s | Just ts <- M.lookup s ts = map (\(s,ops) -> (s, regSet ops)) (CM.elems ts)
              | otherwise = []

    regSet = S.fromList . map fst

    statesWithDefaultTransitions = mapMaybe hasDefaultTransitions (M.toList ts)
    hasDefaultTransitions (s,cm) | not (CM.isComplete cm) = Just s
                                 | otherwise              = Nothing

-- For each finalfunction in each fallback state, check which regops are
-- reading from clobbered registers and add backup and fallback operations.
-- Note that the fallback/backup is much simplified when not dealing with
-- register append operations.
-- If there's a finalReg <- otherReg in the final function, add it as a backup
-- operation on all outgoing edges that clobber otherReg. That way the final
-- register will have the correct value already. (and the fallback function
-- for the state will not include a setting of finalReg)
-- Any finalReg <- nonclobbered or finalReg <- position are added to the
-- fallback function.
-- From what I can gather, the final function is replaced by the fallback
-- function when doing fallback. The TDFA runner will need to remember the
-- input position and the state when leaving a final/fallback state.
-- I *guess* the point of all this (except for multi-valued tags?) is to avoid
-- redundant register operations on outgoing edges from final states. Which
-- can be significant if there are many possibly-final states to pass through
-- before reaching the last one.
fallbackRegOps :: RegOps -> Map StateId (Set RegId) -> StateId -> GenTDFA ((StateId, RegOps), Map (StateId, StateId) RegOps)
fallbackRegOps finRegOps clobbered s = do
  let clobberedRegs = M.findWithDefault S.empty s clobbered
  -- TODO Looks like it doesn't need to be in the monad
  fallBackups <- forM finRegOps $ \(i,o) -> do
    case o of
      CopyReg j | j `S.member` clobberedRegs -> return (Right (i, o))
      _ -> return (Left (i, o))
  let (fallback, backup) = partitionEithers (fallBackups)
  ts <- gets transitions
  let additionalOps
       | null backup = []
       | otherwise = [((s, s'), backup) | (q,(_,(s',_))) <- ts,
                                          q == s, M.member s' clobbered]
  return ((s, fallback), M.fromList additionalOps)

insertRegOps :: Map (StateId, StateId) RegOps -> [(StateId, (Char, (StateId, RegOps)))] -> [(StateId, (Char, (StateId, RegOps)))]
insertRegOps m = map $ \(s, (c, (s', o))) -> (s, (c, (s', o ++ added s s')))
  where
   added s s' = M.findWithDefault [] (s,s') m

determinize :: TNFA -> GenTDFA TDFA
determinize tnfa@TNFA{..} = do
  state0 <- generateInitialState tnfaStartState
  (s0, _) <- addState (epsilonClosure True tnfa state0) []
  -- TODO Check if the BOL=False state can accept anything, if not we should
  -- short circuit this to "fail".
  -- And/or we should have this on a higher level and e.g. skip generating the
  -- code for further matches if the regexp is anchored anyway.
  (s1, _) <- addState (epsilonClosure False tnfa state0) []
  -- s0 and s1 could be the same if there are no edges on BOL
  visitStates tnfa (nub [s0, s1])

  ts <- gets transitions
  ets <- gets eolTransitions
  tagRegMap <- gets (M.map stateRegMap . stateMap)
  stateIdMap <- gets (M.map stateStateIds . stateMap)
  let hasFinalState (s,m) | S.member tnfaFinalState m = Just s
                          | otherwise                 = Nothing
      finalStates = mapMaybe hasFinalState (M.toList stateIdMap)
      finalStateSet = S.fromList finalStates
  finRegOps <- M.fromList <$> forM finalStates (finalRegOps tnfa)
  finRegs <- gets finalRegisters
  defaultableStates <- gets (fallbackStates finalStateSet)
  let fallbackStates = M.restrictKeys defaultableStates finalStateSet
  (fb, backups) <- unzip <$> (forM (M.keys fallbackStates) $ \s ->
    fallbackRegOps (M.findWithDefault [] s finRegOps) defaultableStates s)
  let mergedBackups = foldr (M.unionWith (<>)) M.empty backups
  let ts' = insertRegOps mergedBackups ts
  -- trace ("fallbacks: " ++ show fb) (pure ())
  -- trace ("all backup operations: " ++ show mergedBackups) (pure ())
  return (TDFA {
    tdfaStartState = s0,
    tdfaStartStateNotBOL = s1,
    -- TODO use one map for finalstates and finalfunction
    tdfaFinalStates = S.fromList finalStates,
    tdfaFinalRegisters = finRegs,
    tdfaFinalFunction = finRegOps,
    tdfaFallbackFunction = M.fromList fb,
    tdfaTrans = M.map CM.fromList (multiMapFromList ts'),
    tdfaEOL = M.fromList ets,
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
    showState s = statePrefix s <> showState' s <> showTrans s <> showTagMap s <> showEOLRegOps s <> showFinalRegOps s <> showFallbackRegOps s
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
    finalRegOps ops =
        concat ["\n    " ++ show r ++ " <- " ++ show val | (r,val) <- ops] ++
        concat ["\n    " ++ show t ++ " <- " ++ show r  |
                 (t,r) <- M.toList tdfaFinalRegisters ] ++ "\n"

    showFinalRegOps s | isFinalState s = "  Final reg ops:" ++ finalRegOps ops
                      | otherwise = ""
      where ops = fromJust $ M.lookup s tdfaFinalFunction

    isFallbackState s = s `M.member` tdfaFallbackFunction
    showFallbackRegOps s
      | isFallbackState s && ops /= M.findWithDefault [] s tdfaFinalFunction
        = "  Fallback reg ops:" ++ finalRegOps ops
      | otherwise = ""
      where ops = fromJust $ M.lookup s tdfaFallbackFunction

    eolRegOps ops = "  EOL reg ops:" ++
        concat ["\n    " ++ show r ++ " <- " ++ show val | (r,val) <- ops] ++ "\n"

    showEOLRegOps s | Just o <- M.lookup s tdfaEOL = eolRegOps o
                    | otherwise = ""

testTDFA :: String -> IO ()
testTDFA = putStr . prettyStates . genTDFA . genTNFA . testTagRegex
testTDFAFind = putStr . prettyStates . genTDFA . genTNFA . testTagRegexFind
