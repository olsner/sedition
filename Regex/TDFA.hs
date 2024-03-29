{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Determinization, convert a TNFA to a TDFA state machine.

module Regex.TDFA where

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

-- import Debug.Trace

import qualified CharMap as CM
import CharMap (CharMap)
import Regex.TaggedRegex hiding (Term(..))
import Regex.TNFA (genTNFA, TNFA(..), TNFATrans(..), Tag(..))
import qualified Regex.TNFA as TNFA
import Regex.SimulateTNFA (matchTerm)

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
    tdfaOriginalFinalState :: TNFA.StateId,
    tdfaMinLengths :: Map StateId Int
  }
  deriving (Show, Ord, Eq)

type Prio = TNFA.StateId
type Prec = [Prio]
-- Output or intermediate data of epsilon closure calculation
type Closure = [(Prio, Map TagId RegId, History, History)]
type StateClosure = [(Prio, Map TagId RegId, History)]

type TDFAState = (StateClosure, Prec)
type MapStateKey = (Prec, Set (Prio, History))

-- State for determinization process
data DetState = DetState {
  tags :: Set TagId,
  finalRegisters :: Map TagId RegId,
  stateMap :: Map StateId TDFAState,
  revStateMap :: Map TDFAState StateId,
  mappableStateMap :: Map MapStateKey (Set StateId),
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
    stateMap = M.empty,
    revStateMap = M.empty,
    mappableStateMap = M.empty,
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
        revStateMap = M.insert v k revStateMap,
        mappableStateMap = M.insertWith S.union (stateMapKey v) (S.singleton k) mappableStateMap })

stateMapKey :: TDFAState -> MapStateKey
stateMapKey (s,p) = (p, S.fromList (map fst substates))
  where substates = map (\(q,r,h) -> ((q,h),r)) s

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

history :: History -> TagId -> Maybe RegVal
history hs t = M.lookup t hs

hasHistory :: History -> TagId -> Bool
hasHistory hs t = M.member t hs

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
regop_rhs h t = SetReg (fromJust (history h t))

findState :: TDFAState -> GenTDFA (Maybe StateId)
findState statePrec = gets (M.lookup statePrec . revStateMap)

type Bijection a = (Map a a, Map a a)

makeBijection :: Ord a => [(a,a)] -> Maybe (Bijection a)
makeBijection = go M.empty M.empty
  where
    go fwd rev []         = Just (fwd, rev)
    go fwd rev ((x,y):xs) | x == y = go fwd rev xs
                          | Nothing <- M.lookup x fwd,
                            Nothing <- M.lookup y rev =
                                go (add x y fwd) (add y x rev) xs
                          | Just y' <- M.lookup x fwd, y' == y,
                            Just x' <- M.lookup y rev, x' == x = go fwd rev xs
                          | otherwise = Nothing
    add = M.insert

bijectionToList :: Ord a => Bijection a -> [(a,a)]
bijectionToList (fwd, _) = M.toList fwd

bijectionFwd :: Bijection a -> Map a a
bijectionFwd (fwd, _) = fwd

unionsBijection :: Ord a => [Bijection a] -> Maybe (Bijection a)
unionsBijection = makeBijection . concatMap bijectionToList

bijectionRemove x (fwd, rev)
    | Just y <- M.lookup x fwd = (M.delete x fwd, M.delete y rev)
    | otherwise                = (fwd, rev)

-- First check if the states are compatible:
-- 1. same subset of TNFA states
-- 2. same precedence
-- 3. no "different lookahead tags for some TNFA state"?
--    the "lookahead tags" seems to refer to the "history" (in this case
--    mapping of tag to positive or negative) for each TNFA state. This and 1
--    can be checked at the same time in mappableStates.
--
-- Then try to map registers and return modified register operations.
-- I don't think we mess with reg/tag mappings here, as the output are
-- register operations to be performed in the transition to 't' instead of 's',
-- i.e. input ops is suitable for transition from 'u' to 's', output ops go
-- from 'u' to 't'. 'u' has the same tag/register mappings as before, 's' will
-- not exist and 't' is not modified.
mapState :: Set TagId -> RegOps -> TDFAState -> TDFAState -> Maybe RegOps
mapState allTags ops (s,_) (t,_) = do
        -- trace ("mappable?\n   " ++ show (s,p) ++ "\n<> " ++ show (t,q)
        --        ++ " | " ++ show ops) $ return ()
        subMappings <- mappedRegs
        -- trace ("Mapped regs: " ++ show subMappings) $ return ()
        allMappings <- unionsBijection subMappings
        -- trace ("All mapped regs: " ++ show allMappings) $ return ()
        let copyMappings = bijectionToList (foldr bijectionRemove allMappings (map fst ops))
        let ops' = topo_sort (copyOps copyMappings ++ adjustOps (bijectionFwd allMappings))
        --trace ("Mapped ops: " ++ show ops ++ " -> " ++ show ops') $ return ()
        return ops'
  where
    substates = M.fromList . map (\(q,r,h) -> ((q,h),r))
    s_regs = substates s
    t_regs = substates t
    mappedRegs = M.elems <$> unionWithMaybe mapRegs s_regs t_regs
    mapRegs :: (Prio, History) -> Map TagId RegId -> Map TagId RegId -> Maybe (Bijection RegId)
    mapRegs k xs ys = mapTags (unsetTags k) xs ys
    -- i.e. unmodified (here) - tags that are overwritten here can simply be
    -- put in different registers without copying some old value first.
    unsetTags (_, hs) = S.toList (allTags S.\\ M.keysSet hs)
    mapTags ts xs ys = makeBijection =<< (forM ts $ \t -> do
      -- All tags must have registers for this to work, even if the registers
      -- are never set before. This is ensured in the initial DetState.
      let Just x = M.lookup t xs
      let Just y = M.lookup t ys
      return (x, y))

    -- Copies: any tags that aren't overwritten this time need to be copied
    -- from whatever register they used to live in, to the registers the
    -- existing state expects them in. (i,j) means source register i should
    -- have target register j, so copy j <- i.
    -- The written regsiters are removed in copyMappings above.
    copyOps xs = [(j, CopyReg i) | (i,j) <- xs]
    -- Adjusted ops: tags written here may need to be written in new registers.
    adjustOps m = [(j, o) | (i, o) <- ops, let j = M.findWithDefault i i m]

    -- "sort" probably doesn't work, but neither probably does 'id'. What kind
    -- of topological sort do they mean?
    topo_sort = id -- sort

unionWithMaybe :: (Applicative t, Ord a) => (a -> b -> b -> t c) -> Map a b -> Map a b -> t (Map a c)
unionWithMaybe f x y = M.fromList <$> sequenceA (zipWith f' (M.toList x) (M.toList y))
  where f' (k1,x) (k2,y) | k1 == k2 = (k1,) <$> f k1 x y
                         | otherwise = error "Unmatching maps in unionWithMaybe"

-- mapMaybeM f = liftM catMaybes . mapM f
maybeHead (x:_) = Just x
maybeHead [] = Nothing

findMapState :: TDFAState -> RegOps -> GenTDFA (Maybe (StateId, RegOps))
findMapState new ops = do
  allTags <- gets tags
  mappableStates <- gets (M.lookup (stateMapKey new) . mappableStateMap)
  case mappableStates of
    Nothing -> return Nothing
    Just stateIds -> do
      states <- mapM (\i -> (i,) <$> getState i) (S.toList stateIds)
      return (maybeHead (mapMaybe (tryMapState allTags) states))
  where
    tryMapState allTags (id, s) = do
      (id,) <$> mapState allTags ops new s


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
-- gnused madding.sed has 5446 states.
maxStates = 100000

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
symbolTrans EOL = True
symbolTrans _ = True

epsilonClosure :: Bool -> TNFA -> Closure -> Closure
epsilonClosure bol TNFA{..} = possibleStates . go S.empty []
  where
    go :: Set TNFA.StateId -> Closure -> Closure -> Closure
    go _     c []               = reverse c
    go added c (s@(q,r,h,l):xs) = go (S.insert q added) (s:c) (ys ++ xs)
      where
        epst = sort [(prio,t,p) | (Eps prio t,p) <- transFrom q]
        ys = [ (p,r,h,appendHistory l t) | (_,t,p) <- epst,
                                           not (S.member p added) ]
             ++ [ (p,r,h,l) | p <- anchors, not (S.member p added) ]
        eol = False -- Should this really be handled here?
        anchors = [p | eol, (EOL,p) <- transFrom q] ++
                  [p | bol, (BOL,p) <- transFrom q]

    possibleStates = filter (\(q,_,_,_) -> q `S.member` tnfaClosedStates)
    transFrom s = M.findWithDefault [] s tnfaTrans


forEachTag :: (TagId -> GenTDFA a) -> GenTDFA [a]
forEachTag f = do
    ts <- gets (S.toList . tags)
    mapM f ts

newRegForEachTag :: GenTDFA (Map TagId RegId)
newRegForEachTag = M.fromList <$> forEachTag (\t -> (t,) <$> newReg)

generateInitialState :: TNFA.StateId -> GenTDFA Closure
generateInitialState q0 = do
  regs <- newRegForEachTag
  return [(q0, regs, emptyHistory, emptyHistory)]

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> mapM f xs

visitStates :: TNFA -> [StateId] -> GenTDFA ()
visitStates _    [] = return ()
visitStates tnfa ss = do
  newStates <- concatMapM (visitState tnfa) ss
  visitStates tnfa newStates

nextSymbols :: TNFA -> [TNFA.StateId] -> [Char]
nextSymbols TNFA{..} qs =
  collectSymbols [t | q <- qs, (t,_) <- M.findWithDefault [] q tnfaTrans ]

collectSymbols :: [TNFATrans] -> [Char]
collectSymbols ts = S.toList . S.unions $ map chars ts
  where
    allChars = S.fromList ['\0'..'\255']
    chars :: TNFATrans -> Set Char
    chars Any = allChars
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

assignReg :: (TagId, RegRHS) -> GenTDFA RegOp
assignReg (tag, rhs) = do
  existingReg <- gets (M.lookup (tag, rhs) . tagRHSMap)
  case existingReg of
    Just r -> return (r, rhs)
    Nothing -> do
      r <- newReg
      addTagRHS tag rhs r
      return (r, rhs)

addStateForReach :: TNFA -> Closure -> GenTDFA (Closure, RegOps)
addStateForReach tnfa b = do
    let c = epsilonClosure False tnfa b
    let rhses = transitionRegRHSes c
    o <- mapM assignReg rhses
    c' <- updateTagMap c
    return (c', o)

visitState :: TNFA -> StateId -> GenTDFA [StateId]
visitState tnfa s = do
    -- trace ("visitState " ++ show s) $ return ()
    (clos, prec) <- getState s
    prevStates <- gets (M.keysSet . stateMap)
    let as = nextSymbols tnfa [q | (q,_,_) <- clos]
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
            fo <- finalRegOps' r l
            emitEOLTransition s (o ++ fo)

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
    go ((q,r,l):xs) = [(p,r,l,emptyHistory) | (_,p) <- transitions q] ++ go xs
    transitions q = filter isTransition (M.findWithDefault [] q tnfaTrans)
    isTransition (t, _) = matchTerm t c

stepOnEOL :: TNFA -> Prec -> StateClosure -> Closure
stepOnEOL TNFA{..} prec clos = go (sortByPrec prec clos)
  where
    go [] = []
    go ((q,r,l):xs) = [(p,r,l,emptyHistory) | (_,p) <- transitions q] ++ go xs
    transitions q = filter isTransition (M.findWithDefault [] q tnfaTrans)
    isTransition (EOL, _) = True
    isTransition _ = False

finalRegOps tnfa s = do
  (state,_) <- getState s
  let Just (_,r,l) = find (\(q,_,_) -> q == tnfaFinalState tnfa) state
  o <- finalRegOps' r l
  return (s, o)

finalRegOps' r l = do
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
insertRegOps m = map $ \(s, (c, (s', o))) -> (s, (c, (s', added s s' ++ o)))
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
  let tdfa = TDFA {
    tdfaStartState = s0,
    tdfaStartStateNotBOL = s1,
    tdfaFinalRegisters = finRegs,
    tdfaFinalFunction = finRegOps,
    tdfaFallbackFunction = M.fromList fb,
    tdfaTrans = M.map CM.fromList (multiMapFromList ts'),
    tdfaEOL = M.fromList ets,
    tdfaFixedTags = tnfaTagMap,
    -- Debugging stuff:
    tdfaTagRegMap = tagRegMap,
    tdfaStateMap = stateIdMap,
    tdfaOriginalFinalState = tnfaFinalState,
    tdfaMinLengths = minLengths tdfa
    } in return tdfa

multiMapFromList :: Ord a => [(a,b)] -> Map a [b]
multiMapFromList ts = foldr prepend M.empty ts
  where
    prepend (s,t) m = M.insert s (t : M.findWithDefault [] s m) m


genTDFA :: TNFA -> TDFA
genTDFA tnfa = evalState (determinize tnfa) (initState tnfa)

-- TODO Cache in TDFA struct
tdfaStates :: TDFA -> [StateId]
tdfaStates tdfa@TDFA{..} = go S.empty (S.fromList [tdfaStartState, tdfaStartStateNotBOL])
  where
    go seen todo
      | S.null todo = S.toList seen
      | (s, todo') <- S.deleteFindMin todo =
        go (S.insert s seen) (S.union todo' (newTodo s))
      where newTodo s = S.fromList (nextStates tdfa s) `S.difference` seen

nextStates TDFA{..} s = map fst (CM.elems (getTrans s))
  where
    getTrans :: StateId -> TDFATransTable
    getTrans s = M.findWithDefault CM.empty s tdfaTrans

tdfaRegisters :: TDFA -> [RegId]
tdfaRegisters TDFA{..} = nub (M.elems tdfaFinalRegisters ++ usedRegs)
  where
    usedRegs :: [RegId]
    usedRegs = concatMap (\(_,ops) -> regs ops) (concatMap CM.elems $ M.elems tdfaTrans) ++ concatMap (concatMap regs . M.elems) [tdfaFinalFunction, tdfaEOL, tdfaFallbackFunction]
    regs :: RegOps -> [RegId]
    regs = map fst
    nub = S.toList . S.fromList

prettyStates :: TDFA -> String
prettyStates tdfa@TDFA{..} = foldMap showState ss <> fixedTags <> "\n"
  where
    ss = tdfaStates tdfa
    showState s = statePrefix s <> showState' s <> showTrans s <> showTagMap s <> showEOLRegOps s <> showFinalRegOps s <> showFallbackRegOps s <> showMinLength s
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
                         (t,r) <- ts,
                         r == reg ]
        regOp (r,val) = intercalate "," (getTags r) ++ " " ++ show r ++ " <- " ++ show val

    getTagRegMap s = [(s, M.toList rs) |
        (s,rs) <- M.toList $ M.findWithDefault M.empty s tdfaTagRegMap,
        not (M.null rs) ]
    showTagMap s | not (null rs) = "  Regs:" <> showPrefix "\n   " rs <> "\n"
                 | otherwise     = ""
      where rs = getTagRegMap s
    showPrefix prefix xs = concat [ prefix ++ show x | x <- xs ]
    prefix p xs = concat [p ++ x | x <- xs ]

    showStateIds s = intercalate ", " . map showStateId . S.toList . fromJust $ M.lookup s tdfaStateMap
      where 
        showStateId s | s == tdfaOriginalFinalState = "[" ++ show s ++ "]"
                      | otherwise               = show s

    getTrans :: StateId -> [([(Char,Char)],TDFATrans)]
    getTrans s = CM.toRanges (M.findWithDefault CM.empty s tdfaTrans)

    isFinalState s = s `M.member` tdfaFinalFunction
    finalRegOps ops =
        concat ["\n    " ++ show r ++ " <- " ++ show val | (r,val) <- ops] ++
        finalTagRegs

    finalTagRegs = concat ["\n    " ++ show t ++ " <- " ++ show r  |
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
        concat ["\n    " ++ show r ++ " <- " ++ show val | (r,val) <- ops] ++
        finalTagRegs

    showEOLRegOps s | Just o <- M.lookup s tdfaEOL = eolRegOps o
                    | otherwise = ""

    showMinLength s | Just dist <- M.lookup s tdfaMinLengths = "  Min length: " ++ show dist ++ "\n"
                    | otherwise = "  [failed state]\n"

-- Minimum length to an accepting state. If there aren't this many characters
-- left in the string it cannot match from here.
minLengths :: TDFA -> Map StateId Int
minLengths tdfa@TDFA{..} = go' M.empty 0 (M.keysSet (tdfaFinalFunction `M.union` tdfaEOL `M.union` tdfaFallbackFunction))
  where
    -- States in "new" are newly discovered states at distance "dist" from a
    -- final state. Start at dist = 0 with the final states, than increase
    -- distance by one and add all previous states (that we haven't already
    -- seen).
    go' res dist new | S.null new = res
                     | otherwise  = go' res' (dist + 1) new'
      where
        res' = res `M.union` M.fromSet (const dist) new
        new' = S.unions (map ps (S.toList new)) `S.difference` M.keysSet res'
        ps s = M.findWithDefault S.empty s allPrevStates

    ss = S.fromList (tdfaStates tdfa)
    allPrevStates = M.map S.fromList $ multiMapFromList [(next, prev) | prev <- S.toList ss, next <- nextStates tdfa prev]

testTDFA :: String -> IO ()
testTDFA = putStr . prettyStates . genTDFA . genTNFA . testTagRegex
