{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, RecursiveDo, OverloadedStrings #-}

#define DEBUG 0

module IR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import System.Exit

import AST hiding (Cmd(..), Address(..), Label)
import qualified AST

newtype Pred = Pred Int deriving (Ord,Eq)
type FD = Int

data Cond
  = AtEOF FD
  | PendingIPC
  -- current line == l
  -- Should this take a file too? Redirects could get confusing, but per-file
  -- (per-socket) line counters would make more sense in forks and such.
  -- Fork does reset the counter though.
  | Line Int
  -- current line > l (tested after the first line has been processed)
  | EndLine Int
  | Bool Bool
  | IsMatch MVar
  deriving (Show,Eq)
cTrue = Bool True
cFalse = Bool False

newtype SVar = SVar Int deriving (Ord,Eq)
data StringExpr
  = SConst S
  | SVarRef SVar
  | SRandomString
  -- from to string
  | STrans S S SVar
  -- TODO Replace with more appends and perhaps a predefined svar that contains
  -- a newline. Also investigate if it's always adding the newline or only when
  -- the strings are empty, then more code will need to be generated to use
  -- SAppend.
  | SAppendNL SVar SVar
  | SAppend SVar SVar
  | SSubstring SVar SIndex SIndex
  | SFormatLiteral Int SVar
  | SGetLineNumber
  deriving (Show,Eq)
emptyS = SConst ""

data SIndex
  = SIStart
  | SIEnd
  | SIMatchStart MVar
  | SIMatchEnd MVar
  | SIGroupStart MVar Int
  | SIGroupEnd MVar Int
  deriving (Show,Eq)

newtype MVar = MVar Int deriving (Ord,Eq)
instance Show MVar where
  show (MVar n) = "M" ++ show n

-- Note that we can't immediately replace the "last regexp" state with a match
-- variable since pattern space may be modified between calls, or it may be
-- applied to a different string variable.
data MatchExpr
  = Match SVar RE
  | MatchLastRE SVar
  -- Get a new mvar that starts at match n+1 into mvar. Used for iteration.
  -- Also needs the source string to continue regexp matching in case all
  -- matches are not actually captured on the first match.
  | NextMatch MVar SVar
  | MVarRef MVar
  deriving (Show,Eq)

data Insn e x where
  Label         :: Label                    -> Insn C O

  Branch        :: Label                    -> Insn O C
  If            :: Pred -> Label -> Label   -> Insn O C
  Fork          :: Label -> Label           -> Insn O C
  Quit          :: ExitCode                 -> Insn O C

  -- Wait for IPC or line of input or EOF.
  Wait          :: FD                       -> Insn O O
  -- Writes SVar. Should be a StringExpr I guess then?
  -- OTOH it has side effects and this style kind of matches Read below.
  GetMessage    :: SVar                     -> Insn O O

  SetP          :: Pred -> Cond             -> Insn O O
  SetS          :: SVar -> StringExpr       -> Insn O O
  SetM          :: MVar -> MatchExpr        -> Insn O O
  -- for n/N (which can never accept interrupts)
  Read          :: SVar -> FD               -> Insn O O
  Print         :: FD -> SVar               -> Insn O O
  Message       :: SVar                     -> Insn O O

  SetLastRE     :: RE                       -> Insn O O

  ShellExec     :: SVar                     -> Insn O O
  Listen        :: Int -> (Maybe S) -> Int  -> Insn O O
  Accept        :: Int -> Int               -> Insn O O
  Redirect      :: Int -> Int               -> Insn O O
  CloseFile     :: Int                      -> Insn O O
  Comment       :: String                   -> Insn O O

  WriteFile     :: S -> SVar                -> Insn O O

deriving instance Show (Insn e x)
deriving instance Eq (Insn e x)

showInsn (Label l) = show l ++ ":"
showInsn i = "  " ++ show i

instance NonLocal Insn where
  entryLabel (Label l) = l
  successors (Branch t) = [t]
  successors (If _ t f) = [t,f]
  successors (Fork t c) = [t,c]
  successors (Quit _) = []

instance HooplNode Insn where
  mkBranchNode = Branch
  mkLabelNode = Label

type Program = Graph IR.Insn C C

data IRState = State
  { firstFreeUnique :: Unique
  , autoprint :: Bool
  , sourceLabels :: Map S Label
  , holdSpaces :: Map S SVar
  , nextCycleLabels :: (Label, Label)
  , program :: Graph Insn O O
  }

nextCycleLabelNoPrint = snd . nextCycleLabels
nextCycleLabelPrint = fst . nextCycleLabels

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

invalidLabel :: String -> Label
invalidLabel s = error ("Invalid label: " ++ s)
startState autoprint = State firstNormalPred autoprint M.empty M.empty (dummyCycleLabel, dummyCycleLabel) emptyGraph
dummyCycleLabel = invalidLabel "uninitialized next-cycle label"

instance Show Pred where
  show (Pred 0) = "P{pre-first}"
  show (Pred 1) = "P{irq}"
  show (Pred 2) = "P{run-normal}"
  show (Pred 3) = "P{last-subst}"
  show (Pred 4) = "P{queued-output}"
  show (Pred 5) = "P{has-pattern}"
  show (Pred n) = "P" ++ show n

-- Also includes space for special string and match variables.
firstNormalPred = 5

pPreFirst = Pred 0
pIntr = Pred 1
pRunNormal = Pred 2
pLastSubst = Pred 3
pHasQueuedOutput = Pred 4
pHasPattern = Pred 5

setLastSubst x = emit (SetP pLastSubst (Bool x))

instance Show SVar where
  show (SVar 0) = "S{pattern-space}"
  show (SVar 1) = "S{output-queue}"
  show (SVar 2) = "S{hold-space}"
  show (SVar n) = "S" ++ show n

sPattern = SVar 0
sOutputQueue = SVar 1
sHoldSpace = SVar 2

instance UniqueMonad IRM where
  freshUnique = do
    res <- firstFreeUnique <$> get
    modify $ \state -> state { firstFreeUnique = res + 1 }
    return res

initBlock :: Label -> Graph Insn C O
initBlock l = mkLabel l

newLabel = freshLabel
newPred = Pred <$> freshUnique
newMatch = MVar <$> freshUnique

newString :: IRM SVar
newString = SVar <$> freshUnique
setString :: SVar -> SVar -> IRM ()
setString s src = emit (SetS s (SVarRef src))
emitString :: StringExpr -> IRM SVar
emitString expr = newString >>= \s -> emit (SetS s expr) >> return s
emitCString :: S -> IRM SVar
emitCString s = emitString (SConst s)
withNewString f = do
    next <- newString
    _ <- f next
    return next

setPattern s = setString sPattern s >> emit (SetP pHasPattern cTrue)

addLabelMapping name l = modify $
    \state -> state { sourceLabels = M.insert name l (sourceLabels state) }
getLabelMapping :: S -> IRM Label
getLabelMapping name = do
  res <- M.lookup name . sourceLabels <$> get
  case res of
    Just l -> return l
    Nothing -> withNewLabel (addLabelMapping name)

addHoldMapping name var = modify $
    \state -> state { holdSpaces = M.insert name var (holdSpaces state) }
getHoldMapping Nothing = return sHoldSpace
getHoldMapping (Just name) = do
  res <- M.lookup name . holdSpaces <$> get
  case res of
    Just var -> return var
    Nothing -> withNewString (addHoldMapping name)

emitOCO :: Insn O C -> Insn C O -> IRM ()
emitOCO last first =
    modify $ \s -> s { program = program s H.<*> mkLast last |*><*| mkFirst first }

-- This system of "splitting" the current block and starting a new block with a
-- label is pretty ugly, it would probalby be neater to emit whole blocks (for
-- most cases), e.g. label <- somethingEmitsWholeBlock to get a label to refer
-- to and then emit an (If p trueBlock falseBlock).
thenLabel :: Insn O C -> Label -> IRM ()
thenLabel last next = emitOCO last (Label next)

finishBlock = thenLabel
finishBlock' :: Insn O C -> IRM Label
finishBlock' b = withNewLabel (finishBlock b)

emit :: Insn O O -> IRM ()
emit insn =
    modify $ \s -> s { program = program s H.<*> mkMiddle insn }

comment :: String -> IRM ()
#if DEBUG
comment s = emit (Comment s)
#else
comment _ = return ()
#endif

withNewLabel :: (Label -> IRM a) -> IRM Label
withNewLabel x = do
    next <- newLabel
    _ <- x next
    return next

emitBranch l next = Branch l `thenLabel` next
emitBranch' :: Label -> IRM Label
emitBranch' l = withNewLabel (emitBranch l)
branchNextCyclePrint = () <$ (emitBranch' =<< gets nextCycleLabelPrint)
branchNextCycleNoPrint = () <$ (emitBranch' =<< gets nextCycleLabelNoPrint)

emitLabel l = Branch l `thenLabel` l
-- likely to require mdo unless the first use is afterwards
label :: IRM Label
label = withNewLabel emitLabel

printIfAuto = do
    ap <- gets autoprint
    when ap (tWhen pHasPattern (emit (Print 0 sPattern)))

tIf :: Pred -> IRM a -> IRM b -> IRM ()
tIf p tx fx = mdo
    t <- finishBlock' (If p t f)
    comment "tIf/true"
    _ <- tx
    f <- emitBranch' e
    comment "tIf/false"
    _ <- fx
    e <- label
    comment "tIf/end"

ifCheck c tx fx = do
  p <- tCheck c
  tIf p tx fx

type IRM = State IRState

toIR :: Bool -> [Sed] -> (Label, Graph Insn C C)
toIR autoprint seds = evalState go (startState autoprint)
  where
   go = do
    entry <- newLabel
    tProgram seds
    outState <- get
    return (entry, mkFirst (Label entry) H.<*> program outState H.<*> mkLast (Quit ExitSuccess))

checkQueuedOutput =
  tWhen pHasQueuedOutput $ do
    emit (Print 0 sOutputQueue)
    setString sOutputQueue =<< emitString emptyS
    emit (SetP pHasQueuedOutput cFalse)

-- Entry points to generate:
-- * pre-first line code (if any)
-- * interrupt reception (for new-cycle code)
-- * new cycle label
tProgram seds = mdo
  oldNextCycle <- gets nextCycleLabels

  modify $ \state -> state { nextCycleLabels = (newCyclePrint, newCycleNoPrint) }

  emit (SetP pIntr cFalse)
  emit (SetP pPreFirst cTrue)
  emit (SetP pRunNormal cFalse)

  start <- label
  -- Actual normal program here
  tSeds seds

  newCyclePrint <- label
  printIfAuto
  -- TODO Should this also be done in printIfAuto so that it's done by 'n'?
  emit (SetP pHasPattern cFalse)

  newCycleNoPrint <- label
  checkQueuedOutput
  setLastSubst False

  -- New cycle handling: wait for IPC or input, check for EOF, then run a copy
  -- of the main program with the appropriate predicates set.
  emit (Wait 0)
  emit (SetP pIntr PendingIPC)
  lineOrEOF <- finishBlock' (If pIntr intr lineOrEOF)

  pAtEOF <- emitNewPred (AtEOF 0)
  line <- finishBlock' (If pAtEOF exit line)

  do
    line <- newString
    emit (Read line 0)
    setPattern line

  emit (SetP pPreFirst cFalse)
  emit (SetP pRunNormal cTrue)

  intr <- emitBranch' start

  msg <- newString
  emit (GetMessage msg)
  -- Update pattern variable for matching but don't set pHasPattern in IPC
  -- branch, to avoid printing it at the end of the loop.
  setString sPattern msg

  emit (SetP pPreFirst cFalse)
  emit (SetP pRunNormal cFalse)

  exit <- emitBranch' start

  modify $ \state -> state { nextCycleLabels = oldNextCycle }

tSeds = mapM_ tSed

tWhenNot p x = mdo
  f <- finishBlock' (If p t f)
  r <- x
  t <- label
  return r

tWhen p x = mdo
  t <- finishBlock' (If p t f)
  res <- x
  f <- label
  return res

withCond' Always whenTrue _ = whenTrue
withCond' (At c) whenTrue whenFalse = do
  p <- tCheck c
  tIf p whenTrue whenFalse
withCond' (Between start end) whenTrue whenFalse = mdo
  pActive <- newPred

  let run = emitBranch' t
      skip = emitBranch' f
      setP = emit (SetP pActive cTrue)
      clear = emit (SetP pActive cFalse)

-- Special case for line-based ranges.
-- For normal addresses, the end condition is checked after running the command
-- (or it's checked, setP, and the command is run one more time for the last
-- line).
-- For line numbers, it seems to be checked before running the command with the address.
-- 12,13p should print for lines 12 and 13. 12,3p should only print for 12
-- since the condition is false before reaching the end.
  let checkEnd | (AST.Line n) <- end =  do
                  p <- emitNewPred (EndLine n)
                  tIf p (clear >> skip) run
               | otherwise = ifCheck end (clear >> run) run

  -- If the end address is a line that's <= the current line, clear the flag
  -- immediately and skip the block.
  tIf pActive (do comment "between/active"
                  checkEnd)
              (do comment "between/inactive"
                  ifCheck start (comment "between/first" >> setP >> run) skip)

  t <- label
  _ <- whenTrue
  comment "between/end of code"
  f <- emitBranch' e
  _ <- whenFalse
  e <- label
  return ()
withCond' (NotAddr addr) whenTrue whenFalse = withCond' addr whenFalse whenTrue

withCond addr x = withCond' addr x (return ())

withNewPred f = newPred >>= \p -> f p >> return p
emitNewPred cond = withNewPred $ \p -> emit (SetP p cond) >> return p

withMatch f = newMatch >>= \m -> f m >> return m
emitMatch match = withMatch $ \m -> emit (SetM m match) >> return m

tCheck (AST.Line 0) = return pPreFirst
tCheck (AST.Line n) = emitNewPred (Line n)
tCheck (AST.Match mre) = fst <$> tCheckMatch mre
tCheck (AST.IRQ) = return pIntr
tCheck (AST.EOF) = emitNewPred (AtEOF 0)

tCheckMatch (Just re) = do
    m <- emitMatch (Match sPattern re)
    p <- emitNewPred (IsMatch m)
    emit (SetLastRE re)
    return (p, m)
tCheckMatch Nothing = do
    m <- emitMatch (MatchLastRE sPattern)
    p <- emitNewPred (IsMatch m)
    return (p, m)

tSed :: Sed -> IRM ()
tSed (Sed Always (AST.Block xs)) = tSeds xs
tSed (Sed cond@(At (AST.Line 0)) x) = withCond cond $ do
  -- While running a 0-conditional line, also run all normal lines until we
  -- either reach the "fall-through" from that line, or until we start a new
  -- cycle, then reset it back to... its original value, hmm...
  emit (SetP pRunNormal cTrue)
  tCmd x
  -- FIXME This may need to keep a counter or something rather than just set
  -- to false. Or assign a fresh predicate to push/copy the value into?
  emit (SetP pRunNormal cFalse)
tSed (Sed cond@(At AST.IRQ) x) = withCond cond $ do
  -- See comment/fixme for saving/restrogin pRunNormal above
  emit (SetP pRunNormal cTrue)
  tCmd x
  emit (SetP pRunNormal cFalse)
-- Special case for change with a range: replace all lines with a single copy
-- of the replacement string.
tSed (Sed (Between start end) (AST.Change repl)) = do
    tSed (Sed (At end) (AST.Insert repl))
    tSed (Sed (Between start end) AST.Delete)
tSed (Sed cond x) = tWhen pRunNormal $ withCond cond $ tCmd x

readString :: Int -> IRM SVar
readString fd = do
    s <- newString
    emit (Read s fd)
    return s

tCmd :: AST.Cmd -> IRM ()
tCmd (AST.Block xs) = tSeds xs
tCmd (AST.Print fd) = tWhen pHasPattern $ emit (Print fd sPattern)
tCmd (AST.PrintLineNumber fd) = do
    s <- emitString SGetLineNumber
    emit (Print fd s)
tCmd (AST.PrintLiteral width) = tWhen pHasPattern $ do
    s <- emitString (SFormatLiteral width sPattern)
    emit (Print 0 s)
tCmd (AST.Message Nothing) = tWhen pHasPattern $ emit (Message sPattern)
tCmd (AST.Message (Just s)) = do
    tmp <- emitCString s
    emit (Message tmp)
-- FIXME "If there is no more input then sed exits without processing any more
-- commands." (How does read indicate EOF anyway?)
tCmd (AST.Next fd) = do
    printIfAuto
    checkQueuedOutput
    setLastSubst False
    line <- readString fd
    setPattern line
tCmd (AST.NextA fd) = do
    checkQueuedOutput
    setLastSubst False
    line <- readString fd
    tmp <- emitString (SAppendNL sPattern line)
    tIf pHasPattern (setPattern tmp) (setPattern line)
tCmd (AST.Listen fd host port) = emit (Listen fd host port)
tCmd (AST.Accept sfd fd) = emit (Accept sfd fd)
tCmd (AST.Label name) = do
  emitLabel =<< getLabelMapping name
  comment ("at label " ++ show name)
tCmd (AST.Branch (Just name)) = do
  comment ("branch " ++ show name)
  _ <- emitBranch' =<< getLabelMapping name
  return ()
tCmd (AST.Branch Nothing) = branchNextCyclePrint
tCmd (AST.Test target) = tTest True target
tCmd (AST.TestNot target) = tTest False target
tCmd (AST.Fork sed) = mdo
  entry <- finishBlock' (Fork entry exit)

  oldNextCycle <- nextCycleLabels <$> get
  tProgram [sed]
  modify $ \state -> state { nextCycleLabels = oldNextCycle }

  -- End of thread (quit)
  exit <- finishBlock' (Quit ExitSuccess)
  return ()

tCmd (AST.Clear) = do
    t <- emitString emptyS
    setString sPattern t
    emit (SetP pHasPattern cFalse)
tCmd (AST.Change s) = do
    emitCString s >>= \s -> emit (Print 0 s)
    branchNextCycleNoPrint
tCmd (AST.Delete) = branchNextCycleNoPrint
tCmd (AST.Redirect dst (Just src)) = emit (Redirect dst src)
tCmd (AST.Redirect dst Nothing) = emit (CloseFile dst)
tCmd (AST.Subst mre sub flags actions) = do
  (p, m) <- tCheckMatch mre
  tWhen p $ do
    setLastSubst True
    s <- tSubst m sPattern sub flags
    setPattern s
    tSubstAction actions s
tCmd (AST.Trans from to) = do
    s <- emitString (STrans from to sPattern)
    setPattern s
tCmd (AST.Hold maybeReg) = do
    space <- getHoldMapping maybeReg
    setString space sPattern
tCmd (AST.HoldA maybeReg) = do
    space <- getHoldMapping maybeReg
    tmp2 <- emitString (SAppendNL space sPattern)
    setString space tmp2

tCmd (AST.Get (Just "yhjulwwiefzojcbxybbruweejw")) = do
    temp <- emitString SRandomString
    setPattern temp
tCmd (AST.GetA (Just "yhjulwwiefzojcbxybbruweejw")) = do
    temp <- emitString SRandomString
    tmp2 <- emitString (SAppendNL sPattern temp)
    setString sPattern tmp2

tCmd (AST.Get maybeReg) = setPattern =<< getHoldMapping maybeReg
tCmd (AST.GetA maybeReg) = do
    space <- getHoldMapping maybeReg
    tmp2 <- emitString (SAppendNL sPattern space)
    setString sPattern tmp2
tCmd (AST.Exchange maybeReg) = do
    space <- getHoldMapping maybeReg
    tmp <- emitString (SVarRef space)
    setString space sPattern
    setString sPattern tmp
tCmd (AST.Insert s) = emitCString s >>= \s -> emit (Print 0 s)
tCmd (AST.Append s) = do
    tIf pHasQueuedOutput ifTrue ifFalse
  where
    -- already set to true, so no need to update predicate. Just append to
    -- the queue.
    ifTrue = do
        temp <- emitCString s
        temp2 <- emitString (SAppendNL sOutputQueue temp)
        setString sOutputQueue temp2
    -- If there's no queued output yet, we know we can simply replace the
    -- queued output with a constant.
    ifFalse = do
        emit (SetP pHasQueuedOutput cTrue)
        temp <- emitCString s
        setString sOutputQueue temp
tCmd (AST.WriteFile path) = emit (WriteFile path sPattern)
tCmd (AST.Quit print status) = () <$ do
  when print $ do
    printIfAuto
    checkQueuedOutput
  finishBlock' (Quit status)
tCmd cmd = error ("tCmd: Unmatched case " ++ show cmd)

tSubstAction SActionNone _ = return ()
tSubstAction SActionExec res = emit (ShellExec res)
tSubstAction (SActionPrint n) res = emit (Print n res)
tSubstAction (SActionWriteFile path) res = emit (WriteFile path res)

tSub m s sub = case sub of
  Literal lit -> emitCString lit
  WholeMatch -> emitString (SSubstring s (SIMatchStart m) (SIMatchEnd m))
  BackReference i ->
    emitString (SSubstring s (SIGroupStart m i) (SIGroupEnd m i))
  SetCaseConv _ -> comment "UNIMPL: case conversion" >> emitString emptyS
  -- _ -> error (show sub)

tConcat [] = emitString emptyS
tConcat [x] = return x
tConcat (x:xs) = emitString . SAppend x =<< tConcat xs

tSubs m s subs = tConcat =<< mapM (tSub m s) subs

tSubst m s sub flags = case flags of
  SubstFirst -> do
    ss <- mapM (tSub m s) sub
    -- TODO Analyze the regexp to see if it will always match from the
    -- beginning and/or to the end of the string.
    prefix <- emitString (SSubstring s SIStart (SIMatchStart m))
    suffix <- emitString (SSubstring s (SIMatchEnd m) SIEnd)
    tConcat ((prefix:ss) ++ [suffix])
  SubstNth 1 -> tSubst m s sub SubstFirst
  SubstNth n -> do
    m' <- emitMatch (NextMatch m s)
    tSubst m' s sub (SubstNth (n - 1))
  SubstAll -> mdo
    sres <- emitString (SSubstring s SIStart (SIMatchStart m))
    m' <- emitMatch (MVarRef m)

    loop <- label

    mnext <- emitMatch (NextMatch m' s)
    p <- emitNewPred (IsMatch mnext)

    ss <- mapM (tSub m' s) sub
    s1 <- tConcat (sres:ss)

    hasNextMatch <- finishBlock' (If p hasNextMatch lastMatch)

    mid <- emitString (SSubstring s (SIMatchEnd m') (SIMatchStart mnext))
    emit (SetS sres (SAppend s1 mid))
    emit (SetM m' (MVarRef mnext))

    lastMatch <- emitBranch' loop

    suffix <- emitString (SSubstring s (SIMatchEnd m') SIEnd)
    emit (SetS sres (SAppend s1 suffix))

    return sres

tTest ifTrue maybeTarget = mdo
  comment ("test " ++ show ifTrue ++ " " ++ show target)
  target <- case maybeTarget of
    Nothing -> gets nextCycleLabelPrint
    Just name -> getLabelMapping name
  let (t,f) | ifTrue    = (target, l)
            | otherwise = (l, target)
  let clear = setLastSubst False
  tIf pLastSubst (clear >> emitBranch' t) (clear >> emitBranch' f)
  l <- label
  return ()

allPredicates :: Program -> Set Pred
allPredicates graph = foldGraphNodes (S.union . usedPredicates) graph S.empty
allStrings :: Program -> Set SVar
allStrings graph = foldGraphNodes (S.union . usedStrings) graph S.empty
allFiles :: Program -> Set FD
allFiles graph = foldGraphNodes (S.union . usedFiles) graph S.empty
allMatches :: Program -> Set MVar
allMatches graph = foldGraphNodes (S.union . usedMatches) graph S.empty

usedFiles :: Insn e x -> Set FD
usedFiles (Print i _) = S.singleton i
usedFiles (Wait i) = S.singleton i
usedFiles (Read _ i) = S.singleton i
usedFiles (Listen i _ _) = S.singleton i
usedFiles (Accept s c) = S.fromList [s, c]
usedFiles (Redirect i j) = S.fromList [i, j]
usedFiles (CloseFile i) = S.singleton i
usedFiles (SetP _ c) = condUsedFiles c
usedFiles _ = S.empty

usedPredicates :: Insn e x -> Set Pred
usedPredicates (SetP p _) = S.singleton p
usedPredicates (If p _ _) = S.singleton p
usedPredicates _ = S.empty

usedStrings :: Insn e x -> Set SVar
usedStrings (Print _ s) = S.singleton s
usedStrings (Read s _) = S.singleton s
usedStrings (SetS s e) = S.insert s (stringExprStrings e)
usedStrings (SetP _ c) = condUsedStrings c
usedStrings (SetM _ m) = matchUsedStrings m
usedStrings (Message s) = S.singleton s
usedStrings (GetMessage s) = S.singleton s
usedStrings (ShellExec s) = S.singleton s
usedStrings (WriteFile _ s) = S.singleton s
usedStrings _ = S.empty

stringExprStrings (SVarRef s) = S.singleton s
stringExprStrings (STrans _ _ s) = S.singleton s
stringExprStrings (SAppendNL s t) = S.insert s (S.singleton t)
stringExprStrings (SAppend s t) = S.insert s (S.singleton t)
stringExprStrings (SSubstring s _ _) = S.singleton s
stringExprStrings (SFormatLiteral _ s) = S.singleton s
stringExprStrings (SConst _) = S.empty
stringExprStrings SRandomString = S.empty
stringExprStrings SGetLineNumber = S.empty

matchUsedStrings (Match s _) = S.singleton s
matchUsedStrings (MatchLastRE s) = S.singleton s
matchUsedStrings (NextMatch _ s) = S.singleton s
matchUsedStrings (MVarRef _) = S.empty

usedMatches :: Insn e x -> Set MVar
usedMatches (SetP _ c) = condUsedMatches c
usedMatches (SetS _ s) = stringExprMatches s
usedMatches (SetM m _) = S.singleton m
usedMatches _ = S.empty

stringExprMatches (SSubstring _ i1 i2) =
  stringIndexMatches i1 (stringIndexMatches i2 S.empty)
stringExprMatches _ = S.empty

stringIndexMatches (SIMatchStart m) = S.insert m
stringIndexMatches (SIMatchEnd m) = S.insert m
stringIndexMatches (SIGroupStart m _) = S.insert m
stringIndexMatches (SIGroupEnd m _) = S.insert m
stringIndexMatches _ = id

matchUsedMatches (NextMatch m _) = S.singleton m
matchUsedMatches (MVarRef m) = S.singleton m
matchUsedMatches _ = S.empty

condUsedMatches (IsMatch m) = S.singleton m
condUsedMatches _ = S.empty

condUsedStrings _ = S.empty

condUsedFiles (AtEOF i) = S.singleton i
condUsedFiles _ = S.empty
