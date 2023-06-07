{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, RecursiveDo, OverloadedStrings #-}

#define DEBUG 0

module IR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import qualified Data.ByteString.Char8 as C
import Data.IntSet (IntSet)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (fromJust)

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
  | IsMatch MVar
  | PRef Pred
  | IsStringEmpty SVar
  deriving (Show,Eq)
cTrue = True
cFalse = False

newtype SVar = SVar Int deriving (Ord,Eq)
data StringExpr
  = SConst S
  | SVarRef SVar
  | SRandomString
  -- from to string
  | STrans S S SVar
  | SAppend [StringExpr]
  | SSubstring SVar SIndex SIndex
  | SFormatLiteral Int SVar
  | SGetLineNumber
  deriving (Show,Eq)

emptyS = SConst ""
newline = SConst "\n"
-- TODO Very inefficient with the current implementation(s) of STrans, but that
-- should be optimized in general and might end up just as efficient as using
-- toupper/tolower. (which might not even be all that good anyway.)
sUpper = STrans (C.pack ['a'..'z']) (C.pack ['A'..'Z'])
sLower = STrans (C.pack ['A'..'Z']) (C.pack ['a'..'z'])
sAppendVarsNL a b = SAppend [SVarRef a, newline, SVarRef b]
sAppendNL a b = SAppend [a, newline, b]
sAppend a b = SAppend [SVarRef a, SVarRef b]

data SIndex
  = SIStart
  | SIEnd
  | SIOffset Int
  | SIMatchStart MVar
  | SIMatchEnd MVar
  | SIGroupStart MVar Int
  | SIGroupEnd MVar Int
  deriving (Show,Eq)

newtype MVar = MVar Int deriving (Ord,Eq)
instance Show MVar where
  show (MVar n) = "M" ++ show n

-- An implication of baking the used tags into the derived Eq instance is that
-- deduplicating nicely duplicates/specializes regexes that could be made more
-- efficient. We don't care much about binary size or compile time here.
data RE = RE { reID :: Int, reString :: S, reERE :: Bool, reUsedTags :: Maybe IntSet }
  deriving (Show,Ord,Eq)

compileRE :: Maybe S -> IRM (Maybe RE)
compileRE Nothing  = return Nothing
compileRE (Just s) = do
    ere <- gets extendedRegexps
    return (Just (RE (-1) s ere Nothing))

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
  If            :: Cond -> Label -> Label   -> Insn O C
  Fork          :: Label -> Label           -> Insn O C
  Quit          :: ExitCode                 -> Insn O C

  -- Wait for IPC or line of input or EOF.
  Wait          :: FD                       -> Insn O O
  -- Writes SVar. Should be a StringExpr I guess then?
  -- OTOH it has side effects and this style kind of matches Read below.
  GetMessage    :: SVar                     -> Insn O O

  SetP          :: Pred -> Bool             -> Insn O O
  SetS          :: SVar -> StringExpr       -> Insn O O
  SetM          :: MVar -> MatchExpr        -> Insn O O
  -- for n/N (which can never accept interrupts), and R
  Read          :: SVar -> FD               -> Insn O O
  Print         :: FD -> SVar               -> Insn O O
  Message       :: SVar                     -> Insn O O

  SetLastRE     :: RE                       -> Insn O O

  ShellExec     :: SVar                     -> Insn O O
  Listen        :: FD -> (Maybe S) -> FD    -> Insn O O
  Accept        :: FD -> FD                 -> Insn O O
  Redirect      :: FD -> FD                 -> Insn O O
  Comment       :: String                   -> Insn O O

  OpenFile      :: FD -> Bool -> S          -> Insn O O
  -- Reads a whole file at once, where normal Read just reads the next line.
  ReadFile      :: SVar -> FD               -> Insn O O
  CloseFile     :: FD                       -> Insn O O


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
  , firstFreePred :: Int
  , firstFreeMVar :: Int
  , firstFreeSVar :: Int
  , autoprint :: Bool
  , extendedRegexps :: Bool
  , ipcEnabled :: Bool
  , sourceLabels :: Map S Label
  , holdSpaces :: Map S SVar
  , externalFiles :: Map (S, Bool) FD
  , nextCycleLabels :: (Label, Label)
  , program :: Graph Insn O O
  }

nextCycleLabelNoPrint = snd . nextCycleLabels
nextCycleLabelPrint = fst . nextCycleLabels

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

invalidLabel :: String -> Label
invalidLabel s = error ("Invalid label: " ++ s)
startState autoprint ere ipc = State
  { firstFreeUnique = 0
  , firstFreePred = firstNormalPred
  , firstFreeMVar = 0
  , firstFreeSVar = firstNormalSVar
  , autoprint = autoprint
  , extendedRegexps = ere
  , ipcEnabled = ipc
  , sourceLabels = M.empty
  , holdSpaces = M.empty
  , externalFiles = M.empty
  , nextCycleLabels = (dummyCycleLabel, dummyCycleLabel)
  , program = emptyGraph
  }
dummyCycleLabel = invalidLabel "uninitialized next-cycle label"

instance Show Pred where
  show (Pred 0) = "P{pre-first}"
  show (Pred 1) = "P{irq}"
  show (Pred 2) = "P{run-normal}"
  show (Pred 3) = "P{last-subst}"
  show (Pred 4) = "P{queued-output}"
  show (Pred 5) = "P{has-pattern}"
  show (Pred n) = "P" ++ show n

firstNormalPred = 6

pPreFirst = Pred 0
pIntr = Pred 1
pRunNormal = Pred 2
pLastSubst = Pred 3
pHasQueuedOutput = Pred 4
pHasPattern = Pred 5

setLastSubst x = emit (SetP pLastSubst x)

instance Show SVar where
  show (SVar 0) = "S{pattern-space}"
  show (SVar 1) = "S{output-queue}"
  show (SVar 2) = "S{hold-space}"
  show (SVar n) = "S" ++ show n

sPattern = SVar 0
sOutputQueue = SVar 1
-- TODO Remove and assign generically using hold spaces mapping
sHoldSpace = SVar 2
firstNormalSVar = 3

type IRM = State IRState

instance UniqueMonad IRM where
  freshUnique = do
    res <- firstFreeUnique <$> get
    modify $ \state -> state { firstFreeUnique = res + 1 }
    return res

initBlock :: Label -> Graph Insn C O
initBlock l = mkLabel l

newLabel = freshLabel
newPred = do
    res <- firstFreePred <$> get
    modify $ \state -> state { firstFreePred = res + 1 }
    return (Pred res)
newMatch = do
    res <- firstFreeMVar <$> get
    modify $ \state -> state { firstFreeMVar = res + 1 }
    return (MVar res)
newString :: IRM SVar
newString = do
    res <- firstFreeSVar <$> get
    modify $ \state -> state { firstFreeSVar = res + 1 }
    return (SVar res)

emitPred :: Bool -> IRM Pred
emitPred c = newPred >>= \p -> emit (SetP p c) >> return p

setString s expr = emit (SetS s expr)
copyString :: SVar -> SVar -> IRM ()
copyString s src = setString s (SVarRef src)
emitString :: StringExpr -> IRM SVar
emitString expr = withNewString (\s -> setString s expr)
emitCString :: S -> IRM SVar
emitCString s = emitString (SConst s)
withNewString f = do
    next <- newString
    _ <- f next
    return next

getExternalFD :: S -> Bool -> IRM FD
getExternalFD path write = do
  prev <- gets externalFiles
  case M.lookup (path, write) prev of
    Just fd -> return fd
    Nothing -> do
      let fd = nextFd prev
      modify $ \s -> s { externalFiles = M.insert (path, write) fd prev }
      return fd
  where
    -- Negative FD's for external files
    nextFd = negate . succ . M.size

setPattern s = copyString sPattern s >> setHasPattern
setHasPattern = emit (SetP pHasPattern cTrue)

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
    when ap (tWhenP pHasPattern (emit (Print 0 sPattern)))

tIfP :: Pred -> IRM a -> IRM b -> IRM ()
tIfP p = tIf (PRef p)

tIf :: Cond -> IRM a -> IRM b -> IRM ()
tIf c tx fx = mdo
    t <- finishBlock' (If c t f)
    comment "tIf/true"
    _ <- tx
    f <- emitBranch' e
    comment "tIf/false"
    _ <- fx
    e <- label
    comment "tIf/end"

ifCheck c tx fx = do
  cond <- tCheck c
  tIf cond tx fx

toIR :: Bool -> Bool -> Bool -> [Sed] -> (Label, Graph Insn C C)
toIR autoprint ere ipc seds = evalState go (startState autoprint ere ipc)
  where
   go = do
    entry <- newLabel
    tProgram seds
    outState <- get
    return (entry, mkFirst (Label entry) H.<*> program outState H.<*> mkLast (Quit ExitSuccess))

checkQueuedOutput =
  tWhenP pHasQueuedOutput $ do
    emit (Print 0 sOutputQueue)
    setString sOutputQueue emptyS
    emit (SetP pHasQueuedOutput cFalse)

openFile (path, write) fd = emit (OpenFile fd write path)

-- Entry points to generate:
-- * pre-first line code (if any)
-- * interrupt reception (for new-cycle code)
-- * new cycle label
tProgram seds = mdo
  oldNextCycle <- gets nextCycleLabels

  modify $ \state -> state { nextCycleLabels = (newCyclePrint, newCycleNoPrint) }

  -- Initialize all preset predicates. In particular to prevent optimizations
  -- from deciding that a predicate that only gets set to true will thus also
  -- be true on entry to the program.
  emit (SetP pIntr cFalse)
  emit (SetP pPreFirst cTrue)
  emit (SetP pRunNormal cFalse)
  emit (SetP pLastSubst cFalse)
  emit (SetP pHasQueuedOutput cFalse)
  emit (SetP pHasPattern cFalse)

  start <- emitBranch' openUsedFiles

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
  -- This pIntr predicate also controls control flow around matching interrupts,
  -- so to keep other things working we should maintain the flag correctly even
  -- if ipc is disabled.
  ipc <- gets ipcEnabled
  when ipc (tWhen PendingIPC (() <$ emitBranch' intr))
  emit (SetP pIntr False)

  line <- finishBlock' (If (AtEOF 0) exit line)

  emit (Read sPattern 0)
  setHasPattern
  emit (SetP pPreFirst cFalse)
  emit (SetP pRunNormal cTrue)

  intr <- emitBranch' start

  -- Update pattern variable for matching but don't set pHasPattern in IPC
  -- branch, to avoid printing it at the end of the loop.
  emit (GetMessage sPattern)

  emit (SetP pIntr True)
  emit (SetP pPreFirst False)
  emit (SetP pRunNormal False)

  openUsedFiles <- emitBranch' start

  filesToOpen <- gets (M.toList . externalFiles)
  mapM_ (uncurry openFile) filesToOpen

  exit <- emitBranch' start

  modify $ \state -> state { nextCycleLabels = oldNextCycle }

tSeds = mapM_ tSed

tWhenP p x = tWhen (PRef p) x

tWhenNot c x = mdo
  f <- finishBlock' (If c t f)
  r <- x
  t <- label
  return r

tWhen c x = mdo
  t <- finishBlock' (If c t f)
  res <- x
  f <- label
  return res

withCond' Always whenTrue _ = whenTrue
withCond' (At c) whenTrue whenFalse = do
  cond <- tCheck c
  tIf cond whenTrue whenFalse
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
                  tIf (EndLine n) (clear >> skip) run
               | otherwise = ifCheck end (clear >> run) run

  -- If the end address is a line that's <= the current line, clear the flag
  -- immediately and skip the block.
  tIfP pActive (do comment "between/active"
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

withMatch f = newMatch >>= \m -> f m >> return m
emitMatch match = withMatch $ \m -> emit (SetM m match) >> return m

tCheck (AST.Line 0) = return (PRef pPreFirst)
tCheck (AST.Line n) = return (Line n)
tCheck (AST.Match mre) = do
    m <- tCheckMatch =<< compileRE mre
    return (IsMatch m)
tCheck (AST.IRQ) = return (PRef pIntr)
tCheck (AST.EOF) = return (AtEOF 0)

tCheckMatch (Just re) = do
    m <- emitMatch (Match sPattern re)
    emit (SetLastRE re)
    return m
tCheckMatch Nothing = emitMatch (MatchLastRE sPattern)

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
  -- See comment/fixme for saving/restoring pRunNormal above
  emit (SetP pRunNormal cTrue)
  tCmd x
  emit (SetP pRunNormal cFalse)
-- Special case for change with a range: replace all lines with a single copy
-- of the replacement string.
tSed (Sed (Between start end) (AST.Change repl)) = do
    tSed (Sed (At end) (AST.Insert repl))
    tSed (Sed (Between start end) AST.Delete)
tSed (Sed cond x) = tWhenP pRunNormal $ withCond cond $ tCmd x

readString :: SVar -> Int -> IRM ()
readString s fd = emit (Read s fd)

readStringA :: SVar -> Int -> IRM ()
readStringA s fd = do
    line <- newString
    readString line fd
    setString s (sAppendVarsNL s line)

tCmd :: AST.Cmd -> IRM ()
tCmd (AST.Block xs) = tSeds xs
tCmd (AST.Print fd) = tWhenP pHasPattern $ emit (Print fd sPattern)
tCmd (AST.PrintLineNumber fd) = do
    s <- emitString SGetLineNumber
    emit (Print fd s)
tCmd (AST.PrintLiteral width) = tWhenP pHasPattern $ do
    s <- emitString (SFormatLiteral width sPattern)
    emit (Print 0 s)
tCmd (AST.Message Nothing) = tWhenP pHasPattern $ emit (Message sPattern)
tCmd (AST.Message (Just s)) = do
    tmp <- emitCString s
    emit (Message tmp)
-- FIXME "If there is no more input then sed exits without processing any more
-- commands." (How does read indicate EOF anyway?)
tCmd (AST.Next fd) = do
    printIfAuto
    checkQueuedOutput
    setLastSubst False
    readString sPattern fd
    setHasPattern
tCmd (AST.NextA fd) = do
    checkQueuedOutput
    setLastSubst False
    tIfP pHasPattern (readStringA sPattern fd)
                     (readString sPattern fd >> setHasPattern)
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
    setString sPattern emptyS
    emit (SetP pHasPattern cFalse)
tCmd (AST.Change s) = do
    emitCString s >>= \s -> emit (Print 0 s)
    branchNextCycleNoPrint
tCmd (AST.Delete) = branchNextCycleNoPrint
tCmd (AST.Redirect dst (Just src)) = emit (Redirect dst src)
tCmd (AST.Redirect dst Nothing) = emit (CloseFile dst)
tCmd (AST.Subst mre sub flags actions) = do
  m <- tCheckMatch =<< compileRE mre
  tWhen (IsMatch m) $ do
    setLastSubst True
    -- temp string necessary since original pattern space is input to subst
    s <- tSubst m sPattern sub flags
    setPattern s
    tSubstAction actions s
tCmd (AST.Trans from to) = do
    -- temp string necessary since it's an input (though this could be safe)
    s <- emitString (STrans from to sPattern)
    setPattern s
tCmd (AST.Hold maybeReg) = do
    space <- getHoldMapping maybeReg
    copyString space sPattern
tCmd (AST.HoldA maybeReg) = do
    space <- getHoldMapping maybeReg
    setString space (sAppendVarsNL space sPattern)

tCmd (AST.Get (Just "yhjulwwiefzojcbxybbruweejw")) = do
    setString sPattern SRandomString
    setHasPattern
tCmd (AST.GetA (Just "yhjulwwiefzojcbxybbruweejw")) = do
    setString sPattern (sAppendNL (SVarRef sPattern) SRandomString)

tCmd (AST.Get maybeReg) = setPattern =<< getHoldMapping maybeReg
tCmd (AST.GetA maybeReg) = do
    space <- getHoldMapping maybeReg
    setString sPattern (sAppendVarsNL sPattern space)
tCmd (AST.Exchange maybeReg) = do
    space <- getHoldMapping maybeReg
    -- TODO Add swap string instruction?
    tmp <- emitString (SVarRef space)
    copyString space sPattern
    copyString sPattern tmp
tCmd (AST.Insert s) = emitCString s >>= \s -> emit (Print 0 s)
tCmd (AST.Append s) = tAppendOutputQueue (SConst s)
tCmd (AST.ReadFile path) = do
    fd <- getExternalFD path False
    tWhenNot (AtEOF fd) $ do
        s <- newString
        emit (ReadFile s fd)
        tAppendOutputQueue (SVarRef s)
tCmd (AST.WriteFile path) = do
    fd <- getExternalFD path True
    emit (Print fd sPattern)
tCmd (AST.Quit print status) = () <$ do
  when print $ do
    printIfAuto
    checkQueuedOutput
  finishBlock' (Quit status)
tCmd cmd = error ("tCmd: Unmatched case " ++ show cmd)

tAppendOutputQueue s = tIfP pHasQueuedOutput ifTrue ifFalse
  where
    -- already set to true, so no need to update predicate. Just append to
    -- the queue.
    ifTrue = setString sOutputQueue (sAppendNL (SVarRef sOutputQueue) s)
    -- If there's no queued output yet, we know we can simply replace the
    -- queued output with a constant.
    ifFalse = do
        emit (SetP pHasQueuedOutput cTrue)
        setString sOutputQueue s

tSubstAction SActionNone _ = return ()
tSubstAction SActionExec res = emit (ShellExec res)
tSubstAction (SActionPrint n) res = emit (Print n res)
tSubstAction (SActionWriteFile path) res = do
    fd <- getExternalFD path True
    emit (Print fd res)

data CState
  = Conv CaseConv
  -- Apply the first conversion to one character, then revert to the other
  -- conversion. The predicate starts out True, i.e. first-character conversion
  -- still needs to be done, then is set to False whenever a conversion is
  -- actually done.
  | CharConv Pred CaseConv CaseConv
  deriving (Show)

initCState = Conv NoConv
setCaseConv _ Upper = return (Conv Upper)
setCaseConv _ Lower = return (Conv Lower)
setCaseConv _ AST.NoConv = return (Conv NoConv)
setCaseConv (Conv c) UpperChar = emitPred True >>= \p -> return (CharConv p Upper c)
setCaseConv (Conv c) LowerChar = emitPred True >>= \p -> return (CharConv p Lower c)
setCaseConv (CharConv p _ c) UpperChar = return (CharConv p Upper c)
setCaseConv (CharConv p _ c) LowerChar = return (CharConv p Lower c)

tSub m s sub = case sub of
  Literal lit     -> return (SConst lit)
  WholeMatch      -> return (SSubstring s (SIMatchStart m) (SIMatchEnd m))
  BackReference i -> return (SSubstring s (SIGroupStart m i) (SIGroupEnd m i))
  SetCaseConv _   -> error "leftover SetCaseConv"

{-
Note: Translating case conversions

For the normal upper/lower/reset conversions we track the current conversion
state and apply it to any substitution part we output. The first-character
conversions are a bit more interesting - we need to track the strings we apply
conversion to because empty strings don't count, the first actually output
character is the one that gets case conversion and then we revert to the
previous conversion.

We use a new predicate variable for each conversion step/stage to track if we
should apply the conversion to the next character, then set it to false when
we have output a non-empty string. At IR conversion time we don't try to be
clever about it (e.g. looking at Literals emitted ot anything). That may/will
be done by some optimization later.

Some more interesting behaviours of these escapes:

 * \U..\l.. reverts back to \U after lowercasing one character.
   e.g. echo foobar | sed -r 's/(foo)(bar)/\U\1\l\2/' -> FOObAR

   It might be enough for the first-char case to track one "revert to" state,
   with whatever the previous state was. \U\l\u would be a one-char uppercase
   going back to uppercase so it can be treated as just \U.

 * Literals in the string are affected (this can be done at compile time and
   may remove some of those first-char conversions). For now, leave this for
   optimization passes?
-}
applyCaseConv :: CState -> StringExpr -> IRM StringExpr
applyCaseConv conv s = case conv of
    Conv NoConv -> return s
    Conv Upper -> sUpper <$> emitString s
    Conv Lower -> sLower <$> emitString s
    Conv UpperChar -> error "First-char conversion should have been translated"
    Conv LowerChar -> error "First-char conversion should have been translated"
    CharConv p conv1 convN -> do
      s' <- emitString s
      sres <- newString
      tIfP p (tIf (IsStringEmpty s') (setString sres s)
                                     (convChar conv1 s' >>= setString sres >>
                                      emit (SetP p cFalse)))
             (setString sres =<< applyCaseConv (Conv convN) s)
      return (SVarRef sres)

convChar :: CaseConv -> SVar -> IRM StringExpr
convChar conv s = do
    -- We've already checked that s is not empty.
    head <- emitString (SSubstring s SIStart (SIOffset 1))
    let tail = SSubstring s (SIOffset 1) SIEnd
    let head' = case conv of
                  Lower -> sLower head
                  Upper -> sUpper head
                  _ -> error ("Invalid first-char conversion " ++ show conv)
    return (SAppend [head', tail])

tSubs _ _   _      [] = return []
tSubs m pat cstate (SetCaseConv c:ss) = do
  cstate' <- setCaseConv cstate c
  tSubs m pat cstate' ss
tSubs m pat cstate (sub:subs) = do
  s <- tSub m pat sub
  s' <- applyCaseConv cstate s
  (s':) <$> tSubs m pat cstate subs

tConcat :: [StringExpr] -> IRM SVar
tConcat []  = emitString emptyS
tConcat [x] = emitString x
tConcat xs  = emitString (SAppend xs)

tSubst m s sub flags = case flags of
  SubstFirst -> do
    ss <- tSubs m s initCState sub
    -- TODO Analyze the regexp to see if it will always match from the
    -- beginning and/or to the end of the string.
    let prefix = SSubstring s SIStart (SIMatchStart m)
    let suffix = SSubstring s (SIMatchEnd m) SIEnd
    emitString (SAppend ((prefix:ss) ++ [suffix]))
  SubstNth 1 -> tSubst m s sub SubstFirst
  SubstNth n -> do
    m' <- emitMatch (NextMatch m s)
    tSubst m' s sub (SubstNth (n - 1))
  SubstAll -> mdo
    sres <- emitString (SSubstring s SIStart (SIMatchStart m))

    loop <- label

    mnext <- emitMatch (NextMatch m s)

    ss <- tSubs m s initCState sub
    s1 <- tConcat (SVarRef sres:ss)

    hasNextMatch <- finishBlock' (If (IsMatch mnext) hasNextMatch lastMatch)

    let mid = SSubstring s (SIMatchEnd m) (SIMatchStart mnext)
    setString sres (SAppend [SVarRef s1, mid])
    -- TODO Last instance of copy_match, figure out how to remove. E.g.
    -- duplicate the match code so we can leave the next match in m before
    -- looping?
    emit (SetM m (MVarRef mnext))

    lastMatch <- emitBranch' loop

    let suffix = SSubstring s (SIMatchEnd m) SIEnd
    setString sres (SAppend [SVarRef s1, suffix])

    return sres

tTest ifTrue maybeTarget = mdo
  comment ("test " ++ show ifTrue ++ " " ++ show target)
  target <- case maybeTarget of
    Nothing -> gets nextCycleLabelPrint
    Just name -> getLabelMapping name
  let (t,f) | ifTrue    = (target, l)
            | otherwise = (l, target)
  let clear = setLastSubst False
  tIfP pLastSubst (clear >> emitBranch' t) (clear >> emitBranch' f)
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
allRegexps :: Program -> [RE]
allRegexps graph = S.toList (foldGraphNodes usedRegexps graph S.empty)
numberAllRegexps :: Program -> Program
numberAllRegexps graph = mapGraph f graph
  where
    m = foldGraphNodes numberUsedRegexps graph M.empty
    f :: Insn e x -> Insn e x
    f (SetM m expr) = SetM m (fMatchExpr expr)
    f (SetLastRE re) = SetLastRE (fre re)
    f insn = insn
    fMatchExpr (Match s re) = Match s (fre re)
    fMatchExpr expr = expr
    fre re = re { reID = fromJust (M.lookup re m) }

usedFiles :: Insn e x -> Set FD
usedFiles (Print i _) = S.singleton i
usedFiles (Wait i) = S.singleton i
usedFiles (Read _ i) = S.singleton i
usedFiles (Listen i _ _) = S.singleton i
usedFiles (Accept s c) = S.fromList [s, c]
usedFiles (Redirect i j) = S.fromList [i, j]
usedFiles (CloseFile i) = S.singleton i
usedFiles (ReadFile _ i) = S.singleton i
usedFiles (OpenFile i _ _) = S.singleton i
usedFiles _ = S.empty

usedPredicates :: Insn e x -> Set Pred
usedPredicates (SetP p _) = S.singleton p
usedPredicates (If c _ _) = condUsedPredicates c
usedPredicates _ = S.empty

condUsedPredicates (PRef p) = S.singleton p
condUsedPredicates _ = S.empty

usedStrings :: Insn e x -> Set SVar
usedStrings (Print _ s) = S.singleton s
usedStrings (Read s _) = S.singleton s
usedStrings (SetS s e) = S.insert s (stringExprStrings e)
usedStrings (SetP _ c) = condUsedStrings c
usedStrings (SetM _ m) = matchUsedStrings m
usedStrings (Message s) = S.singleton s
usedStrings (GetMessage s) = S.singleton s
usedStrings (ShellExec s) = S.singleton s
usedStrings _ = S.empty

stringExprStrings (SVarRef s) = S.singleton s
stringExprStrings (STrans _ _ s) = S.singleton s
stringExprStrings (SAppend xs) = S.unions (map stringExprStrings xs)
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
usedMatches (SetS _ s) = stringExprMatches s
usedMatches (SetM m e) = S.insert m (matchUsedMatches e)
usedMatches (If (IsMatch m) _ _) = S.singleton m
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

numberUsedRegexps :: Insn e x -> Map RE Int -> Map RE Int
numberUsedRegexps (SetM _ (Match _ re)) m = M.insertWith (flip const) re (M.size m) m
numberUsedRegexps (SetLastRE re) m = M.insertWith (flip const) re (M.size m) m
numberUsedRegexps _ m = m

usedRegexps :: Insn e x -> Set RE -> Set RE
usedRegexps (SetM _ (Match _ re)) = S.insert re
usedRegexps (SetLastRE re) = S.insert re
usedRegexps _ = id
