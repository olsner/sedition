{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, RecursiveDo, OverloadedStrings #-}

#define DEBUG 0

module IR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M

import System.Exit

import AST hiding (Cmd(..), Address(..), Label)
import AST (Replacement)
import qualified AST

newtype Pred = Pred Int deriving (Ord,Eq)
type FD = Int

data Cond
  = AtEOF
  -- current line == l
  | Line Int
  -- current line > l (tested after the first line has been processed)
  | EndLine Int
  -- Possible extension: explicit "match" registers to track several precomputed
  -- matches at once, and use that instead of MatchLastRE.
  -- A complication: pattern space may change but the last regexp is the same,
  -- so should repeat the match but optimize repeated match against unchanged
  -- pattern space elsewhere.
  -- I also think the last regexp is dynamic so we'd need to track a global for
  -- that similar to internal predicates and string variables.
  | Match SVar RE
  | MatchLastRE SVar
  | Bool Bool
  deriving (Show,Eq)
cTrue = Bool True
cFalse = Bool False

newtype SVar = SVar Int deriving (Ord,Eq)
data StringExpr
  = SConst S
  | SVarRef SVar
  | SHoldSpace (Maybe S)
  -- Subst last match against current pattern. See Match TODO about match regs.
  | SSubst SVar Replacement SubstType
  -- from to string
  | STrans S S SVar
  | SAppendNL SVar SVar
  deriving (Show,Eq)
emptyS = SConst ""

data Insn e x where
  Label         :: Label                    -> Insn C O
  Branch        :: Label                    -> Insn O C
  If            :: Pred -> Label -> Label   -> Insn O C
  Fork          :: Label -> Label           -> Insn O C
  Quit          :: ExitCode                 -> Insn O C
  -- for n and new cycle (which can accept incoming messages)
  -- labels are interrupt, line successfully read, EOF
  Cycle         :: FD -> Label -> Label -> Label -> Insn O C

  SetP          :: Pred -> Cond             -> Insn O O
  SetS          :: SVar -> StringExpr       -> Insn O O
  -- for n/N (which can never accept interrupts)
  Read          :: SVar -> FD               -> Insn O O
  PrintConstS   :: FD -> S                  -> Insn O O
  PrintLineNumber :: FD                     -> Insn O O
  PrintLiteral  :: Int -> FD -> SVar        -> Insn O O
  Print         :: FD -> SVar               -> Insn O O
  Message       :: SVar                     -> Insn O O

  -- TODO Map hold names to string variables here in IR?
  -- But initially:
  -- remove append forms
  -- Hold takes hold-name and string-var (not expression, to keep things simple)
  -- Get is replaced with SetS var (SHoldSpace ...)
  -- Exchange adds some temporaries
  Hold          :: (Maybe S) -> SVar        -> Insn O O
  Exchange      :: (Maybe S)                -> Insn O O

  SetLastRE     :: RE                       -> Insn O O

  ShellExec     ::                             Insn O O
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
  successors (Cycle _ i r e) = [i,r,e]

instance HooplNode Insn where
  mkBranchNode = Branch
  mkLabelNode = Label

data IRState = State
  { firstFreeUnique :: Unique
  , autoprint :: Bool
  , sourceLabels :: Map S Label
  , nextCycleLabels :: (Label, Label)
  , program :: Graph Insn O O
  }

nextCycleLabelNoPrint = snd . nextCycleLabels
nextCycleLabelPrint = fst . nextCycleLabels

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

invalidLabel :: String -> Label
invalidLabel s = error ("Invalid label: " ++ s)
startState autoprint = State firstNormalPred autoprint M.empty (dummyCycleLabel, dummyCycleLabel) emptyGraph
dummyCycleLabel = invalidLabel "uninitialized next-cycle label"

instance Show Pred where
  show (Pred 0) = "P{pre-first}"
  show (Pred 1) = "P{irq}"
  show (Pred 2) = "P{run-normal}"
  show (Pred 3) = "P{last-subst}"
  show (Pred 4) = "P{queued-output}"
  show (Pred 5) = "P{has-pattern}"
  show (Pred n) = "P" ++ show n

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
  show (SVar n) = "S" ++ show n

sPattern = SVar 0
sOutputQueue = SVar 1

instance UniqueMonad IRM where
  freshUnique = do
    res <- firstFreeUnique <$> get
    modify $ \state -> state { firstFreeUnique = res + 1 }
    return res

initBlock :: Label -> Graph Insn C O
initBlock l = mkLabel l

newLabel = freshLabel
newPred = Pred <$> freshUnique

newString :: IRM SVar
newString = SVar <$> freshUnique
setString :: SVar -> StringExpr -> IRM ()
setString s expr = emit (SetS s expr)
emitString :: StringExpr -> IRM SVar
emitString expr = newString >>= \s -> setString s expr >> return s
emitCString :: S -> IRM SVar
emitCString s = emitString (SConst s)

setPattern s = setString sPattern (SVarRef s) >> emit (SetP pHasPattern cTrue)

addLabelMapping name l = modify $
    \state -> state { sourceLabels = M.insert name l (sourceLabels state) }
getLabelMapping :: S -> IRM Label
getLabelMapping name = do
  res <- M.lookup name . sourceLabels <$> get
  case res of
    Just l -> return l
    Nothing -> withNewLabel (addLabelMapping name)

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
    ap <- autoprint <$> get
    when ap (emit (Print 0 sPattern))

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
    setString sOutputQueue emptyS
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
  doprint <- gets autoprint
  when doprint (tWhen pHasPattern (emit (Print 0 sPattern)))
  emit (SetP pHasPattern cFalse)
  newCycleNoPrint <- label
  checkQueuedOutput
  setLastSubst False
  line <- finishBlock' (Cycle 0 intr line exit)

  emit (SetP pIntr cFalse)
  emit (SetP pPreFirst cFalse)
  emit (SetP pRunNormal cTrue)
  emit (SetP pHasPattern cTrue)

  intr <- emitBranch' start

  emit (SetP pIntr cTrue)
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
                  p <- withNewPred $ \p -> emit (SetP p (EndLine n))
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

tCheck (AST.Line 0) = return pPreFirst
tCheck (AST.Line n) = withNewPred $ \p -> emit (SetP p (Line n))
tCheck (AST.Match (Just re)) = withNewPred $ \p -> do
    emit (SetP p (Match sPattern re))
    emit (SetLastRE re)
tCheck (AST.Match Nothing) = withNewPred $ \p -> emit (SetP p (MatchLastRE sPattern))
tCheck (AST.IRQ) = return pIntr
tCheck (AST.EOF) = withNewPred $ \p -> emit (SetP p AtEOF)

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
tCmd (AST.PrintLineNumber fd) = emit (PrintLineNumber fd)
tCmd (AST.PrintLiteral width) = tWhen pHasPattern $ emit (PrintLiteral width 0 sPattern)
tCmd (AST.Message Nothing) = tWhen pHasPattern $ emit (Message sPattern)
tCmd (AST.Message (Just s)) = do
    tmp <- emitCString s
    emit (Message tmp)
-- FIXME Wrong! "If there is no more input then sed exits without processing
-- any more commands." (How does read indicate EOF anyway?)
tCmd (AST.Next fd) = do
    checkQueuedOutput
    printIfAuto
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

tCmd (AST.Clear) = setString sPattern emptyS >> emit (SetP pHasPattern cFalse)
tCmd (AST.Change replacement) = do
    emit (PrintConstS 0 replacement)
    branchNextCycleNoPrint
tCmd (AST.Delete) = branchNextCycleNoPrint
tCmd (AST.Redirect dst (Just src)) = emit (Redirect dst src)
tCmd (AST.Redirect dst Nothing) = emit (CloseFile dst)
tCmd (AST.Subst mre sub flags actions) = do
  p <- tCheck (AST.Match mre)
  tIf p ifMatch (setLastSubst False)
  where
    ifMatch = do
        setLastSubst True
        s <- emitString (SSubst sPattern sub flags)
        setPattern s
        tSubstAction actions s
tCmd (AST.Trans from to) = do
    s <- emitString (STrans from to sPattern)
    setPattern s
tCmd (AST.Hold maybeReg) = emit (Hold maybeReg sPattern)
tCmd (AST.HoldA maybeReg) = do
    tmp <- emitString (SHoldSpace maybeReg)
    tmp2 <- emitString (SAppendNL tmp sPattern)
    emit (Hold maybeReg tmp2)
tCmd (AST.Get maybeReg) = setPattern =<< emitString (SHoldSpace maybeReg)
tCmd (AST.GetA maybeReg) = do
    tmp <- emitString (SHoldSpace maybeReg)
    tmp2 <- emitString (SAppendNL sPattern tmp)
    setString sPattern (SVarRef tmp2)
tCmd (AST.Exchange maybeReg) = do
    tmp <- emitString (SHoldSpace maybeReg)
    emit (Hold maybeReg sPattern)
    setString sPattern (SVarRef tmp)
tCmd (AST.Insert s) = emit (PrintConstS 0 s)
tCmd (AST.Append s) = do
    tIf pHasQueuedOutput ifTrue ifFalse
  where
    -- already set to true, so no need to update predicate. Just append to
    -- the queue.
    ifTrue = do
        temp <- emitCString s
        setString sOutputQueue (SAppendNL sOutputQueue temp)
    -- If there's no queued output yet, we know we can simply replace the
    -- queued output with a constant.
    ifFalse = do
        emit (SetP pHasQueuedOutput cTrue)
        setString sOutputQueue (SConst s)
tCmd (AST.WriteFile path) = emit (WriteFile path sPattern)
tCmd (AST.Quit print status) = () <$ do
  when print $ emit (Print 0 sPattern)
  finishBlock' (Quit status)
tCmd cmd = error ("tCmd: Unmatched case " ++ show cmd)

tSubstAction SActionNone _ = return ()
tSubstAction SActionExec _ = emit ShellExec
tSubstAction (SActionPrint n) res = emit (Print n res)
tSubstAction (SActionWriteFile path) res = emit (WriteFile path res)

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
