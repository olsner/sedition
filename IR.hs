{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP #-}

#define DEBUG 0

module IR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M

import System.Exit

import AST hiding (Cmd(..), Address(..), Label)
import qualified AST

newtype Pred = Pred Int deriving (Ord,Eq)
type FD = Int

data Cond
  = AtEOF
  | Line Int
  -- Possible extension: explicit "match" registers to track several precomputed
  -- matches at once.
  | Match RE
  | MatchLastRE
  | Bool Bool
  deriving (Show,Eq)
cTrue = Bool True
cFalse = Bool False

data Insn e x where
  Label         :: Label                    -> Insn C O
  Branch        :: Label                    -> Insn O C
  If            :: Pred -> Label -> Label   -> Insn O C
  Fork          :: Label -> Label           -> Insn O C
  Quit          :: ExitCode                 -> Insn O C
  -- for n and new cycle (which can accept incoming messages)
  -- labels are interrupt, line successfully read, EOF
  Cycle         :: FD -> Label -> Label -> Label -> Insn O C

  Set           :: Pred -> Cond             -> Insn O O
  -- Clear pattern space
  Clear         ::                             Insn O O
  -- for N (which can never accept interrupts)
  Read          :: FD                       -> Insn O O
  ReadAppend    :: FD                       -> Insn O O
  Print         :: FD                       -> Insn O O
  PrintS        :: FD -> S                  -> Insn O O
  Message       :: (Maybe S)                -> Insn O O

  Hold          :: (Maybe S)                -> Insn O O
  HoldA         :: (Maybe S)                -> Insn O O
  Get           :: (Maybe S)                -> Insn O O
  GetA          :: (Maybe S)                -> Insn O O

  SetLastRE     :: RE                       -> Insn O O
  -- Subst last match against current pattern. See Match TODO about match regs.
  Subst         :: S -> SubstType           -> Insn O O

  ShellExec     ::                             Insn O O
  Listen        :: Int -> (Maybe S) -> Int  -> Insn O O
  Accept        :: Int -> Int               -> Insn O O
  Redirect      :: Int -> Int               -> Insn O O
  CloseFile     :: Int                      -> Insn O O
  Comment       :: String                   -> Insn O O

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
  , nextCycleLabel :: Label
  , program :: Graph Insn O O
  }

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

invalidLabel :: String -> Label
invalidLabel s = error ("Invalid label: " ++ s)
startState autoprint = State 3 autoprint M.empty (invalidLabel "uninitialized next-cycle label") emptyGraph

instance Show Pred where
  show (Pred 0) = "P{pre-first}"
  show (Pred 1) = "P{irq}"
  show (Pred 2) = "P{run-normal}"
  show (Pred n) = "P" ++ show n

pPreFirst = Pred 0
pIntr = Pred 1
pRunNormal = Pred 2

instance UniqueMonad IRM where
  freshUnique = do
    res <- firstFreeUnique <$> get
    modify $ \state -> state { firstFreeUnique = res + 1 }
    return res

initBlock :: Label -> Graph Insn C O
initBlock l = mkLabel l

newLabel = freshLabel
newPred = Pred <$> freshUnique

addLabelMapping name l = modify $
    \state -> state { sourceLabels = M.insert name l (sourceLabels state) }
getLabelMapping :: S -> IRM Label
getLabelMapping name = do
  res <- M.lookup name . sourceLabels <$> get
  case res of
    Just l -> return l
    Nothing -> do
      l <- newLabel
      addLabelMapping name l
      return l

emitOCO :: Insn O C -> Insn C O -> IRM ()
emitOCO last first =
    modify $ \s -> s { program = program s H.<*> mkLast last |*><*| mkFirst first }

thenLabel :: Insn O C -> Label -> IRM ()
thenLabel last next = emitOCO last (Label next)

finishBlock = thenLabel
finishBlock' b = newLabel >>= finishBlock b

emit :: Insn O O -> IRM ()
emit insn =
    modify $ \s -> s { program = program s H.<*> mkMiddle insn }

comment :: String -> IRM ()
#if DEBUG
comment s = emit (Comment s)
#else
comment _ = return ()
#endif

emitBranch' l = newLabel >>= emitBranch l
emitBranch l next = Branch l `thenLabel` next
branchNextCycle = emitBranch' =<< nextCycleLabel <$> get

emitLabel l = Branch l `thenLabel` l

printIfAuto = do
    ap <- autoprint <$> get
    when ap (emit (Print 0))

-- emitIf branch th el = graphFromAGraph (mkIfThenElse branch th el)

tIf p tx fx = do
    f <- newLabel
    t <- newLabel
    e <- newLabel
    finishBlock (If p t f) t
    comment "tIf/true"
    tx
    emitBranch e f
    comment "tIf/false"
    fx
    emitLabel e
    comment "tIf/end"

ifCheck c tx fx = do
  p <- tCheck c
  tIf p tx fx

type IRM = State IRState

toIR :: Bool -> [Sed] -> Graph Insn O C
toIR autoprint seds = program (execState (tProgram seds) (startState autoprint)) H.<*> mkLast (Quit ExitSuccess)

-- Returns the entry-point label (pre-first line) of the sed program.
--
-- Entry points to generate:
-- * pre-first line code (if any)
-- * interrupt reception (for new-cycle code)
-- * new cycle label
tProgram seds = do
  entry <- newLabel
  newCycle <- newLabel
  intr <- newLabel
  exit <- newLabel

  oldNextCycle <- gets nextCycleLabel

  modify $ \state -> state { nextCycleLabel = newCycle }
  emit (Set pPreFirst cTrue)
  emit (Set pRunNormal cFalse)
  emitLabel entry
  -- Actual normal program here
  tSeds seds

  emitLabel newCycle
  emit (Set pRunNormal cTrue)
  emit (Set pPreFirst cFalse)
  emit (Set pIntr cFalse)
  get >>= \s -> when (autoprint s) (emit (Print 0))
  Cycle 0 intr entry exit `thenLabel` intr

  emit (Set pIntr cTrue)
  emit (Set pRunNormal cFalse)

  Branch entry `thenLabel` exit

  modify $ \state -> state { nextCycleLabel = oldNextCycle }

tSeds = mapM_ tSed

tWhenNot :: Pred -> IRM () -> IRM ()
tWhenNot p x = do
  t <- newLabel
  f <- newLabel
  If p t f `thenLabel` f
  x
  emitLabel t

tWhen p x = do
  t <- newLabel
  f <- newLabel
  If p t f `thenLabel` t
  x
  emitLabel f

withCond Always x = x
withCond (At c) x = do
  f <- newLabel
  t <- newLabel
  p <- tCheck c
  finishBlock (If p t f) t
  x
  emitLabel f
withCond (Between start end) x = do
  pActive <- newPred
  f <- newLabel
  t <- newLabel

  let run = emitBranch' t
      skip = emitBranch' f
      set = emit (Set pActive cTrue)
      clear = emit (Set pActive cFalse)

  tIf pActive (do comment "between/active"
                  ifCheck end (do comment "between/last"
                                  clear
                                  run) run)
              (do comment "between/inactive"
                  ifCheck start (comment "between/first" >> set >> run) skip)

  emitLabel t
  x
  comment "between/end of code"
  emitLabel f

withNewPred f = newPred >>= \p -> f p >> return p

tCheck (AST.Line 0) = return pPreFirst
tCheck (AST.Line n) = withNewPred $ \p -> emit (Set p (Line n))
tCheck (AST.Match (Just re)) = withNewPred $ \p -> do
    emit (Set p (Match re))
    emit (SetLastRE re)
tCheck (AST.Match Nothing) = withNewPred $ \p -> emit (Set p MatchLastRE)
tCheck (AST.IRQ) = return pIntr
tCheck addr = error ("tCheck: Unmatched case " ++ show addr)

tSed (Sed Always (AST.Block xs)) = tSeds xs
tSed (Sed cond@(At (AST.Line 0)) x) = withCond cond $ do
  -- While running a 0-conditional line, also run all normal lines until we
  -- either reach the "fall-through" from that line, or until we start a new
  -- cycle, then reset it back to... its original value, hmm...
  emit (Set pRunNormal cTrue)
  tCmd x
  -- FIXME This may need to keep a counter or something rather than just set
  -- to false. Or assign a fresh predicate to push/copy the value into?
  emit (Set pRunNormal cFalse)
tSed (Sed cond@(At AST.IRQ) x) = withCond cond $ do
  -- While running a 0-conditional line, also run all normal lines until we
  -- either reach the "fall-through" from that line, or until we start a new
  -- cycle, then reset it back to... its original value, hmm...
  emit (Set pRunNormal cTrue)
  tCmd x
  -- FIXME This may need to keep a counter or something rather than just set
  -- to false. Or assign a fresh predicate to push/copy the value into?
  emit (Set pRunNormal cFalse)
tSed (Sed cond x) = tWhen pRunNormal $ withCond cond $ tCmd x

tCmd (AST.Block xs) = tSeds xs
tCmd (AST.Print fd) = emit (Print fd)
tCmd (AST.Message m) = emit (Message m)
-- FIXME Wrong! "If there is no more input then sed exits without processing
-- any more commands."
tCmd (AST.Next fd) = do
  printIfAuto
  emit (Read fd)
tCmd (AST.NextA fd) = printIfAuto >> emit (ReadAppend fd)
tCmd (AST.Listen fd host port) = emit (Listen fd host port)
tCmd (AST.Accept sfd fd) = emit (Accept sfd fd)
tCmd (AST.Label name) = do
  emitLabel =<< getLabelMapping name
  comment ("at label " ++ show name)
tCmd (AST.Branch (Just name)) = do
  comment ("branch " ++ show name)
  emitBranch' =<< getLabelMapping name
tCmd (AST.Branch Nothing) = branchNextCycle
tCmd (AST.Fork sed) = do
  exit <- newLabel
  entry <- newLabel

  Fork entry exit `thenLabel` entry

  oldNextCycle <- nextCycleLabel <$> get
  tProgram [sed]
  modify $ \state -> state { nextCycleLabel = oldNextCycle }

  -- End of thread (quit)
  Quit ExitSuccess `thenLabel` exit

tCmd (AST.Delete) = branchNextCycle
tCmd (AST.Clear) = emit Clear
tCmd (AST.Redirect dst (Just src)) = emit (Redirect dst src)
tCmd (AST.Redirect dst Nothing) = emit (CloseFile dst)
tCmd (AST.Subst mre sub flags actions) = do
  p <- tCheck (AST.Match mre)
  tIf p (emit (Subst sub flags) >> tSubstAction actions) (return ())
tCmd (AST.Hold maybeReg) = emit (Hold maybeReg)
tCmd (AST.Get maybeReg) = emit (Get maybeReg)
tCmd (AST.GetA maybeReg) = emit (GetA maybeReg)
tCmd (AST.Insert s) = emit (PrintS 0 s)
-- TODO append ('a'/'A') needs to save data to be printed at the start of the
-- next cycle (or the end of this one).
tCmd (AST.Quit print status) = do
  when print $ emit (Print 0)
  finishBlock' (Quit status)
tCmd cmd = error ("tCmd: Unmatched case " ++ show cmd)

tSubstAction SActionNone = return ()
tSubstAction SActionExec = emit ShellExec
tSubstAction (SActionPrint n) = emit (Print n)
