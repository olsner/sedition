{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving #-}

module IR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

import System.Exit

import Parser

import AST hiding (Cmd(..), Address(..), Label(..))
import qualified AST

newtype Pred = Pred Int deriving (Show,Ord,Eq)
type FD = Int

data Insn e x where
  Label         :: Label                    -> Insn C O
  Branch        :: Label                    -> Insn O C
  If            :: Pred -> Label -> Label   -> Insn O C
  Fork          :: Label -> Label           -> Insn O C
  Quit          :: ExitCode                 -> Insn O C
  -- for n and new cycle (which can accept incoming messages)
  Read          :: FD -> (Maybe Label) -> Label -> Insn O C

  Set           :: Pred -> Bool             -> Insn O O
  -- Clear pattern space
  Clear         ::                             Insn O O
  -- for N (which can never accept interrupts)
  ReadAppend    :: FD                       -> Insn O O
  Print         :: FD                       -> Insn O O
  PrintS        :: FD -> S                  -> Insn O O

  Hold          :: (Maybe S)                -> Insn O O
  HoldA         :: (Maybe S)                -> Insn O O
  Get           :: (Maybe S)                -> Insn O O
  GetA          :: (Maybe S)                -> Insn O O

  -- TODO Add instruction for incrementing the line number when starting a new
  -- cycle. Or is the line number incremented on read?
  -- TODO Add EOF check instruction
  -- Any read for file descriptor 0 would increment it.
  Line          :: Int -> Pred              -> Insn O O
  -- Possible extension: explicit "match" registers to track several precomputed
  -- matches at once.
  Match         :: RE -> Pred               -> Insn O O
  SetLastRE     :: RE                       -> Insn O O
  MatchLastRE   :: Pred                     -> Insn O O
  -- Subst last match against current pattern. See Match TODO about match regs.
  Subst         :: S -> SubstType           -> Insn O O

  ShellExec     ::                             Insn O O
  Listen        :: Int -> (Maybe S) -> Int  -> Insn O O
  Accept        :: Int -> Int               -> Insn O O
  Redirect      :: Int -> Int               -> Insn O O
  CloseFile     :: Int                      -> Insn O O
  Comment       :: String                   -> Insn O O

deriving instance Show (Insn e x)

showInsn (Label l) = show l ++ ":"
showInsn i = "  " ++ show i

instance NonLocal Insn where
  entryLabel (Label l) = l
  successors (Branch t) = [t]
  successors (If _ t f) = [t,f]
  successors (Fork t c) = [t,c]
  successors (Read _ (Just i) r) = [i,r]
  successors (Read _ Nothing r) = [r]

instance HooplNode Insn where
  mkBranchNode = Branch
  mkLabelNode = Label

data Cycle = PreFirstCycle | NormalCycle | InterruptCycle

data IRState = State
  { firstFreeUnique :: Unique
  , firstFreePred :: Int
  , autoprint :: Bool
  , sourceLabels :: Map S Label
  , nextCycleLabel :: Label
  , program :: Graph Insn O O
  }

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

invalidLabel :: String -> Label
invalidLabel s = error ("Invalid label: " ++ s)
startState autoprint = State 0 1 autoprint M.empty (invalidLabel "uninitialized next-cycle label") emptyGraph
p0 = Pred 0

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

addLabelMapping name l = modify $
    \state -> state { sourceLabels = M.insert name l (sourceLabels state) }
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

comment s = emit (Comment s)

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
  tCheck p0 c
  tIf p0 tx fx

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
  modify $ \state -> state { nextCycleLabel = newCycle }

  -- tSeds PreFirstCycle seds

  emitLabel newCycle
  get >>= \s -> when (autoprint s) (emit (Print 0))
  emit Clear
  -- TODO EOF -> exit
  Read 0 (Just intr) entry `thenLabel` entry

  -- Actual normal program here
  tSeds NormalCycle seds

  Branch newCycle `thenLabel` intr

  -- Interrupt handling here
  -- tSeds InterruptCycle seds

  Branch newCycle `thenLabel` exit

  modify $ \state -> state { nextCycleLabel = invalidLabel "end of program" }

-- May need more state: I-block or 0-block for instance
tSeds cycle = mapM_ tSed

withCond Always x = x
withCond (At c) x = do
  -- Check if `c` should update block state, compare with cycle from state
  f <- newLabel
  t <- newLabel
  tCheck p0 c
  finishBlock (If p0 t f) t
  x
  emitLabel f
withCond (Between start end) x = do
  pActive <- newPred
  f <- newLabel
  t <- newLabel

  let run = emitBranch' t
      skip = emitBranch' f
      set = emit (Set pActive True)
      clear = emit (Set pActive False)

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

tCheck p (AST.Line n) = emit (Line n p)
-- TODO Translate last-expression into something explicit
tCheck p (AST.Match (Just re)) = emit (Match re p) >> emit (SetLastRE re)
tCheck p (AST.Match Nothing) = emit (MatchLastRE p)
tCheck p addr = error ("tCheck: Unmatched case " ++ show addr)

-- TODO track I-block and 0-block state like the interpreter does
tSed (Sed cond x) = withCond cond $ tCmd x

tCmd (AST.Block xs) = tSeds NormalCycle xs
tCmd (AST.Print fd) = emit (Print fd)
tCmd (AST.Next fd) = do
  printIfAuto
  next <- newLabel
  Read fd Nothing next `thenLabel` next
tCmd (AST.NextA fd) = printIfAuto >> emit (ReadAppend fd)
tCmd (AST.Listen fd host port) = emit (Listen fd host port)
tCmd (AST.Accept sfd fd) = emit (Accept sfd fd)
tCmd (AST.Label name) = emitLabel =<< getLabelMapping name
tCmd (AST.Branch (Just name)) = emitBranch' =<< getLabelMapping name
tCmd (AST.Branch Nothing) = branchNextCycle
tCmd (AST.Fork sed) = do
  exit <- newLabel
  entry <- newLabel

  Fork exit entry `thenLabel` entry

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
  tCheck p0 (AST.Match mre)
  tIf p0 (emit (Subst sub flags) >> tSubstAction actions) (return ())
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
