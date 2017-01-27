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

  AtEOF         :: Pred                     -> Insn O O
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

data IRState = State
  { firstFreeUnique :: Unique
  , firstFreePred :: Int
  , autoprint :: Bool
  , sourceLabels :: Map S Label
  , nextCycleLabel :: Label
  , program :: Graph Insn O O
  , cycleBlock :: BlockState
  , block :: BlockState
  }

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

invalidLabel :: String -> Label
invalidLabel s = error ("Invalid label: " ++ s)
startState autoprint = State 0 1 autoprint M.empty (invalidLabel "uninitialized next-cycle label") emptyGraph Block0 BlockN
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

  oldSourceLabels <- gets sourceLabels
  oldCycleBlock <- gets cycleBlock
  oldNextCycle <- gets nextCycleLabel

  modify $ \state -> state { nextCycleLabel = newCycle, cycleBlock = Block0, sourceLabels = M.empty }

  tSeds seds

  emitLabel newCycle
  get >>= \s -> when (autoprint s) (emit (Print 0))
  emit Clear
  doRead <- newLabel
  emit (AtEOF p0)
  If p0 exit doRead `thenLabel` doRead
  Read 0 (Just intr) entry `thenLabel` entry

  modify $ \state -> state { nextCycleLabel = newCycle, cycleBlock = BlockN, sourceLabels = M.empty }
  -- Actual normal program here
  tSeds seds

  Branch newCycle `thenLabel` intr

  modify $ \state -> state { nextCycleLabel = newCycle, cycleBlock = BlockI, sourceLabels = M.empty }
  tSeds seds

  Branch newCycle `thenLabel` exit

  modify $ \state -> state { nextCycleLabel = oldNextCycle, cycleBlock = oldCycleBlock, sourceLabels = oldSourceLabels }

tSeds = mapM_ tSed

withBlock b x = do
  oldBlock <- block <$> get
  modify $ \s -> s { block = b }
  cblock <- gets cycleBlock
  comment ("start of block " ++ show b ++ " in " ++ show cblock)
  x
  cblock <- gets cycleBlock
  comment ("end of block " ++ show b ++ " in " ++ show cblock)
  modify $ \s -> s { block = oldBlock }

blockForAddr AST.IRQ = BlockI
blockForAddr (AST.Line 0) = Block0
blockForAddr _ = BlockN

ifBlock b x = do
  block <- gets cycleBlock
  when (b == block) x
  when (b /= block) $ do
    comment ("wrong block " ++ show block ++ ", wanted " ++ show b)

ifRightBlock x = do
  b <- gets block
  ifBlock b x

withCond Always x = ifRightBlock x
withCond (At c) x = do
  block <- gets cycleBlock
  when (blockForAddr c == block) $ do
    f <- newLabel
    t <- newLabel
    tCheck p0 c
    finishBlock (If p0 t f) t
    withBlock (blockForAddr c) x
    emitLabel f
withCond (Between start end) x = ifBlock BlockN $ do
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

-- TODO Even in "block 0", this will stop being true if we read a line...
tCheck p (AST.Line 0) = do
  b <- gets cycleBlock
  emit (Set p (b == Block0))
tCheck p (AST.Line n) = emit (Line n p)
tCheck p (AST.Match (Just re)) = emit (Match re p) >> emit (SetLastRE re)
tCheck p (AST.Match Nothing) = emit (MatchLastRE p)
tCheck p addr = error ("tCheck: Unmatched case " ++ show addr)

tSed (Sed Always (AST.Block xs)) = tSeds xs
tSed (Sed cond (AST.Block xs)) = withCond cond $ tSeds xs
tSed (Sed cond x) = do
  cb <- gets cycleBlock
  comment ("In " ++ show cb ++ ", " ++ show cond ++ ": " ++ show x)
  withCond cond $ tCmd x

tCmd (AST.Block xs) = tSeds xs
tCmd (AST.Print fd) = emit (Print fd)
tCmd (AST.Next fd) = do
  printIfAuto
  next <- newLabel
  Read fd Nothing next `thenLabel` next
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
