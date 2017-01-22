module IR where

import Parser

import AST hiding (Cmd(..), Address(..), Label(..))
import qualified AST

import Control.Monad
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.RWS.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

newtype Label = Label Int deriving (Show,Ord,Eq)
newtype Pred = Pred Int deriving (Show,Ord,Eq)
type FD = Int

data SedIR =
    Branch Label
  | If Pred Label Label
  | Set Pred Bool
  | Clear -- pattern space
  -- for n and new cycle (which can accept incoming messages)
  | Read FD (Maybe Label)
  -- for N (which can never accept interrupts)
  | ReadAppend FD
  | Print FD
  | PrintS FD S

  | Hold (Maybe S)
  | HoldA (Maybe S)
  | Get (Maybe S)
  | GetA (Maybe S)

  -- TODO Add instruction for incrementing the line number when starting a new
  -- cycle. Or is the line number incremented on read?
  -- Any read for file descriptor 0 would increment it.
  | Line Int Pred
  -- Possible extension: explicit "match" registers to track several precomputed
  -- matches at once.
  | Match RE Pred
  | SetLastRE RE
  | MatchLastRE Pred
  -- Subst last match against current pattern. See Match TODO about match regs.
  | Subst S SubstType

  | ShellExec
  | Listen Int (Maybe S) Int
  | Accept Int Int
  | Redirect Int Int
  | CloseFile Int

  | Fork Label
  deriving (Show,Ord,Eq)

data State = State
  { firstFreeLabel :: Int
  , firstFreePred :: Int
  , autoprint :: Bool
  , sourceLabels :: Map S Label
  , nextCycleLabel :: Label
  } deriving (Show,Ord,Eq)

invalidLabel :: String -> Label
invalidLabel s = error ("Invalid label: " ++ s)
startState autoprint = State 0 1 autoprint M.empty (invalidLabel "uninitialized next-cycle label")
p0 = Pred 0
-- Might need next-cycle label

newLabel :: Monoid w => RWS r w State Label
newLabel = do
  res <- firstFreeLabel <$> get
  modify $ \state -> state { firstFreeLabel = res + 1 }
  return (Label res)

newPred :: Monoid w => RWS r w State Pred
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

emitLabel l = tell [Left l]
emitNewLabel = do
  l <- newLabel
  emitLabel l
  return l
emit c = tell [Right c]
emitBranch l = emit (Branch l)
branchNextCycle = do
  l <- nextCycleLabel <$> get
  emitBranch l

printIfAuto = do
    ap <- autoprint <$> get
    when ap (emit (Print 0))

tIf p tx fx = do
    f <- newLabel
    t <- newLabel
    e <- newLabel
    emit (If p t f)
    emitLabel t
    tx
    emitBranch e
    emitLabel f
    fx
    emitLabel e

ifCheck c tx fx = do
  tCheck p0 c
  tIf p0 tx fx

blocky :: Label -> [Either Label SedIR] -> (Label, Map Label [SedIR])
blocky entry code = (entry, S.execState (go entry [] code) M.empty)
  where
    finish label acc = S.modify $ \s -> M.insert label (reverse acc) s
    -- TODO Track exit labels to avoid inserting redundant branches
    go label acc [] = finish label acc
    go label acc (x:xs) =
      case x of
        Left l -> finish label (Branch l:acc) >> go l [] xs
        Right r -> go label (r:acc) xs

-- TODO Post-process into labelled basic blocks
toIR' :: Bool -> [Sed] -> (Label, [Either Label SedIR])
toIR' autoprint seds = evalRWS (tProgram seds) M.empty (startState autoprint)

toIR autoprint seds = uncurry blocky (toIR' autoprint seds)

-- Returns the entry-point label (pre-first line) of the sed program.
--
-- Entry points to generate:
-- * pre-first line code (if any)
-- * interrupt reception (for new-cycle code)
-- * new cycle label
tProgram seds = do
  newCycle <- newLabel
  modify $ \state -> state { nextCycleLabel = newCycle }
  entry <- emitNewLabel
  -- TODO Emit pre-first line separately
  tSeds seds
  emitLabel newCycle
  get >>= \s -> when (autoprint s) (emit (Print 0))
  emit Clear
  -- TODO Add interrupt handler
  emit (Read 0 Nothing)
  emitBranch entry
  modify $ \state -> state { nextCycleLabel = invalidLabel "end of program" }
  return entry

-- May need more state: I-block or 0-block for instance
tSeds = mapM_ tSed

withCond Always x = x
withCond (At c) x = do
  f <- newLabel
  t <- newLabel
  tCheck p0 c
  emit (If p0 t f)
  emitLabel t
  x
  emitLabel f
withCond (Between start end) x = do
  pActive <- newPred
  f <- newLabel
  t <- newLabel

  let run = emitBranch t
      skip = emitBranch f
      set = emit (Set pActive True)
      clear = emit (Set pActive False)

  tIf pActive (ifCheck end (clear >> run) run)
              (ifCheck start (set >> run) skip)

  emitLabel t
  x
  emitLabel f

tCheck p (AST.Line n) = emit (Line n p)
-- TODO Translate last-expression into something explicit
tCheck p (AST.Match (Just re)) = emit (Match re p) >> emit (SetLastRE re)
tCheck p (AST.Match Nothing) = emit (MatchLastRE p)
tCheck p addr = error ("Unmatched case " ++ show addr)

-- TODO track I-block and 0-block state like the interpreter does
tSed (Sed cond x) = withCond cond $ tCmd x

tCmd (AST.Block xs) = tSeds xs
tCmd (AST.Print fd) = emit (Print fd) >> emit Clear
tCmd (AST.Next fd) = printIfAuto >> emit (Read fd Nothing)
tCmd (AST.NextA fd) = printIfAuto >> emit (ReadAppend fd)
tCmd (AST.Listen fd host port) = emit (Listen fd host port)
tCmd (AST.Accept sfd fd) = emit (Accept sfd fd)
tCmd (AST.Label name) = emitLabel =<< getLabelMapping name
tCmd (AST.Branch (Just name)) = emitBranch =<< getLabelMapping name
tCmd (AST.Branch Nothing) = branchNextCycle
tCmd (AST.Fork sed) = do
  skip <- newLabel
  emitBranch skip
  oldNextCycle <- nextCycleLabel <$> get
  forked <- tProgram [sed]
  modify $ \state -> state { nextCycleLabel = oldNextCycle }
  emitLabel skip
  emit (Fork forked)
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
tCmd cmd = error ("Unmatched case " ++ show cmd)

tSubstAction SActionNone = return ()
tSubstAction SActionExec = emit ShellExec
tSubstAction (SActionPrint n) = emit (Print n)
