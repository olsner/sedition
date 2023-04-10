{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, RecordWildCards #-}

module Regex.IR where

import Compiler.Hoopl as H

import Data.Map (Map)
import qualified Data.Set as S

import Collections
import CharMap (CharMap)
import qualified CharMap as CM
-- Ideally, this module has no dependencies on TDFA.
import Regex.TDFA (RegId)
import Regex.TaggedRegex (TagId)

type R = RegId

data TagValue
    = EndOfMatch Int  -- ^ Current position / end of match, minus offset
    | Reg R Int       -- ^ Register value minus offset
    deriving (Show,Ord,Eq)

data Insn e x where
  Label         :: Label                    -> Insn C O

  -- If we're on the first character of the line, go to the first label
  -- otherwise go to the second.
  IfBOL         :: Label -> Label           -> Insn O C
  -- Match current character against label map, jump to matching label.
  -- For characters not in the label map, go to fallback label instead.
  Switch        :: CharMap Label -> Label   -> Insn O C
  -- Definitely did not match.
  Fail          ::                             Insn O C
  -- Definitely did match. Argument maps tags to final registers, including the
  -- evaluation of fixed tags.
  Match         :: Map TagId TagValue       -> Insn O C
  -- If EOF is closer than n characters (0 => at eof), go to first label.
  -- Otherwise go to second label.
  CheckBounds   :: Int -> Label -> Label    -> Insn O C
  Branch        :: Label                    -> Insn O C

  Trace         :: String                   -> Insn O O
  -- TODO Add stats counters

  -- Read next character from string into current-character register. Must not
  -- be called without bounds check somewhere before it.
  Next          ::                             Insn O O
  -- R := current position (TODO specify better - positions have been off by
  -- one in every direction twice)
  Set           :: R                        -> Insn O O
  -- R := nil
  Clear         :: R                        -> Insn O O
  -- R1 := R2
  Copy          :: R -> R                   -> Insn O O

  -- Fallback and restore mechanism.
  -- Jump back to the last set fallback label. Must not be used before the first
  -- SetFallback. The entry point probably has a SetFallback that goes to Fail.
  Fallback      :: LabelSet                 -> Insn O C
  -- Set fallback to given label.
  SetFallback   :: Label                    -> Insn O O
  -- This is done separately to allow fallback to at least sometimes be
  -- optimized out to a direct branch.
  SaveCursor    ::                             Insn O O
  RestoreCursor ::                             Insn O O

deriving instance Show (Insn e x)
deriving instance Eq (Insn e x)

showInsn (Label l) = show l ++ ":"
showInsn i = "  " ++ show i

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

instance NonLocal Insn where
  entryLabel (Label l) = l
  successors (IfBOL l1 l2) = [l1, l2]
  successors (Branch l) = [l]
  successors (Switch cm l) = S.toList (S.insert l (CM.elemSet cm))
  successors Fail = []
  successors (Match _) = []
  successors (CheckBounds _ eof cont) = [eof, cont]
  successors (Fallback ls) = setElems ls

instance HooplNode Insn where
  mkBranchNode = Branch
  mkLabelNode = Label

data Program = Program { entryPoint :: Label,
                         programGraph :: Graph Insn C C }
  deriving (Show)

finishProgram :: Label -> Graph Insn C C -> Program
finishProgram e g = Program e (updateFallbackLabels g)

updateFallbackLabels g = mapGraph f g
  where
    f :: Insn e x -> Insn e x
    f (Fallback _) = Fallback fallbacks
    f insn = insn
    fallbacks = usedFallbackLabels g

usedFallbackLabels :: Graph Insn C C -> LabelSet
usedFallbackLabels g = foldGraphNodes f g setEmpty
  where
    f :: Insn e x -> LabelSet -> LabelSet
    f (SetFallback l) s = setInsert l s
    f _ s = s

allRegs :: Program -> RegSet
allRegs Program{..} = foldGraphNodes f programGraph setEmpty
  where
    f :: Insn e x -> RegSet -> RegSet
    f (Set r) = setInsert r
    f (Clear r) = setInsert r
    f (Copy r1 r2) = setInsert r1 . setInsert r2
    f _ = id
