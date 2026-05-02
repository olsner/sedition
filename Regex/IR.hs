{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, RecordWildCards #-}

module Regex.IR where

import Compiler.Hoopl as H

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as S

import Collections
import CharMap (CharMap)
import qualified CharMap as CM
-- Ideally, this module has no dependencies on TDFA.
import Regex.TDFA (RegId)
import Regex.TaggedRegex (TagId)

type R = RegId

data TagValue
  = Reg R Int      -- ^ Register value minus offset
  | NoTag          -- ^ Tag not set in this branch
  deriving (Show,Ord,Eq)

type Pos = (R, Int)

data Insn e x where
  Label         :: Label                    -> Insn C O

  -- If register points to the first character of the string, go to the first
  -- label otherwise go to the second. Note that this is different from whether
  -- the cursor is at its initial value, in the case of repeated searching.
  IfBOL         :: Label -> Label      -> Insn O C
  -- Match character at offset against label map, jump to matching label. For
  -- characters not in the label map, go to default-label instead.
  Switch        :: Int -> CharMap Label -> Label -> Insn O C
  -- Switch that does not need a default case.
  -- All switches could use this by augmenting them with missing entries, but
  -- then we'd want a corresponding transformation on the output side to e.g.
  -- use default for the most common target label.
  TotalSwitch   :: Int -> CharMap Label     -> Insn O C
  -- Definitely did not match.
  Fail          ::                             Insn O C
  -- Definitely did match. Argument maps tags to final registers, including the
  -- evaluation of fixed tags.
  Match         :: Map TagId TagValue       -> Insn O C
  -- If EOF is at or before Pos, i.e. if EOF is closer than n characters (0 =>
  -- at eof) from the given register, go to first label.
  -- Otherwise go to second label.
  CheckBounds   :: Int -> Label -> Label    -> Insn O C
  Branch        :: Label                    -> Insn O C

  Trace         :: String                   -> Insn O O
  -- TODO Add stats counters

  -- R := nil
  Clear         :: R                        -> Insn O O
  -- R1 := R2 + Offset (not valid for nil source registers)
  -- TODO May be unnecessary in the end.
  Set           :: R -> (R,Int)             -> Insn O O
  -- R1 := R2 (preserving nil)
  Copy          :: R -> R                   -> Insn O O

  -- Cursor := d
  MoveCursor    :: Int                      -> Insn O O
  -- R := Cursor + d
  SaveCursor    :: R -> Int                 -> Insn O O
  -- Cursor := R
  LoadCursor    :: R                        -> Insn O O

  -- Fallback and restore mechanism.
  -- Jump back to the last set fallback label. Must not be used before the first
  -- SetFallback. The entry point probably has a SetFallback that goes to Fail.
  Fallback      :: LabelSet                 -> Insn O C
  -- Set fallback to given label.
  SetFallback   :: Label                    -> Insn O O

deriving instance Show (Insn e x)
deriving instance Eq (Insn e x)
deriving instance Ord (Insn e x)

showInsn (Label l) = show l ++ ":"
showInsn i = "  " ++ show i

instance Show (Graph Insn e x) where
  show g = showGraph showInsn g

instance NonLocal Insn where
  entryLabel (Label l) = l
  successors (IfBOL l1 l2) = [l1, l2]
  successors (Branch l) = [l]
  successors (Switch _ cm l) = S.toList (S.insert l (CM.elemSet cm))
  successors (TotalSwitch _ cm) = S.toList (CM.elemSet cm)
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
    f (Set r (r2, _)) = setInsert r . setInsert r2
    f (Copy r r2) = setInsert r . setInsert r2
    f (Clear r) = setInsert r
    f (SaveCursor r _) = setInsert r
    f (LoadCursor r) = setInsert r
    f _ = id
