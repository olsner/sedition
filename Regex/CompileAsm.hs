{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}

module Regex.CompileAsm where

import Compiler.Hoopl as H

import Control.Monad

import qualified Data.ByteString.Char8 as C

--import Data.Map (Map)
import qualified Data.Map as M
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
-- import Data.List

import Debug.Trace

import qualified CharMap as CM
-- import CharMap (CharMap)

import Regex.Regex (Regex)
import qualified Regex.Regex as Regex

import Regex.IR as IR
import Regex.TaggedRegex hiding (EndOfMatch)
import Regex.TNFA (genTNFA)
import Regex.TDFA (genTDFA)
import Regex.Minimize (minimize)
import Regex.TDFA2IR (genIR)
import Regex.OptimizeIR (optimize)
import GenAsm

tagix (T t) = t
possibleTag (T t) = t < 20

tagoffs t = intDec (8 * tagix t)

-- TODO We should know which tags are set and not when we get to the exit? If
-- nothing else, at least sometimes this can be known from what was last set
-- for each register. This only runs once on exit though, so I would guess
-- that we still need the code for it.
matchFromTag (t,val) | possibleTag t = do
  comment (regA res0 <> " := " <> showB val)
  tagValue val res0
  comment ("tag " <> showB t)
  storeAddr (yymatch <> " + " <> tagoffs t) res0
                     | otherwise = trace "found an unoptimized tag that can't be used by match" mempty -- skip all impossible tags

tagValue :: IR.TagValue -> Reg -> Builder ()
tagValue (IR.Reg r d) res = do
  notSet <- newLabel
  isSet <- newLabel
  loadAddr (yyreg r) res
  jz res notSet
  sub (regA res) yybegin
  when (d > 0) $ sub (regA res) (intDec d)
  goto isSet
  label notSet
  setInt (-1) res
  label isSet

tagValue (EndOfMatch d) res = do
  copy yycursor (regA res)
  sub (regA res) yybegin
  when (d > 0) $ sub (regA res) (intDec d)

declareReg :: R -> Builder ()
declareReg r = label ("." <> showB r) <> op1 "resq" "1"

-- Tons of fun optimizations to do with switches:
-- 1. Avoid unnecessary tests based on things we've learned about the value
--    (enabler for doing "binary search" switches)
-- 2. Switch to jump tables at some number of comparisons/jumps
-- 3. Add/remove/change default label depending on how many cases there are
--    per label. Maybe convert all switches to total switches then make the
--    label with the largest number of cases (disjoint ranges) the "default".
--    (And make decisions on jump tables/number of tests after this
--    transformation/optimizations.)

emitCase :: Builder () -> (Char,Char) -> Builder ()
emitCase target (lb,ub)
    | lb == ub = do
        comment ("case " <> showB lb <> " => " <> target)
        op "cmp" [yychar, cchar lb] <> je target
    | otherwise  = do
        nomatch <- newLabel
        comment ("case " <> showB lb <> ".." <> showB ub <> " => " <> target)
        -- If the switch has a default (== holes in the ranges), we may need to
        -- check the lower bound if there was a hole. For now, always do this.
        -- Future: make a decision tree and track wisdom about checked ranges.
        -- Or even: lower to an IR that doesn't have switches and add dataflow
        -- optimization to it.
        when (lb > minBound) $ do
          op "cmp" [yychar, cchar lb]
          jb nomatch
        -- Should be done on a new IR so that the jump can be optimized later.
        when (fromEnum ub == 255) $ do
          goto target
        when (fromEnum ub < 255) $ do
          op "cmp" [yychar, cchar ub]
          jbe target
        label nomatch

emitCases :: ([(Char,Char)], Label) -> Builder ()
emitCases (cs, label) = foldMap (emitCase (lblname label)) cs

yychar = reg8 res0
yybegin = reg64 arg0 -- rdi
yycursor = reg64 arg1 -- rsi
yylimit = reg64 arg2 -- rdx
-- Seldomly used, probably don't need to be in registers.
fallbackLabel = arg3
fallbackCursor = regA arg4
yymatch = regA tmp0
yystring = regA tmp1
yyorigOffset = reg64 tmp2

yyreg r = ("." <> showB r)

-- Calling convention for matcher functions:
-- 
-- static bool FUN(match_t* m, string* s, const size_t orig_offset)
-- struct string { char* buf; size_t len; size_t alloc; };
-- typedef ptrdiff_t tags_t[20]
-- where match_t has an array of tags (with 20 entries)
-- orig_offset is > 0 when repeating a match for a global replace
--
-- Tags are "tX" (offsets in string), registers are "rX" (pointers in string).
--
-- Although it complicates things a bit in here (more goto spaghetti!), never
-- return directly but goto the end of the block, where the caller may have put
-- some before-return debugging code.
--
-- The variable 'bool result' should be set to the success (true = match) of
-- the regexp search.
--
-- Note use of uint8_t for pointers, this is necessary to get the correct
-- behavior for characters above 128 (and e.g. ranges like 0..255).
genAsm :: Program -> Builder ()
genAsm program@Program{..} = do
    when (not (null allRegs)) $ do
      section ".bss"
      foldMap declareReg allRegs
      section ".text"
    op "mov" [yymatch, regA arg0]
    op "mov" [yystring, regA arg1]
    op "mov" [yyorigOffset, reg64 arg2]
    -- Last use of yystring, probably?
    op "mov" [yybegin, mem (yystring <> " + " <> intDec stringBufOffset)]
    op "mov" [yylimit, yybegin]
    op "add" [yylimit, mem (yystring <> " + " <> intDec stringLenOffset)]
    op "lea" [yycursor, mem (yybegin <> " + " <> yyorigOffset)]
    comment "Jump to entry point"
    gotoL entryPoint
    comment "Basic blocks"
    postOrderFoldGraphNodes foldEmitInsn program mempty
    comment "Exit point"
    label ".end"
  where allRegs = setElems (IR.allRegs program)

tdfa2asm :: Maybe IntSet -> Regex -> C.ByteString
tdfa2asm used = toByteString .
    genAsm .
    -- TODO Allow controlling optimization fuel here, preferrably integrated in
    -- a way that lets you bisect both regex and Sed IR optimizations.
    fst . optimize 1000000 .
    genIR .
    minimize .
    genTDFA .
    genTNFA .
    fixTags .
    unusedTags .
    tagRegex
  where unusedTags | Just s <- used = selectTags (\(T t) -> t `IS.member` s)
                   | otherwise = id

isCompatible :: Regex -> Bool
isCompatible = Regex.tdfa2cCompatible

postOrderFoldGraphNodes ::
  forall a . Monoid a => (forall e x . Insn e x -> a -> a) -> Program -> a -> a
postOrderFoldGraphNodes f Program{..} e = foldMap f' (postorder_dfs g) e
  where g = mkLast (Branch entryPoint) H.|*><*| programGraph
        f' :: Block Insn e x -> IndexedCO e a a -> IndexedCO x a a
        f' = foldBlockNodesF f

foldEmitInsn :: Insn e x -> Builder () -> Builder ()
foldEmitInsn insn = (<> emitInsn insn)

-- TODO Way to avoid redundant branches:
--
-- 1. Track the fall-through target of the last emitted instruction.
-- 2. Track the set of emitted labels
-- 3. If the fall-through target has not been emitted yet, output it here
-- 4. Otherwise, output a jump instruction
--
-- Finally, output all remaining basic blocks (since they could be reachable
-- from indirect or conditional jumps).
--
-- If there are cases where a jump is dead (e.g. previous conditions are
-- complete), that should be optimized in the "Regex IR" level before we get
-- here.

emitInsn :: Insn e x -> Builder ()
emitInsn (Label l) = label (lblname l)

-- O C control flow
emitInsn (IfBOL tl fl) = do
  comment ("if BOL: " <> lblname tl <> " else: " <> lblname fl)
  cmp yycursor yybegin
  je (lblname tl)
  gotoL fl
emitInsn (Switch cm def) = do
  comment "Switch {"
  loadUInt8 yycursor res0
  foldMap emitCases (CM.toRanges cm)
  comment ("} End of switch, default = " <> lblname def)
  gotoL def
emitInsn (TotalSwitch cm) = do
  comment "Total switch {"
  loadUInt8 yycursor res0
  foldMap emitCases (CM.toRanges cm)
  comment "} End of total switch"
emitInsn Fail = comment "fail" <> setInt 0 res0 <> goto ".end"
emitInsn (Match tagMap) =
    comment ("Match: " <> showB tagMap) <>
    foldMap matchFromTag (M.toList tagMap) <>
    setInt 1 res0 <>
    goto ".end"
emitInsn (CheckBounds 1 eof cont) = do
  comment ("Need >= 1 char")
  cmp yylimit yycursor
  jbe (lblname eof)
  gotoL cont
emitInsn (CheckBounds n eof cont) = do
  comment ("Need >= " <> intDec n <> " chars")
  -- instead of yylimit < pos+n, test yylimit <= pos+(n-1) to allow one more
  -- case to fit in a byte-size offset. n > 1 (so n-1 > 0), since we already
  -- checked the 0 case above.
  setAddr (yycursor <> " + " <> intDec (n - 1)) res0
  cmp yylimit (regA res0)
  jbe (lblname eof)
  gotoL cont
emitInsn (Branch l) = gotoL l

-- O O debugging
emitInsn (Trace msg) = comment (string8 msg)
-- O O primitives
emitInsn Next = inc yycursor
emitInsn (Set r) = do
  comment (showB r <> " := YYCURSOR")
  op "mov" [mem (yyreg r), yycursor]
emitInsn (Clear r) = do
  comment (showB r <> " := nullptr")
  op "mov" [qword_ptr (yyreg r), "0"]
emitInsn (Copy r r2) = do
  comment (showB r <> " := " <> showB r2)
  -- r := r2
  loadAddr (yyreg r2) res0
  storeAddr (yyreg r) res0

-- O O fallback operations
emitInsn (Fallback _) = goto (regA fallbackLabel)
emitInsn (SetFallback l) = setAddr (lblname l) fallbackLabel
emitInsn SaveCursor = copy yycursor fallbackCursor
emitInsn RestoreCursor = copy fallbackCursor yycursor
