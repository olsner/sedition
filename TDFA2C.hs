{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module TDFA2C where

import Control.Monad.Trans.State.Strict

import Data.ByteString.Builder as B
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy.Char8 as L

import qualified CharMap as CM
import CharMap (CharMap)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Data.List
import Data.Maybe
import Data.Word

import Debug.Trace

import Regex (Regex)
import qualified Regex

import TaggedRegex
import TNFA
import SimulateTNFA
import TDFA

-- TODO Extract utility module to share with Compile...
showB x = string8 (show x)
stmt builder = builder <> ";\n"
comment builder = "// " <> builder <> "\n"

label name = string8 name <> ":\n"
goto name = stmt ("goto " <> string8 name)

decstate s = label (show s)
gostate s = goto (show s)

cchar = showB . fromEnum

-- Since back references are single-digit, only the first 20 tags can be
-- output.
-- TODO Do this as part of previus optimizations. Will be automatic when we
-- track used groups since impossible tags cannot be used then.
possibleTag (T t) = t < 20

fixedTag (t, f) = stmt (showB t <> " = " <> g f)
  where
    g (EndOfMatch dist) = "YYPOS - " <> showB dist
    g (FixedTag t2 dist) = showB t2 <> " - " <> showB dist

matchix (T t) = showB (t `div` 2)
matchfld (T t) | even t = "rm_so"
               | otherwise = "rm_eo"

matchFromTag t | possibleTag t =
  stmt ("m->matches[" <> matchix t <> "]." <> matchfld t <> " = " <> showB t)
               | otherwise = trace "found an unoptimized tag that can't be used by match" mempty -- skip all impossible tags

setTagFromReg (t, r) = stmt (showB t <> " = " <>
    showB r <> " ? " <> showB r <> " - s->buf : -1")

declareTagVar t = stmt ("regoff_t " <> showB t <> " = -1")
declareReg r = stmt ("const char* " <> showB r <> " = NULL")

emitCase (min,max)
    | min == max = " case " <> cchar min <> ":\n"
    | otherwise  = " case " <> cchar min <> " ... " <> cchar max <> ":\n"

emitRegOp (r,SetReg val) = stmt ("  " <> showB r <> " = " <> g val)
  where
    g Pos = "YYCURSOR - 1" -- cases run after incrementing YYCURSOR
    g Nil = "NULL"
emitRegOp (r,CopyReg r2) = stmt ("  " <> showB r <> " = " <> showB r2)

emitTrans (cs, (s', regops)) =
    foldMap emitCase cs <> "{\n" <>
    foldMap emitRegOp regops <>
    "  " <> gostate s' <>
    "}\n"

emitState TDFA{..} s =
    decstate s <>
    stmt ("YYNEXT(" <> string8 endLabel <> ")") <>
    "switch (YYCHAR) {\n" <>
    foldMap emitTrans trans <>
    -- TODO Don't emit "default" label if cases cover all possible values.
    " default: goto fail;\n" <>
    "}\n" <>
    (if isFinalState then finalRegOps else mempty)
  where
    trans = CM.toRanges $ M.findWithDefault CM.empty s tdfaTrans
    isFinalState = S.member s tdfaFinalStates
    endLabel = if isFinalState then matchLabelName else "fail"
    matchLabelName = "matched_" <> show s
    finalRegOps =
        label matchLabelName <>
        foldMap emitRegOp (M.findWithDefault [] s tdfaFinalFunction) <>
        goto "match"

-- Calling convention for matcher functions:
-- 
-- static void FUN(match_t* m, string* s, size_t offset)
-- struct string { char* buf; size_t len; size_t alloc; };
-- struct match_t { bool result; regmatch_t matches[]; }
-- where regmatch_t has rm_so and rm_eo, corresponding to the even/odd tag
--
-- Will probably emulate re2c a bit with YY* variables to track position.
--
-- Tags are "tX" (offsets in string), registers are "rX" (pointers in string).
genC :: TDFA -> B.Builder
genC tdfa@TDFA{..} =
    stmt ("const char *const YYBEGIN = s->buf + offset") <>
    stmt ("const char *const YYLIMIT = s->buf + s->len") <>
    stmt ("const char *YYCURSOR = YYBEGIN") <>
    stmt ("unsigned char YYCHAR = 0") <>
    "#define YYPOS (YYCURSOR - YYBEGIN)\n" <>
    "#define YYNEXT(endlabel) do { \\\n" <>
    "   if (YYCURSOR >= YYLIMIT) goto endlabel; \\\n" <>
    "   else YYCHAR = *YYCURSOR++; \\\n" <>
    "  } while (0)\n" <>
    foldMap declareTagVar (S.toList allTags) <>
    foldMap declareReg allRegs <>
    stmt "m->result = false" <>
    gostate tdfaStartState <>
    -- states
    foldMap (emitState tdfa) (tdfaStates tdfa) <>
    -- finish successfully
    label "match" <>
    stmt "m->result = true" <>
    foldMap setTagFromReg (M.toList tdfaFinalRegisters) <>
    foldMap fixedTag (M.toList tdfaFixedTags) <>
    foldMap matchFromTag (S.toList allTags) <>
    stmt "return" <>
    -- no match
    label "fail" <>
    stmt "return"
  where
    allTags = S.union (M.keysSet tdfaFixedTags) (M.keysSet tdfaFinalRegisters)
    allRegs = tdfaRegisters tdfa

toStrictByteString = L.toStrict . toLazyByteString

tdfa2c :: Regex -> ByteString
tdfa2c = toStrictByteString .
    genC . genTDFA . genTNFA .
    fixTags . adjustForFind . tagRegex

isCompatible :: Regex -> Bool
isCompatible = Regex.tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = L.putStrLn . toLazyByteString . genC . genTDFA . genTNFA . testTagRegex
