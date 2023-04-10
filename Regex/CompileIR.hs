{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Regex.CompileIR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict

import qualified Data.ByteString.Char8 as C

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
-- import Data.List

import Debug.Trace

import qualified CharMap as CM
-- import CharMap (CharMap)

import Regex.Regex (Regex)
import qualified Regex.Regex as Regex

import Regex.IR as IR
import Regex.TaggedRegex (TagId(..), fixTags, selectTags, tagRegex)
import Regex.TNFA (genTNFA)
import Regex.TDFA (genTDFA)
import Regex.TDFA2IR (genIR)
import GenC

yystats name inc = sfun "YYSTATS" [name, inc]
yydebug fmt args = sfun "YYDEBUG" (fmt : args)

matchix (T t) = showB (t `div` 2)
matchfld (T t) | even t = "rm_so"
               | otherwise = "rm_eo"

possibleTag (T t) = t < 20

matchFromTag (t,val) | possibleTag t =
  stmt ("m->matches[" <> matchix t <> "]." <> matchfld t <> " = " <> tagValue val)
               | otherwise = trace "found an unoptimized tag that can't be used by match" mempty -- skip all impossible tags

debugTag t = yydebug ("\"match[" <> matchix t <> "]." <> matchfld t <> " = %td\\n\"") ["m->matches[" <> matchix t <> "]." <> matchfld t]

tagValue :: IR.TagValue -> Builder
tagValue (Reg r d) = showB r <> " ? " <> showB r <> " - s->buf - " <> intDec d <> " : -1"
-- TOOD off-by-one etc
tagValue (EndOfMatch d) = "YYCURSOR - " <> intDec d

declareReg :: R -> Builder
declareReg r = stmt ("const char* " <> showB r <> " = NULL")

emitCase :: (Char,Char) -> Builder
emitCase (lb,ub)
    | lb == ub = " case " <> cchar lb <> ":\n"
    | otherwise  = " case " <> cchar lb <> " ... " <> cchar ub <> ":\n"

emitCases :: ([(Char,Char)], Label) -> Builder
emitCases (cs, label) = foldMap emitCase cs <> gotoL label

-- Calling convention for matcher functions:
-- 
-- static bool FUN(match_t* m, string* s, const size_t orig_offset)
-- struct string { char* buf; size_t len; size_t alloc; };
-- struct match_t { regmatch_t matches[]; }
-- where regmatch_t has rm_so and rm_eo, corresponding to the even/odd tag
-- offset is > 0 when repeating a match for a global replace
--
-- Tags are "tX" (offsets in string), registers are "rX" (pointers in string).
--
-- Although it complicates things a bit in here (more goto spaghetti!), never
-- return directly but goto the end of the block, where the caller may have put
-- some before-return debugging code.
--
-- The variable 'bool result' should be set to the success (true = match) of
-- the regexp search.
genC :: Program -> Builder
genC (entry, graph) =
    stmt ("YYDEBUG(\"Starting match at %zu (of %zu)\\n\", orig_offset, s->len)") <>
    stmt ("const char *const YYBEGIN = s->buf") <>
    stmt ("const char *const YYLIMIT = s->buf + s->len") <>
    sfun "YYSTATS" ["matched_chars", "s->len - orig_offset"] <>
    "#define YYPOS (YYCURSOR - YYBEGIN)\n" <>
    "#define YYEOF (YYCURSOR >= YYLIMIT)\n" <>
    "#define YYREMAINING (YYLIMIT - YYCURSOR)\n" <>
    "#define YYGET() (*YYCURSOR)\n" <>
    "#define YYNEXT() (YYCURSOR++)\n" <>
    stmt ("const char *YYCURSOR = s->buf + orig_offset") <>
    stmt ("unsigned char YYCHAR = 0") <>
    stmt ("void *fallback_label = NULL") <>
    stmt ("const char *fallback_cursor = NULL") <>
    -- foldMap declareReg allRegs <>
    blockComment "Jump to entry point" <>
    gotoL entry <>
    blockComment "Basic blocks" <>
    foldGraphNodes foldEmitInsn graph mempty <>
    blockComment "Exit point" <>
    label "end" <>
    sfun "YYSTATS" ["matched", "result"] <>
    sfun "YYSTATS" ["failed", "!result"]

earlyOut l = sfun "YYSTATS" ["early_out", "1"] <> goto l

tdfa2c :: Maybe IntSet -> Regex -> C.ByteString
tdfa2c used = toByteString .
    genC . genIR . genTDFA . genTNFA . fixTags . unusedTags . tagRegex
  where unusedTags | Just s <- used = selectTags (\(T t) -> t `IS.member` s)
                   | otherwise = id

isCompatible :: Regex -> Bool
isCompatible = Regex.tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = C.putStrLn . tdfa2c Nothing . Regex.parseString True . C.pack

foldEmitInsn :: Insn e x -> Builder -> Builder
foldEmitInsn insn = (<> emitInsn insn)

emitInsn :: Insn e x -> Builder
emitInsn (Label l) = label (show l)

-- O C control flow
emitInsn (IfBOL tl fl) = cIf "YYPOS == YYBEGIN" (gotoL tl) (gotoL fl)
emitInsn (Switch cm def) =
    "switch (YYCHAR) {\n" <>
    foldMap emitCases (CM.toRanges cm) <>
    (if not (CM.isComplete cm)
        then " default: " <> gotoL def
        else mempty) <>
    "}\n"
emitInsn Fail = goto "end"
emitInsn (Match tagMap) =
    stmt "YYDEBUG(\"match found\\n\")" <>
    stmt "result = true" <>
    foldMap matchFromTag (M.toList tagMap) <>
    foldMap debugTag (M.keys tagMap) <>
    goto "end"
emitInsn (CheckBounds n eof cont) =
  cIf ("YYLIMIT - YYCURSOR < " <> intDec n) (gotoL eof) (gotoL cont)
emitInsn (Branch l) = gotoL l

-- O O debugging
emitInsn (Trace msg) = yydebug (cstring (C.pack msg)) []
-- O O primitives
emitInsn Next = sfun "YYNEXT" []
emitInsn (Set r) = stmt (showB r <> " = YYCURSOR")
emitInsn (Clear r) = stmt (showB r <> " = nullptr")
emitInsn (Copy r r2) = stmt (showB r <> " = " <> showB r2)

-- O O fallback operations
emitInsn Fallback = goto "*fallback_label"
emitInsn (SetFallback l) = stmt ("fallback_label = &&" <> showB l)
emitInsn SaveCursor = stmt "fallback_cursor = YYCURSOR"
emitInsn RestoreCursor = stmt "YYCURSOR = fallback_cursor"
