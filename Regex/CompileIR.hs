{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}

module Regex.CompileIR where

import Compiler.Hoopl as H

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
import GenC

yystats name inc = sfun "YYSTATS" [name, inc]
yydebug fmt args = sfun "YYDEBUG" (fmt : args)

tagix (T t) = intDec t
possibleTag (T t) = t < 20

matchFromTag (t,val) | possibleTag t = stmt ("m->tags[" <> tagix t <> "] = " <> tagValue val)
                     | otherwise = trace "found an unoptimized tag that can't be used by match" mempty -- skip all impossible tags

debugTag t = yydebug ("\"match[" <> tagix t <> "] = %td\\n\"") ["m[" <> tagix t <> "]"]

tagValue :: IR.TagValue -> Builder
tagValue (Reg r 0) = showB r <> " ? " <> showB r <> " - YYBEGIN : -1"
tagValue (Reg r d) = showB r <> " ? " <> showB r <> " - YYBEGIN - " <> intDec d <> " : -1"
tagValue (EndOfMatch 0) = "YYPOS"
tagValue (EndOfMatch d) = "YYPOS - " <> intDec d

declareReg :: R -> Builder
declareReg r = stmt ("const uint8_t* " <> showB r <> " = NULL")

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
genC :: Program -> Builder
genC program@Program{..} =
    stmt ("YYDEBUG(\"Starting match at %zu (of %zu)\\n\", orig_offset, s->len)") <>
    stmt ("const uint8_t *const YYBEGIN = s->buf") <>
    stmt ("const uint8_t *const YYLIMIT = s->buf + s->len") <>
    sfun "YYSTATS" ["matched_chars", "s->len - orig_offset"] <>
    "#define YYPOS (YYCURSOR - YYBEGIN)\n" <>
    "#define YYEOF (YYCURSOR >= YYLIMIT)\n" <>
    "#define YYREMAINING (YYLIMIT - YYCURSOR)\n" <>
    "#define YYGET(offs) (YYCURSOR[offs])\n" <>
    "#define YYNEXT() (YYCURSOR++)\n" <>
    stmt ("const uint8_t *YYCURSOR = s->buf + orig_offset") <>
    stmt ("void *fallback_label = NULL") <>
    stmt ("const uint8_t *fallback_cursor = NULL") <>
    foldMap declareReg allRegs <>
    blockComment "Jump to entry point" <>
    gotoL entryPoint <>
    blockComment "Basic blocks" <>
    postOrderFoldGraphNodes foldEmitInsn program mempty <>
    blockComment "Exit point" <>
    label "end" <>
    sfun "YYSTATS" ["matched", "result"] <>
    sfun "YYSTATS" ["failed", "!result"]
  where allRegs = setElems (IR.allRegs program)

earlyOut l = sfun "YYSTATS" ["early_out", "1"] <> goto l

tdfa2c :: Maybe IntSet -> Regex -> C.ByteString
tdfa2c used = toByteString .
    genC .
    -- TODO Allow controlling optimization fuel here, preferrably integrated in
    -- a way that lets you bisect both regex and Sed IR optimizations.
    fst . optimize 1000000 .
    genIR .
    minimize .
    genTDFA .
    genTNFA .
    fixTags .
    makeSearchRegex .
    unusedTags .
    tagRegex
  where unusedTags | Just s <- used = selectTags (\(T t) -> t `IS.member` s)
                   | otherwise = id

isCompatible :: Regex -> Bool
isCompatible = Regex.tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = C.putStrLn . tdfa2c Nothing . Regex.parseString True . C.pack

postOrderFoldGraphNodes ::
  forall a . Monoid a => (forall e x . Insn e x -> a -> a) -> Program -> a -> a
postOrderFoldGraphNodes f Program{..} e = foldMap f' (postorder_dfs g) e
  where g = mkLast (Branch entryPoint) H.|*><*| programGraph
        f' :: Block Insn e x -> IndexedCO e a a -> IndexedCO x a a
        f' = foldBlockNodesF f

foldEmitInsn :: Insn e x -> Builder -> Builder
foldEmitInsn insn = (<> emitInsn insn)

emitInsn :: Insn e x -> Builder
emitInsn (Label l) = label (show l)

-- O C control flow
emitInsn (IfBOL tl fl) = cIf "YYCURSOR == YYBEGIN" (gotoL tl) (gotoL fl)
emitInsn (Switch cm def) =
    "switch (YYGET(0)) {\n" <>
    foldMap emitCases (CM.toRanges cm) <>
    " default: " <> gotoL def <> "}\n"
emitInsn (TotalSwitch cm) =
    "switch (YYGET(0)) {\n" <>
    foldMap emitCases (CM.toRanges cm) <>
    "}\n"
emitInsn Fail = goto "end"
emitInsn (Match tagMap) =
    stmt "YYDEBUG(\"match found\\n\")" <>
    stmt "result = true" <>
    foldMap matchFromTag (M.toList tagMap) <>
    foldMap debugTag (M.keys tagMap) <>
    goto "end"
emitInsn (CheckBounds 1 eof cont) =
  cIf ("YYLIMIT <= YYCURSOR") (gotoL eof) (gotoL cont)
emitInsn (CheckBounds n eof cont) =
  cIf ("YYLIMIT < YYCURSOR + " <> intDec n) (gotoL eof) (gotoL cont)
emitInsn (Branch l) = gotoL l

-- O O debugging
emitInsn (Trace msg) = yydebug "\"%s\\n\"" [cstring (C.pack msg)]
-- O O primitives
emitInsn Next = sfun "YYNEXT" []
emitInsn (Set r) = stmt (showB r <> " = YYCURSOR")
emitInsn (Clear r) = stmt (showB r <> " = NULL")
emitInsn (Copy r r2) = stmt (showB r <> " = " <> showB r2)

-- O O fallback operations
emitInsn (Fallback _) = goto "*fallback_label"
emitInsn (SetFallback l) = stmt ("fallback_label = &&" <> showB l)
emitInsn SaveCursor = stmt "fallback_cursor = YYCURSOR"
emitInsn RestoreCursor = stmt "YYCURSOR = fallback_cursor"
