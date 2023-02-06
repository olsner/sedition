{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module TDFA2C where

import qualified Data.ByteString.Char8 as C

import qualified CharMap as CM
-- import CharMap (CharMap)
import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Set (Set)
import qualified Data.Set as S

-- import Data.List

import Debug.Trace

import GenC

import Regex (Regex)
import qualified Regex

import TaggedRegex
import TNFA (genTNFA)
import TDFA

decstate s = label (show s)
gostate s = goto (show s)

fixedTag (t, f) = stmt (showB t <> " = " <> g f)
  where
    g (EndOfMatch dist) = "YYPOS - " <> showB dist
    g (FixedTag t2 dist) = showB t2 <> " - " <> showB dist

matchix (T t) = showB (t `div` 2)
matchfld (T t) | even t = "rm_so"
               | otherwise = "rm_eo"

-- Since back references are single-digit, only the first 20 tags can be
-- output. POSIX requires parens in a lot of places and can't be told not to
-- add a capturable subexpression for it though, so this can pop up.
-- We need to ensure we don't write past the end of m->matches.
-- With optimization of unused tags this should not be used.
-- (And along with that we can probably stop using regmatch_t.)
possibleTag (T t) = t < 20

matchFromTag t | possibleTag t =
  stmt ("m->matches[" <> matchix t <> "]." <> matchfld t <> " = " <> showB t)
               | otherwise = trace "found an unoptimized tag that can't be used by match" mempty -- skip all impossible tags

debugTag t = stmt ("YYDEBUG(\"match[" <> matchix t <> "]." <> matchfld t <> " = %d\\n\", "  <> showB t <> ")")

setTagFromReg :: (TagId, RegId) -> Builder
setTagFromReg (t, r) = stmt (showB t <> " = " <>
    showB r <> " ? " <> showB r <> " - s->buf : -1")

declareTagVar :: TagId -> Builder
declareTagVar t = stmt ("regoff_t " <> showB t <> " = -1")
declareReg :: RegId -> Builder
declareReg r = stmt ("const char* " <> showB r <> " = NULL")

emitCase :: (Char,Char) -> Builder
emitCase (lb,ub)
    | lb == ub = " case " <> cchar lb <> ":\n"
    | otherwise  = " case " <> cchar lb <> " ... " <> cchar ub <> ":\n"

emitRegOp :: RegOp -> Builder
emitRegOp (r,val) = stmt ("  " <> showB r <> " = " <> g val) <>
    stmt ("YYDEBUG(\"" <> showB r <> " <- " <> showB val <> " == %td\\n\", " <> showB r <> " - YYBEGIN)") <>
    sfun "YYSTATS" ["regops", intDec 1]
  where
    g (SetReg Pos) = "YYCURSOR"
    g (SetReg Nil) = "NULL"
    g (CopyReg r2) = showB r2

emitTrans :: ([(Char,Char)], TDFATrans) -> Builder
emitTrans (cs, (s', regops)) =
    foldMap emitCase cs <> "{\n" <>
    (if not (null regops) then stmt ("YYDEBUG(\" -> " <> showB s' <> " at %zd\\n\", YYPOS)") else mempty) <>
    foldMap emitRegOp regops <>
    stmt "YYNEXT()" <>
    "  " <> gostate s' <>
    "}\n"

emitState :: TDFA -> Map StateId Int -> StateId -> Builder
emitState TDFA{..} minLengths s =
    hsep <>
    (if isFallbackState || isFinalState then fallbackRegOps else mempty) <>
    (if isEOLState || isFinalState then eolRegOps else mempty) <>
    decstate s <>
    -- SimulateTDFA does this after incPos for the state we're going to, so
    -- do it first thing in the state block. Should be the same, I hope :)
    maybeSetFallback <>
    earlyOut <>
    cWhen "YYEOF" (goto eolLabel) <>
    sfun "YYSTATS" ["visited_chars", "1"] <>
    stmt "YYCHAR = YYGET()" <>
    stmt ("YYDEBUG(\"" <> showB s <> ": YYCHAR=%x at %zu\\n\", YYCHAR, YYPOS)") <>
    "switch (YYCHAR) {\n" <>
    foldMap emitTrans (CM.toRanges trans) <>
    (if not (CM.isComplete trans)
        then (" default:\n" <>
              if isFinalState then finalRegOps else goto "fail")
        else mempty) <>
    "}\n"
  where
    trans = M.findWithDefault CM.empty s tdfaTrans
    isFallbackState = M.member s tdfaFallbackFunction
    isFinalState = M.member s tdfaFinalFunction
    isEOLState = M.member s tdfaEOL
    eolLabel | isEOLState || isFinalState = eolLabelName
             | otherwise = "fail"
    fallbackLabelName = "fallback_" <> show s
    eolLabelName = "eol_" <> show s
    finalRegOps =
        stmt ("YYDEBUG(\"default-transition from final state " <> showB s <> " at %zd\\n\", YYPOS)") <>
        emitEndRegOps tdfaFinalFunction
    eolRegOps = label eolLabelName <>
        stmt ("YYDEBUG(\"Matched EOF in " <> showB s <> " at %zu\\n\", YYPOS)") <>
        emitEndRegOps (if isEOLState then tdfaEOL else tdfaFinalFunction)
    fallbackRegOps = label fallbackLabelName  <>
        stmt ("YYCURSOR = fallback_cursor") <>
        stmt ("YYDEBUG(\"Fell back to " <> showB s <> " at %zu\\n\", YYPOS)") <>
        emitEndRegOps (tdfaFallbackFunction `M.union` tdfaFinalFunction)
    emitEndRegOps opfun =
        foldMap emitRegOp (M.findWithDefault [] s opfun) <> goto "match"

    setFallback =
        stmt ("YYDEBUG(\"Setting fallback to " <> showB s <> " @%zu\\n\", YYPOS)") <>
        stmt ("fallback_label = &&" <> string8 fallbackLabelName) <>
        stmt ("fallback_cursor = YYCURSOR")
    maybeSetFallback | isFinalState = setFallback
                     | otherwise    = mempty

    -- Very arbitrarily chosen minimum length where we assume an extra range
    -- check outweighs the work of useless matching.
    earlyOut | Just min <- M.lookup s minLengths, min > 3 =
        cWhen ("YYLIMIT - YYCURSOR < " <> intDec min) $
           sfun "YYSTATS" ["early_out", "1"] <> goto "fail"
             | otherwise = mempty

-- Calling convention for matcher functions:
-- 
-- static void FUN(match_t* m, string* s, const size_t orig_offset)
-- struct string { char* buf; size_t len; size_t alloc; };
-- struct match_t { bool result; regmatch_t matches[]; }
-- where regmatch_t has rm_so and rm_eo, corresponding to the even/odd tag
-- offset is > 0 when repeating a match for a global replace
--
-- Tags are "tX" (offsets in string), registers are "rX" (pointers in string).
--
-- Although it complicates things a bit in here (more goto spaghetti!), never
-- return directly but goto the end of the block, where the caller may have put
-- some before-return debugging code.
genC :: TDFA -> Builder
genC tdfa@TDFA{..} =
    cWhen "orig_offset && orig_offset >= s->len" (
        stmt ("YYDEBUG(\"Already at EOF (%zu >= %zu)\\n\", orig_offset, s->len)") <>
        goto "end"
    ) <>
    stmt ("YYDEBUG(\"Starting match at %zu (of %zu)\\n\", orig_offset, s->len)") <>
    stmt ("const char *const YYBEGIN = s->buf") <>
    stmt ("const char *const YYLIMIT = s->buf + s->len") <>
    sfun "YYSTATS" ["matched_chars", "s->len - orig_offset"] <>
    "#define YYPOS (YYCURSOR - YYBEGIN)\n" <>
    "#define YYEOF (YYCURSOR >= YYLIMIT)\n" <>
    "#define YYGET() (*YYCURSOR)\n" <>
    "#define YYNEXT() (YYCURSOR++)\n" <>
    "for (size_t offset = orig_offset; offset <= s->len; offset++) {\n" <>
    cWhen "offset > orig_offset" (sfun "YYSTATS" ["retries", "1"]) <>
    stmt ("const char *YYCURSOR = s->buf + offset") <>
    stmt ("unsigned char YYCHAR = 0") <>
    stmt ("void *fallback_label = NULL") <>
    stmt ("const char *fallback_cursor = NULL") <>
    foldMap declareTagVar (S.toList allTags) <>
    foldMap declareReg allRegs <>
    gotoStart <>
    blockComment "States" <>
    foldMap (emitState tdfa tdfaMinLengths) (tdfaStates tdfa) <>
    blockComment "Successful finish: found match" <>
    label "match" <>
    stmt "YYDEBUG(\"match found\\n\")" <>
    stmt "m->result = true" <>
    foldMap setTagFromReg (M.toList tdfaFinalRegisters) <>
    foldMap fixedTag (M.toList tdfaFixedTags) <>
    foldMap matchFromTag (S.toList allTags) <>
    foldMap debugTag (S.toList allTags) <>
    goto "end" <>
    blockComment "No match: retry, or fail" <>
    label "fail" <>
    -- TODO Check if this is same as SimulateTDFA
    cWhen "fallback_label" (goto "*fallback_label") <>
    cWhen "offset < s->len" (stmt "YYDEBUG(\"retry match\\n\")") <>
    "}\n" <>
    stmt "YYDEBUG(\"match failed\\n\")" <>
    label "end" <>
    sfun "YYSTATS" ["matched", "m->result"] <>
    sfun "YYSTATS" ["failed", "!m->result"]
  where
    allTags = S.union (M.keysSet tdfaFixedTags) (M.keysSet tdfaFinalRegisters)
    allRegs = tdfaRegisters tdfa
    tdfaMinLengths = minLengths tdfa
    gotoStart
      | tdfaStartStateNotBOL /= tdfaStartState =
        cIf "offset > 0" (gostate tdfaStartStateNotBOL) (gostate tdfaStartState)
      | otherwise = gostate tdfaStartState

tdfa2c :: Regex -> C.ByteString
tdfa2c = toByteString .
    genC . genTDFA . genTNFA . fixTags . tagRegex

isCompatible :: Regex -> Bool
isCompatible = Regex.tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = C.putStrLn . toByteString . genC . genTDFA . genTNFA . testTagRegex
