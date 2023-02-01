{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module TDFA2C where

import Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy.Char8 as L
import Data.Semigroup

import qualified CharMap as CM
-- import CharMap (CharMap)
-- import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Set (Set)
import qualified Data.Set as S

-- import Data.List

import Debug.Trace

import Regex (Regex)
import qualified Regex

import TaggedRegex
import TNFA (genTNFA)
import TDFA

-- TODO Extract utility module to share with Compile...
showB :: Show a => a -> Builder
showB x = string8 (show x)

-- TODO intercalateM since it's not builder-specific
intercalateB :: Monoid a => a -> [a] -> a
intercalateB _   [] = mempty
intercalateB sep (x:xs) = x <> foldMap (sep <>) xs

fun :: Builder -> [Builder] -> Builder
fun function args = function <> "(" <> intercalateB ", " args <> ")"

sfun :: Builder -> [Builder] -> Builder
sfun function args = stmt (fun function args)

stmt :: Builder -> Builder
stmt builder = builder <> ";\n"

comment :: Builder -> Builder
comment builder = "// " <> builder <> "\n"

blockComment :: Builder -> Builder
blockComment builder = hsep <> "// " <> builder <> "\n"

hsep = stimes 79 "/" <> "\n"

cIf :: Builder -> Builder -> Builder -> Builder
cIf cond t f = fun "if " [cond] <> " {\n  " <> t <> "} else {\n  " <> f <> "}\n"
cWhen cond t = fun "if " [cond] <> " {\n  " <> t <> "}\n"

label name = string8 name <> ":\n"
goto name = stmt ("goto " <> string8 name)

decstate s = label (show s)
gostate s = goto (show s)

cchar = showB . fromEnum

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
emitRegOp (r,SetReg val) = stmt ("  " <> showB r <> " = " <> g val)
  where
    g Pos = "YYCURSOR - 1" -- cases run after incrementing YYCURSOR
    g Nil = "NULL"
emitRegOp (r,CopyReg r2) = stmt ("  " <> showB r <> " = " <> showB r2)

emitTrans :: ([(Char,Char)], TDFATrans) -> Builder
emitTrans (cs, (s', regops)) =
    foldMap emitCase cs <> "{\n" <>
    foldMap emitRegOp regops <>
    "  " <> gostate s' <>
    "}\n"

emitState :: TDFA -> StateId -> Builder
emitState TDFA{..} s =
    hsep <>
    (if isFallbackState then fallbackRegOps else mempty) <>
    (if isFinalState then finalRegOps else mempty) <>
    (if isEOLState then eolRegOps else mempty) <>
    hsep <>
    decstate s <>
    stmt ("YYNEXT(" <> string8 eolLabel <> ")") <>
    stmt ("YYDEBUG(\"" <> showB s <> ": YYCHAR=%d (%c) at %zu\\n\", YYCHAR, YYCHAR, YYPOS - 1)") <>
    -- TODO Check for off-by-one in position etc
    maybeSetFallback <>
    "switch (YYCHAR) {\n" <>
    foldMap emitTrans trans <>
    -- TODO Don't emit "default" label if cases cover all possible values.
    " default:\n" <>
    (if isFinalState then stmt "YYCURSOR--" <> goto matchLabelName else goto "fail") <>
    "}\n"
  where
    trans = CM.toRanges $ M.findWithDefault CM.empty s tdfaTrans
    isFallbackState = M.member s tdfaFallbackFunction
    isFinalState = M.member s tdfaFinalFunction
    isEOLState = M.member s tdfaEOL
    eolLabel | isEOLState = eolLabelName
             | isFinalState = matchLabelName
             | otherwise = "fail"
    fallbackLabelName = "fallback_" <> show s
    matchLabelName = "matched_" <> show s
    eolLabelName = "eol_" <> show s
    finalRegOps = label matchLabelName  <>
        stmt ("YYDEBUG(\"Final state " <> showB s <> " at %zu\\n\", YYPOS)") <>
        emitEndRegOps tdfaFinalFunction
    -- applyFinalState True s:
    -- 1. final function
    -- 2. eol function
    eolRegOps = label eolLabelName <>
        stmt ("YYDEBUG(\"Matched EOF in " <> showB s <> " at %zu\\n\", YYPOS)") <>
        emitEndRegOps tdfaEOL
    fallbackRegOps = label fallbackLabelName  <>
        stmt ("YYCURSOR = fallback_cursor") <>
        stmt ("YYDEBUG(\"Fell back to " <> showB s <> " at %zu\\n\", YYPOS)") <>
        emitEndRegOps tdfaFallbackFunction
    emitEndRegOps opfun =
        foldMap emitRegOp (M.findWithDefault [] s opfun) <> goto "match"

    setFallback =
        stmt ("fallback_label = &&" <> string7 fallbackLabelName) <>
        stmt ("fallback_cursor = YYCURSOR")
    maybeSetFallback | isFallbackState = setFallback
                     | otherwise    = mempty

-- Calling convention for matcher functions:
-- 
-- static void FUN(match_t* m, string* s, size_t offset)
-- struct string { char* buf; size_t len; size_t alloc; };
-- struct match_t { bool result; regmatch_t matches[]; }
-- where regmatch_t has rm_so and rm_eo, corresponding to the even/odd tag
-- offset is > 0 when repeating a match for a global replace
--
-- Tags are "tX" (offsets in string), registers are "rX" (pointers in string).
genC :: TDFA -> B.Builder
genC tdfa@TDFA{..} =
    stmt ("const char *const YYBEGIN = s->buf + offset") <>
    "for (; offset <= s->len; offset++) {\n" <>
    stmt ("const char *const YYLIMIT = s->buf + s->len") <>
    stmt ("const char *YYCURSOR = s->buf + offset") <>
    stmt ("unsigned char YYCHAR = 0") <>
    stmt ("void *fallback_label = NULL") <>
    stmt ("const char *fallback_cursor = NULL") <>
    "#define YYPOS (YYCURSOR - YYBEGIN)\n" <>
    "#define YYNEXT(endlabel) do { \\\n" <>
    "   if (YYCURSOR >= YYLIMIT) goto endlabel; \\\n" <>
    "   else YYCHAR = *YYCURSOR++; \\\n" <>
    "  } while (0)\n" <>
    foldMap declareTagVar (S.toList allTags) <>
    foldMap declareReg allRegs <>
    stmt "m->result = false" <>
    gotoStart <>
    blockComment "States" <>
    foldMap (emitState tdfa) (tdfaStates tdfa) <>
    blockComment "Successful finish: found match" <>
    label "match" <>
    stmt "YYDEBUG(\"match found\\n\")" <>
    stmt "m->result = true" <>
    foldMap setTagFromReg (M.toList tdfaFinalRegisters) <>
    foldMap fixedTag (M.toList tdfaFixedTags) <>
    foldMap matchFromTag (S.toList allTags) <>
    foldMap debugTag (S.toList allTags) <>
    stmt "return" <>
    blockComment "No match: retry, or fail" <>
    label "fail" <>
    -- TODO Check if this is same as SimulateTDFA
    cWhen "fallback_label" (goto "*fallback_label") <>
    cWhen "offset <= s->len" (stmt "YYDEBUG(\"retry match\\n\")") <>
    "}\n" <>
    stmt "YYDEBUG(\"match failed\\n\")" <>
    stmt "return"
  where
    allTags = S.union (M.keysSet tdfaFixedTags) (M.keysSet tdfaFinalRegisters)
    allRegs = tdfaRegisters tdfa

    gotoStart
      | tdfaStartStateNotBOL /= tdfaStartState =
        cIf "offset > 0" (gostate tdfaStartStateNotBOL) (gostate tdfaStartState)
      | otherwise = gostate tdfaStartState

toStrictByteString :: Builder -> C.ByteString
toStrictByteString = L.toStrict . toLazyByteString

tdfa2c :: Regex -> C.ByteString
tdfa2c = toStrictByteString .
    genC . genTDFA . genTNFA . fixTags . tagRegex

isCompatible :: Regex -> Bool
isCompatible = Regex.tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = L.putStrLn . toLazyByteString . genC . genTDFA . genTNFA . testTagRegex
