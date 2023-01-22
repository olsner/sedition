{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module TDFA2C where

import Data.ByteString.Builder as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy.Char8 as L

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

cIf :: Builder -> Builder -> Builder -> Builder
cIf cond t f = fun "if" [cond] <> "{\n  " <> t <> "} else {\n  " <> f <> "}\n"

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
    decstate s <>
    stmt ("YYNEXT(" <> string8 eolLabel <> ")") <>
    -- TODO if this is an accepting state we should generate code to set a flag
    -- that a match was found and back up the tags before continuing if we're
    -- *not* at EOF. (which we know now that we've passed YYNEXT)
    stmt ("YYDEBUG(\"" <> showB s <> ": YYCHAR=%d (%c)\\n\", YYCHAR, YYCHAR)") <>
    "switch (YYCHAR) {\n" <>
    foldMap emitTrans trans <>
    -- TODO Don't emit "default" label if cases cover all possible values.
    " default: goto fail;\n" <>
    "}\n" <>
    -- TODO See above
    -- (if isFinalState then finalRegOps else mempty) <>
    (if isEOLState then eolRegOps else mempty)
  where
    trans = CM.toRanges $ M.findWithDefault CM.empty s tdfaTrans
    --isFinalState = S.member s tdfaFinalStates
    isEOLState = M.member s tdfaEOL
    eolLabel = if isEOLState then eolLabelName else "fail"
    --matchLabelName = "matched_" <> show s
    eolLabelName = "eol_" <> show s
    -- finalRegOps =
    --     emitEndRegOps matchLabelName (M.findWithDefault [] s tdfaFinalFunction)
    eolRegOps =
        emitEndRegOps eolLabelName (M.findWithDefault [] s tdfaEOL)
    emitEndRegOps l ops =
        label l <>
        -- Use the one-past index for positions set in final regops
        stmt ("YYCURSOR++") <>
        stmt ("YYDEBUG(\"Matched EOF in " <> showB s <> " at %zu\\n\", YYPOS)") <>
        foldMap emitRegOp ops <>
        goto "match"

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
    cIf "offset > 0" (gostate tdfaStartStateNotBOL) (gostate tdfaStartState) <>
    -- states
    foldMap (emitState tdfa) (tdfaStates tdfa) <>
    -- finish successfully
    label "match" <>
    stmt "YYDEBUG(\"match found\\n\")" <>
    stmt "m->result = true" <>
    foldMap setTagFromReg (M.toList tdfaFinalRegisters) <>
    foldMap fixedTag (M.toList tdfaFixedTags) <>
    foldMap matchFromTag (S.toList allTags) <>
    foldMap debugTag (S.toList allTags) <>
    stmt "return" <>
    -- no match
    label "fail" <>
    stmt "YYDEBUG(\"match failed\\n\")" <>
    stmt "return"
  where
    allTags = S.union (M.keysSet tdfaFixedTags) (M.keysSet tdfaFinalRegisters)
    allRegs = tdfaRegisters tdfa

toStrictByteString :: Builder -> C.ByteString
toStrictByteString = L.toStrict . toLazyByteString

tdfa2c :: Regex -> C.ByteString
tdfa2c = toStrictByteString .
    genC . genTDFA . genTNFA .
    fixTags . adjustForFind . tagRegex

isCompatible :: Regex -> Bool
isCompatible = Regex.tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = L.putStrLn . toLazyByteString . genC . genTDFA . genTNFA . testTagRegex
