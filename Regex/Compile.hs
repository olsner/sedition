{-# LANGUAGE OverloadedStrings #-}

module Regex.Compile where

import qualified Data.ByteString.Char8 as C
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import qualified Data.Set as S

import Debug.Trace

import GenC
import GenAsm
import Regex.CompileAsm (genAsm)
import Regex.CompileIR (genC)
import Regex.IR (Program)
import Regex.Minimize (minimize)
import Regex.OptimizeIR (optimize)
import Regex.Regex hiding (Literal)
import qualified Regex.Regex as Regex
import Regex.TaggedRegex hiding (Literal)
import Regex.TDFA (genTDFA)
import Regex.TDFA2IR (genIR)
import Regex.TNFA (genTNFA)
import Regex.NFA (glushkovCompatible, removeTags, nfaFromRegex)
import Regex.NFA.Bitwise (bitwiseNFA, bitwiseToAsm, bitwiseToC, BitNFA)

data REImpl
  = IR Program
  | Bitwise (BitNFA Word)
  | Literal C.ByteString
  | LiteralChar Char
  deriving (Show)

re2asm :: Maybe IntSet -> Regex -> GenAsm.Builder ()
re2asm used re = case re2ir used re of
  IR ir -> genAsm . fst . optimize 1000000 $ ir
  Bitwise nfa -> bitwiseToAsm nfa
  Literal s -> GenAsm.sfun "match_literal" [GenAsm.already arg0, GenAsm.already arg1, GenAsm.already arg2, GenAsm.setCString s, GenAsm.setInt (C.length s)]
  LiteralChar c -> GenAsm.sfun "match_char" [GenAsm.already arg0, GenAsm.already arg1, GenAsm.already arg2, GenAsm.setInt (fromEnum c)]

-- TODO Allow controlling optimization fuel here, preferrably integrated in a
-- way that lets you bisect both regex and Sed IR optimizations.
re2c :: Maybe IntSet -> Regex -> GenC.Builder
re2c used re = case re2ir used re of
  IR ir -> genC . fst . optimize 1000000 $ ir
  Bitwise nfa -> bitwiseToC nfa
  Literal s -> GenC.stmt ("result = " <> fun "match_literal" ["m", "s", "orig_offset", cstring s, GenC.intDec (C.length s)])
  LiteralChar c -> GenC.stmt ("result = " <> fun "match_char" ["m", "s", "orig_offset", GenC.intDec (fromEnum c)])

tdfaIR = genIR . minimize . genTDFA . genTNFA . fixTags

re2ir :: Maybe IntSet -> Regex -> REImpl
re2ir used orig_re
  -- start/end tags are set by both literal and BNDM matchers, but if more tags
  -- are used we need to use the complete TDFA construction.
  | hasComplicatedTags re       = IR (tdfaIR re)
  | Regex.Char c <- orig_re     = LiteralChar c
  -- Prefer using BNDM over memmem for short enough literals, for now.
  | glushkovCompatible (removeTags re)
  , Just nfa <- bitwiseNFA 16 (nfaFromRegex re) = Bitwise (trace_ ("Using BNDM for " ++ show re) nfa)
  | Regex.Literal s <- orig_re
  , not (glushkovCompatible (removeTags re)) = trace ("Incompatible literal " ++ show s) $ Literal (C.pack s)
  | Regex.Literal s <- orig_re  = Literal (C.pack s)
  | otherwise                   = IR $ trace_ ("Could use other pure NFA for " ++ show re ++ " " ++ showCompatibility used orig_re) (tdfaIR re)
  where re = unusedTags used (tagRegex orig_re)
        trace_ _ x = x
        -- trace_ s x = trace s x

hasComplicatedTags re = not (S.null unfixedTags) || not (S.null usedTags)
  where
    (fixed,tags) = fixTags re
    -- Used tags: tags except "fixed" tags that are easy to manage
    -- if any tags are left used and unfixed that implies a variable length
    -- pattern where we would have wanted the BNDM machine to return the
    -- longest match. TODO Add flag to let BNDM now if it should keep
    -- going to find the longest match.
    unfixedTags = allTags fixed
    -- We can allow start/end tags to be used if fixed (i.e. constant
    -- length regex), but if any other tags are used we have to use a more
    -- complete implementation.
    -- TODO This now ends up excluding fixed-length patterns that
    -- definitely can be handled by BNDM.
    -- TODO Generate code to resolve fixed tags after BNDM matching.
    usedTags = S.delete (T 0) . allTags $ re
    hasSignificantTags = not (S.null unfixedTags) || not (S.null usedTags)

showCompatibility :: Maybe IntSet -> Regex -> String
showCompatibility used orig_re =
  "\nAnalyzing regex: " <> show orig_re <> " with tags " <> show used <>
  "\n => " <> (if isLiteral orig_re then "Literal!" else "Needs NFA at least") <>
  "\nAll tags: " <> show re <>
  "\nUsed tags " <> show fixed <>
  "\nWith fixed tags: " <> show tags <>
  "\n => " <> (if hasComplicatedTags re then "Complicated tags" else "Simple/no tags") <>
  (if hasAnchors re then "\n => not glushkov compatible: anchors" else "\nNo anchors")
  where
    re = unusedTags used (tagRegex orig_re)
    (fixed,tags) = fixTags re

isLiteral (Regex.Literal _) = True
isLiteral (Regex.Char _) = True
isLiteral _ = False

unusedTags (Just s) = selectTags (\(T t) -> t `IS.member` s)
unusedTags Nothing  = id

isCompatible :: Regex -> Bool
isCompatible = tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = C.putStrLn . GenC.toByteString . re2c Nothing . parseString True . C.pack

