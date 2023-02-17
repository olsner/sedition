{-# LANGUAGE OverloadedStrings,GADTs,TypeFamilies,RankNTypes,TemplateHaskell #-}

module Compile (compileIR) where

import Prelude hiding (pred)
import Compiler.Hoopl as H

import qualified Data.ByteString.Char8 as C
import Data.FileEmbed (embedStringFile)
import Data.Map (Map)
import qualified Data.Map as M
import Data.String

-- import Debug.Trace

import System.Exit

import AST
import GenC
import qualified IR
import IR (Program)
import qualified Regex
import qualified TDFA2C

seditionRuntime :: IsString a => a
seditionRuntime = $(embedStringFile "sedition.h")
startingLine = length (lines seditionRuntime) + 2

programHeader ofile program =
    "#line " <> intDec startingLine <> " " <> cstring ofile <> "\n" <>
    "/* ^ runtime system */\n\
    \/* v compiled program */\n\
    \static bool hasPendingIPC = false;\n\
    \static int exit_status = EXIT_SUCCESS;\n\
    \static regex_match_fun_t* lastRegex = NULL;\n" <>
    foldMap (declare "re_t" regexvar) regexpvars <>
    foldMap compileRE (M.assocs allRegexps) <>
    "int main(int argc, const char *argv[]) {\n" <>
    foldMap (declare "bool" pred) preds <>
    foldMap (declare "string" stringvar) strings <>
    foldMap (declare "FILE*" infd) files <>
    foldMap (declare "FILE*" outfd) files <>
    foldMap (declare "match_t" match) matches <>
    foldMap (declare "bool" mpred) matches <>
    foldMap initRegexp (M.assocs regexps) <>
    infd 0 <> " = next_input(argc, argv);\n" <>
    outfd 0 <> " = stdout;\n"
  where
    declare t s var = "static " <> t <> " " <> s var <> ";\n"
    preds = IR.allPredicates program
    strings = IR.allStrings program
    files = IR.allFiles program
    matches = IR.allMatches program
    regexps :: Map IR.RE (S, Bool)
    allRegexps = IR.allRegexps program
    regexps = M.filter needRegcomp allRegexps
    regexpvars = M.keys regexps
    initRegexp (re, (s, ere)) = sfun "compile_regexp" [regex re, cstring s, bool ere]

programFooter program = "exit:\n" <>
    foldMap closeFile files <>
    foldMap freeRegex regexps <>
    foldMap freeString strings <>
    sfun "tdfa2c_statistics" [] <>
    "return exit_status;\n" <>
    "}\n"
  where
    strings = IR.allStrings program
    files = IR.allFiles program
    regexps = M.keys (M.filter needRegcomp (IR.allRegexps program))
    freeRegex re = sfun "free_regexp" [regex re]
    freeString s = sfun "free_string" [string s]

compileIR :: FilePath -> Bool -> H.Label -> Program -> S
compileIR ofile _ipc entry program = toByteString $
  seditionRuntime
  <> programHeader (C.pack ofile) program
  <> gotoL entry
  <> foldMap compileBlock blocks
  <> programFooter program
  where GMany _ blocks _ = program

-- compileBlock :: Block IR.Insn e x -> Builder
compileBlock block = fold (mempty :: Builder)
  where
    fold :: Builder -> Builder
    fold = foldBlockNodesF f block
    f :: forall e x . IR.Insn e x -> Builder -> Builder
    f insn builder = builder <> compileInsn insn

gotoL :: H.Label -> Builder
gotoL l = goto (show l)

string (IR.SVar s) = "&S" <> intDec s
stringvar (IR.SVar s) = "S" <> intDec s
pred (IR.Pred p) = "P" <> intDec p
match (IR.MVar m) = "M" <> intDec m
matchref (IR.MVar m) = "&M" <> intDec m
mpred (IR.MVar m) = "MP" <> intDec m
infd i = "inF" <> idIntDec i
outfd i = "outF" <> idIntDec i

regexvar (IR.RE i) = "RE" <> intDec i
regexfun (IR.RE i) = "match_RE" <> intDec i
regex r = "&" <> regexvar r

lineNumber = "lineNumber"
hasPendingIPC = "hasPendingIPC"
lastRegex = "lastRegex"

compileCond cond = case cond of
  IR.Bool b -> bool b
  IR.Line l -> intDec l <> " == " <> lineNumber
  IR.EndLine l -> intDec l <> " < " <> lineNumber
  IR.IsMatch mvar -> mpred mvar
  IR.AtEOF 0 -> fun "is_all_eof" ["&" <> infd 0, "argc", "argv"]
  IR.AtEOF i -> fun "is_eof" [infd i]
  IR.PendingIPC -> hasPendingIPC
  IR.PRef p -> pred p

compileMatch m (IR.Match svar re) = fun (regexfun re) [matchref m, string svar, "0"]
compileMatch m (IR.MatchLastRE svar) = fun lastRegex [matchref m, string svar, "0"]
compileMatch m (IR.NextMatch m2 s) = fun "next_match" [matchref m, matchref m2, string s]
compileMatch m (IR.MVarRef m2) = fun "copy_match" [matchref m, matchref m2, mpred m2]

closeFile i = sfun "close_file" [infd i] <> sfun "close_file" [outfd i]

compileInsn :: IR.Insn e x -> Builder
compileInsn (IR.Label lbl) = label (show lbl)
compileInsn (IR.Branch l) = gotoL l
compileInsn (IR.SetP p cond) = stmt (pred p <> " = " <> compileCond cond)
compileInsn (IR.SetS s expr) = stmt (setString s expr)
compileInsn (IR.SetM m expr) = stmt (mpred m <> "  = " <> compileMatch m expr)
compileInsn (IR.If c t f) = cIf (compileCond c) (gotoL t) (gotoL f)
compileInsn (IR.Listen i maybeHost port) =
  sfun "sock_listen" [infd i, chost maybeHost, intDec port]
  where
    chost (Just host) = cstring host
    chost Nothing = "NULL"
compileInsn (IR.Accept s c) = stmt (infd c <> " = " <> fun "accept" [infd s])
compileInsn (IR.Fork entry next) = sfun "FORK" [showB entry, showB next]
compileInsn (IR.Redirect i j) =
  closeFile i <>
  stmt (outfd i <> " = " <> outfd j) <>
  stmt (infd i <> " = " <> outfd j) <>
  stmt (outfd j <> " = NULL") <>
  stmt (infd j <> " = NULL")
compileInsn (IR.CloseFile i) = closeFile i

-- Done in initialization
compileInsn (IR.CompileRE _ _ _) = mempty
compileInsn (IR.SetLastRE re) = setLastRegex re
compileInsn (IR.Message s) = sfun "send_message" [string s]

compileInsn (IR.Print i s) = sfun "print" [outfd i, string s]
compileInsn (IR.Quit code) =
    stmt ("exit_status = " <> c_code code) <> goto "exit"
  where
    c_code (ExitFailure n) = intDec n
    c_code ExitSuccess = "EXIT_SUCCESS"
compileInsn (IR.Comment s) = comment (string8 s)

compileInsn (IR.Wait i) = sfun "wait_or_event" [infd i]
compileInsn (IR.Read svar 0) =
    cWhile ("!" <> fun "read_line" [string svar, infd 0]) $
        -- should not touch output file
        sfun "close_file" [infd 0] <>
        infd 0 <> " = " <> sfun "next_input" ["argc", "argv"] <>
        "if (" <> infd 0 <> " == NULL) goto exit;\n"
compileInsn (IR.Read svar i) = sfun "read_line" [string svar, infd i]
compileInsn (IR.GetMessage svar) = sfun "get_message" [string svar]

compileInsn (IR.OpenFile fd write path) =
    sfun "close_file" [fdvar] <>
    fdvar <> " = " <> sfun "open_file" [cstring path, bool write]
  where
    fdvar = (if write then outfd else infd) fd
compileInsn (IR.ReadFile svar fd) = sfun "read_file" [string svar, infd fd]
compileInsn (IR.ShellExec svar) = sfun "shell_exec" [string svar]

--compileInsn cmd = fatal ("compileInsn: Unhandled instruction " ++ show cmd)

setLastRegex re = stmt (lastRegex <> " = &" <> regexfun re)

setString :: IR.SVar -> IR.StringExpr -> Builder
setString t (IR.SConst s) = fun "set_str_const" [string t, cstring s, intDec (C.length s)]
setString t (IR.SVarRef svar) = fun "copy" [string t, string svar]
setString t (IR.SRandomString) = fun "random_string" [string t]
setString t (IR.STrans from to s) =
  -- TODO compile transformations into functions. Might require that we add
  -- statefulness to cache them and to output functions outside of main though.
  fun "trans" [string t, cstring from, cstring to, string s]
setString t (IR.SAppendNL a b) = fun "concat_newline" (map string [t, a, b])
setString t (IR.SAppend a b)
    | t == a    = fun "concat_inplace" (map string [t, b])
    | otherwise = fun "concat" (map string [t, a, b])
setString t (IR.SSubstring s start end) =
  fun "substring" [string t, string s, startix, endix]
  where
      startix = resolveStringIndex s start
      endix = resolveStringIndex s end
setString t (IR.SFormatLiteral w s) =
    fun "format_literal" [string t, intDec w, string s]
setString t (IR.SGetLineNumber) = fun "format_int" [string t, lineNumber]

resolveStringIndex :: IR.SVar -> IR.SIndex -> Builder
resolveStringIndex s ix = case ix of
  IR.SIStart -> "0"
  IR.SIEnd -> fun "string_len" [string s]
  IR.SIMatchStart m -> groupStart m 0
  IR.SIMatchEnd m -> groupEnd m 0
  IR.SIGroupStart m i -> groupStart m i
  IR.SIGroupEnd m i -> groupEnd m i
  where
    groupStart m i = match m <> ".matches[" <> intDec i <> "].rm_so"
    groupEnd m i = match m <> ".matches[" <> intDec i <> "].rm_eo"

testCompare = False

forceRegcomp = False

needRegcomp (s, ere) = forceRegcomp ||
    testCompare || not (TDFA2C.isCompatible (Regex.parseString ere s))

compileRE (r, (s, ere)) = wrapper body
  where
    body | needRegexec = regexec
         | testCompare = match_for_compare <> tdfa2c r re <> compare_matches
         | otherwise   = tdfa2c r re
    re = Regex.parseString ere s
    needRegexec = forceRegcomp || not (TDFA2C.isCompatible re)
    res = C.pack $ Regex.reString re
    wrapper b = "static bool " <> regexfun r <> "(match_t* m, string* s, const size_t orig_offset) {\n" <> comment description <> "bool result = false;\n" <> b <> "return result;\n}\n"
    match m = fun "match_regexp" [m, "s", "orig_offset", regex r, regexfun r]
    -- regcomp is run at start of main so we just need to forward the arguments.
    regexec = stmt ("result = " <> match "m")
    match_for_compare =
        stmt "match_t m2" <>
        stmt ("const bool result2 = " <> match "&m2")
    compare_matches = sfun "compare_regexp_matches" ["result2", "&m2", "result", "m", "s", "orig_offset", "__PRETTY_FUNCTION__", cstring res]

    description =
        (if ere then "ERE: "  else "BRE: ") <> cstring s <>
        " -> ERE: " <> cstring res <>
        (if needRegexec then " (using regcomp)" else " (using TDFA2C)")

tdfa2c r re =
    comment ("tdfa2c regex: " <> cstring res) <>
    sfun "clear_match" ["m"] <>
    -- Since regexec seems to set all unused matches to -1, do the same for
    -- compare_regexp_matches.
    (if testCompare then stmt "memset(&m->matches, 0xff, sizeof(m->matches))" else mempty) <>
    stmt ("m->fun = " <> regexfun r)  <>
    byteString (TDFA2C.tdfa2c re)
  where
    res = C.pack $ Regex.reString re
