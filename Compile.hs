{-# LANGUAGE OverloadedStrings,GADTs,TypeFamilies,RankNTypes,TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}

module Compile (compileIR) where

import Prelude hiding (pred)
import Compiler.Hoopl as H

import qualified Data.ByteString.Char8 as C
import Data.FileEmbed (embedStringFile)
import Data.String

-- import Debug.Trace

import System.Exit

import AST
import GenC
import qualified IR
import IR (Program)
import qualified Regex.Regex as Regex
import qualified Regex.CompileIR as Regex2C

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
    foldMap (declare "re_t" regexvar) regexps <>
    foldMap compileRE allRegexps <>
    "int main(int argc, const char *argv[]) {\n" <>
    -- These are just static to get them zero-initialized for free. (also they
    -- are always passed by address, so anything smart the C compiler can do
    -- with local variables might not apply anyway.) Other variables are local
    -- to allow the C compiler more freedom.
    foldMap (declare "string" stringvar) strings <>
    foldMap (declare "match_t" match) matches <>
    foldMap (declare "regex_match_fun_t*" matchfun) matches <>
    foldMap (init "bool" pred "false") preds <>
    foldMap (init "FILE*" infd "NULL") files <>
    foldMap (init "FILE*" outfd "NULL") files <>
    foldMap (init "bool" mpred "false") matches <>
    sfun "enable_stats_on_sigint" [] <>
    sfun "setlinebuf" ["stdin"] <>
    sfun "setlinebuf" ["stdout"] <>
    foldMap initRegexp regexps <>
    infd 0 <> " = next_input(argc, argv);\n" <>
    outfd 0 <> " = stdout;\n"
  where
    declare t s var = "static " <> t <> " " <> s var <> ";\n"
    init t s value var = t <> " " <> s var <> " = " <> value <> ";\n"
    preds = IR.allPredicates program
    strings = IR.allStrings program
    files = IR.allFiles program
    matches = IR.allMatches program
    allRegexps = IR.allRegexps program
    regexps = filter needRegcomp allRegexps
    initRegexp re@IR.RE{..} = sfun "compile_regexp" [regex re, cstring reString, bool reERE]

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
    regexps = filter needRegcomp (IR.allRegexps program)
    freeRegex re = sfun "free_regexp" [regex re]
    freeString s = sfun "free_string" [string s]

compileIR :: FilePath -> Bool -> H.Label -> Program -> S
compileIR ofile _ipc entry program_in = toByteString $
  seditionRuntime
  <> programHeader (C.pack ofile) program
  <> gotoL entry
  <> foldMap compileBlock blocks
  <> programFooter program
  where
    program@(GMany _ blocks _) = IR.numberAllRegexps program_in

-- compileBlock :: Block IR.Insn e x -> Builder
compileBlock block = fold (mempty :: Builder)
  where
    fold :: Builder -> Builder
    fold = foldBlockNodesF f block
    f :: forall e x . IR.Insn e x -> Builder -> Builder
    f insn builder = builder <> compileInsn insn

string (IR.SVar s) = "&S" <> intDec s
stringvar (IR.SVar s) = "S" <> intDec s
pred (IR.Pred p) = "P" <> intDec p
match (IR.MVar m) = "M" <> intDec m
matchref (IR.MVar m) = "&M" <> intDec m
matchfun (IR.MVar m) = "MF" <> intDec m
mpred (IR.MVar m) = "MP" <> intDec m
infd i = "inF" <> idIntDec i
outfd i = "outF" <> idIntDec i

regexvar IR.RE{..} = "RE" <> intDec reID
regexfun IR.RE{..} = "match_RE" <> intDec reID
regex r = "&" <> regexvar r

lineNumber = "lineNumber"
hasPendingIPC = "hasPendingIPC"
lastRegex = "lastRegex"

compileCond cond = case cond of
  IR.Line l -> intDec l <> " == " <> lineNumber
  IR.EndLine l -> intDec l <> " < " <> lineNumber
  IR.IsMatch mvar -> mpred mvar
  IR.AtEOF 0 -> fun "is_all_eof" ["&" <> infd 0, "argc", "argv"]
  IR.AtEOF i -> fun "is_eof" [infd i]
  IR.PendingIPC -> hasPendingIPC
  IR.IsStringEmpty svar -> "!" <> fun "string_len" [string svar]
  IR.PRef p -> pred p

compileMatch m (IR.Match svar re) =
  stmt (matchfun m <> " = &" <> regexfun re) <>
  stmt (mpred m <> " = " <> fun (regexfun re) [matchref m, string svar, "0"])
compileMatch m (IR.MatchLastRE svar) =
  stmt (matchfun m <> " = " <> lastRegex) <>
  stmt (mpred m <> " = " <> fun lastRegex [matchref m, string svar, "0"])
compileMatch m (IR.NextMatch m2 s) =
  stmt (matchfun m <> " = " <> matchfun m2) <>
  stmt (mpred m <> " = " <> fun "next_match" [matchref m, matchref m2, matchfun m2, string s])
compileMatch m (IR.MVarRef m2) =
  sfun "copy_match" [matchref m, matchref m2] <>
  stmt (matchfun m <> " = " <> matchfun m2) <>
  stmt (mpred m <> " = " <> mpred m2)

closeFile i = sfun "close_file" [infd i] <> sfun "close_file" [outfd i]

compileInsn :: IR.Insn e x -> Builder
compileInsn (IR.Label lbl) = label (show lbl)
compileInsn (IR.Branch l) = gotoL l
compileInsn (IR.SetP p value) = stmt (pred p <> " = " <> bool value)
compileInsn (IR.SetS s expr) = setString s expr
compileInsn (IR.SetM m expr) = compileMatch m expr
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
setString t (IR.SConst s) | C.null s = sfun "clear_string" [string t]
                          | True     = sfun "set_str_const" [string t, cstring s, intDec (C.length s)]
setString t (IR.SVarRef svar) = sfun "set_str" [string t, string svar]
setString t (IR.SRandomString) = sfun "random_string" [string t]
setString t (IR.STrans from to s) =
  -- TODO compile transformations into functions. Might require that we add
  -- statefulness to cache them and to output functions outside of main though.
  sfun "trans" [string t, cstring from, cstring to, string s]
setString t (IR.SAppend []) = fun "clear_string" [string t]
setString t (IR.SAppend (x:xs))
    | x == IR.SVarRef t = appendInPlace t xs
    | IR.SVarRef t `elem` xs = error ("Unsafe self-append: " ++ show t ++ " += " ++ show (x:xs))
    | otherwise = setString t x <> appendInPlace t xs
setString t e@(IR.SSubstring _ _ _) =
  sfun "clear_string" [string t] <> appendExpr t e
setString t (IR.SFormatLiteral w s) =
  sfun "format_literal" [string t, intDec w, string s]
setString t (IR.SGetLineNumber) = sfun "format_int" [string t, lineNumber]

appendInPlace _ []     = mempty
appendInPlace t (x:xs) = appendExpr t x <> appendInPlace t xs

-- Some duplication between this and setString, but in practice the more
-- complicated setString expressions are only ever used with setString and
-- never appended. (Appends generally come from substitutions.)
appendExpr t (IR.SConst s)
  | len == 0  = mempty
  | len == 1  = sfun "append_char" [string t, cchar (C.head s)]
  | otherwise = sfun "append_cstr" [string t, cstring s, intDec len]
  where len = C.length s
appendExpr t (IR.SVarRef x) = sfun "append_str" [string t, string x]
appendExpr t (IR.SSubstring s start end) =
  sfun "append_substr" [string t, string s, startix, endix]
  where
      startix = resolveStringIndex s start
      endix = resolveStringIndex s end
appendExpr t (IR.STrans from to s) =
  sfun "append_trans" [string t, cstring from, cstring to, string s]
appendExpr t (IR.SRandomString) = sfun "append_random_string" [string t]
appendExpr _ x = error ("Unimplemented append subexpression: " ++ show x)

resolveStringIndex :: IR.SVar -> IR.SIndex -> Builder
resolveStringIndex s ix = case ix of
  IR.SIStart -> "0"
  IR.SIOffset i -> intDec i
  IR.SIEnd -> fun "string_len" [string s]
  IR.SIMatchStart m -> groupStart m 0
  IR.SIMatchEnd m -> groupEnd m 0
  IR.SIGroupStart m i -> groupStart m i
  IR.SIGroupEnd m i -> groupEnd m i
  where
    groupStart m i = match m <> ".tags[" <> intDec (2 * i) <> "]"
    groupEnd m i = match m <> ".tags[" <> intDec (2 * i + 1) <> "]"

testCompare = False

forceRegcomp = False

needRegcomp (IR.RE _ s ere _) = forceRegcomp ||
    testCompare || not (Regex2C.isCompatible (Regex.parseString ere s))

compileRE r@IR.RE{..} = wrapper body
  where
    ere = reERE
    s = reString
    -- TODO Actually use the set of tags for comparison, so that we can
    -- validate that the used tags optimization doesn't change output.
    usedTags | testCompare = Nothing
             | otherwise   = reUsedTags
    body | needRegexec = regexec
         | testCompare = match_for_compare <> tdfa2c re usedTags <> compare_matches
         | Regex.Literal s <- re = literal (C.pack s)
         | Regex.Char c    <- re = literalChar c
         | otherwise   = tdfa2c re usedTags
    re = Regex.parseString ere s
    isLiteral | Regex.Literal _ <- re = True
              | otherwise             = False
    needRegexec = forceRegcomp || not (Regex2C.isCompatible re)
    res = C.pack $ Regex.reString re
    wrapper b =
        "NOINLINE static bool " <> regexfun r <>
            "(match_t* m, string* s, const size_t orig_offset) {\n" <>
        comment description <>
        comment ("Used tags: " <> showB reUsedTags) <>
        (if isLiteral then comment ("Literal string: " <> showB re) else "") <>
        "bool result = false;\n" <> b <> "return result;\n}\n"
    match m = fun "match_regexp" [m, "s", "orig_offset", regex r]
    -- regcomp is run at start of main so we just need to forward the arguments.
    regexec = stmt ("result = " <> match "m")
    literal s = stmt ("result = " <> fun "match_literal" ["m", "s", "orig_offset", cstring s, intDec (C.length s)])
    literalChar c = stmt ("result = " <> fun "match_char" ["m", "s", "orig_offset", intDec (fromEnum c)])
    match_for_compare =
        stmt "match_t m2" <>
        sfun "clear_match" ["&m2"] <>
        stmt ("const bool result2 = " <> match "&m2")
    compare_matches = sfun "compare_regexp_matches" ["result2", "&m2", "result", "m", "s", "orig_offset", "__PRETTY_FUNCTION__", cstring res]

    description =
        (if ere then "ERE: "  else "BRE: ") <> cstring s <>
        " -> ERE: " <> cstring res <> " (using " <> engineName <> ")"

    engineName | needRegexec = "regexec"
               | isLiteral = "memmem"
               | otherwise = "Regex2C"

tdfa2c re used =
    (if testCompare then sfun "clear_match" ["m"] else mempty) <>
    byteString (Regex2C.tdfa2c used re)
