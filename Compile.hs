{-# LANGUAGE OverloadedStrings,GADTs,TypeFamilies,RankNTypes,TemplateHaskell #-}

module Compile (compileIR) where

import Prelude hiding (pred)
import Compiler.Hoopl as H

import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy.Char8 as L
import Data.ByteString.Builder as B
import Data.FileEmbed (embedStringFile)
import Data.Word

import System.Exit

import AST
import qualified IR
import IR (Program)

seditionRuntime = $(embedStringFile "sedition.h")

programHeader ere program =
    "int main(int argc, const char *argv[]) {\n\
    \bool hasPendingIPC = false;\n\
    \const char* lastRegex = NULL;\n" <>
    foldMap (declare "bool" pred " = false") preds <>
    foldMap (declare "string" stringvar mempty) strings <>
    foldMap (declare "FILE*" infd " = NULL") files <>
    foldMap (declare "FILE*" outfd " = NULL") files <>
    foldMap (declare "match_t" match mempty) matches <>
    foldMap (clear match) matches <>
    foldMap (clear stringvar) strings <>
    "const int re_cflags = " <> cflags <> ";\n" <>
    infd 0 <> " = next_input(argc, argv);\n" <>
    outfd 0 <> " = stdout;\n"
  where
    declare t s init var = t <> " " <> s var <> init <> ";\n"
    clear s var = sfun "memset" ["&" <> s var, "0", fun "sizeof" [s var]]
    preds = IR.allPredicates program
    strings = IR.allStrings program
    files = IR.allFiles program
    matches = IR.allMatches program
    cflags | ere       = "REG_EXTENDED"
           | otherwise = "0"

programFooter = "}\n"

compileIR :: Bool -> Bool -> H.Label -> Program -> S
compileIR _ipc ere entry program = L.toStrict . toLazyByteString $
  seditionRuntime
  <> programHeader ere program
  <> goto entry
  <> foldMap compileBlock blocks
  <> programFooter
  where GMany _ blocks _ = program

-- compileBlock :: Block IR.Insn e x -> Builder
compileBlock block = fold (mempty :: Builder)
  where
    fold :: Builder -> Builder
    fold = foldBlockNodesF f block
    f :: forall e x . IR.Insn e x -> Builder -> Builder
    f insn builder = builder <> compileInsn insn

goto :: H.Label -> Builder
goto l = stmt ("goto " <> label l)

label l = showB l
string (IR.SVar s) = "&S" <> intDec s
stringvar (IR.SVar s) = "S" <> intDec s
pred (IR.Pred p) = "P" <> intDec p
match (IR.MVar m) = "M" <> intDec m
matchref (IR.MVar m) = "&M" <> intDec m
infd i = "inF" <> intDec i
outfd i = "outF" <> intDec i
lineNumber = "lineNumber"
hasPendingIPC = "hasPendingIPC"
lastRegex = "lastRegex"
re_cflags = "re_cflags"

cstring s = "\"" <> foldMap quoteC (C.unpack s) <> "\""
  where
    quoteC '\n' = "\\n"
    quoteC '\"' = "\\\""
    quoteC '\\' = "\\\\"
    quoteC c
      -- Add an extra "" pair to terminate the hex escape in case it is
      -- followed by a valid hex digit.
      | length (show c) /= 3 = "\\x" <> word8HexFixed (toWord8 c) <> "\"\""
    quoteC c = char8 c
    toWord8 :: Char -> Word8
    toWord8 = fromIntegral . fromEnum

showB x = string8 (show x)
intercalateB _   [] = mempty
intercalateB sep (x:xs) = x <> go sep xs
  where
    go _   []     = mempty
    go sep (x:xs) = sep <> x <> go sep xs

fun function args = function <> "(" <> intercalateB ", " args <> ")"
sfun function args = stmt (fun function args)
stmt builder = builder <> ";\n"
comment builder = "// " <> builder <> "\n"

compileCond cond = case cond of
  IR.Bool True -> "true"
  IR.Bool False -> "false"
  IR.Line l -> intDec l <> " == " <> lineNumber
  IR.EndLine l -> intDec l <> " < " <> lineNumber
  IR.IsMatch mvar -> match mvar <> ".result"
  IR.AtEOF 0 -> fun "is_all_eof" ["&" <> infd 0, "argc", "argv"]
  IR.AtEOF i -> fun "is_eof" [infd i]
  IR.PendingIPC -> hasPendingIPC

cIf cond t f = fun "if" [cond] <> "{\n  " <> t <> "} else {\n  " <> f <> "}\n"
--cWhen cond t = fun "if" [cond] <> "{\n  " <> t <> "}\n"
cWhile cond t = fun "while" [cond] <> "{\n  " <> t <> "}\n"

compileMatch m (IR.Match svar re) = fun "match_regexp" [matchref m, string svar, cstring (reString re), re_cflags, "0"]
compileMatch m (IR.MatchLastRE svar) = fun "match_regexp" [matchref m, string svar, lastRegex, re_cflags, "0"]
compileMatch m (IR.NextMatch m2 s) = fun "next_match" [matchref m, matchref m2, string s]
compileMatch m (IR.MVarRef m2) = fun "copy_match" [matchref m, matchref m2]

closeFile i = sfun "close_file" [infd i] <> sfun "close_file" [outfd i]

compileInsn :: IR.Insn e x -> Builder
compileInsn (IR.Label lbl) = label lbl <> ":\n"
compileInsn (IR.Branch l) = goto l
compileInsn (IR.SetP p cond) = stmt (pred p <> " = " <> compileCond cond)
compileInsn (IR.SetS s expr) = stmt (setString s expr)
compileInsn (IR.SetM m expr) = stmt (compileMatch m expr)
compileInsn (IR.If p t f) = cIf (pred p) (goto t) (goto f)
compileInsn (IR.Listen i maybeHost port) =
  sfun "sock_listen" [infd i, chost maybeHost, intDec port]
  where
    chost (Just host) = cstring host
    chost Nothing = "NULL"
compileInsn (IR.Accept s c) = stmt (infd c <> " = " <> fun "accept" [infd s])
compileInsn (IR.Fork entry next) = sfun "FORK" [label entry, label next]
compileInsn (IR.Redirect i j) =
  closeFile i <>
  stmt (outfd i <> " = " <> outfd j) <>
  stmt (infd i <> " = " <> outfd j) <>
  stmt (outfd j <> " = NULL") <>
  stmt (infd j <> " = NULL")
compileInsn (IR.CloseFile i) = closeFile i

compileInsn (IR.SetLastRE re) = setLastRegex re
compileInsn (IR.Message s) = sfun "send_message" [string s]

compileInsn (IR.Print i s) = sfun "print" [outfd i, string s]
compileInsn (IR.Quit code) = stmt (fun "exit" [c_code code])
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
        "if (" <> infd 0 <> " == NULL) exit(0);\n"
compileInsn (IR.Read svar i) = sfun "read_line" [string svar, infd i]
compileInsn (IR.GetMessage svar) = sfun "get_message" [string svar]

-- Not quite right - all referenced files should be created/truncated before
-- the first written line, then all subsequent references continue writing
-- without reopening the file.
-- Probably the IR step should assign a file descriptor for each used output
-- file, generate code to open them on startup and then this should be done
-- through (Print fd) instead.
compileInsn (IR.WriteFile path svar) = sfun "write_file" [cstring path, string svar]
compileInsn (IR.ShellExec svar) = sfun "shell_exec" [string svar]

--compileInsn cmd = fatal ("compileInsn: Unhandled instruction " ++ show cmd)

setLastRegex re = stmt (lastRegex <> " = " <> cstring (reString re))

setString :: IR.SVar -> IR.StringExpr -> Builder
setString t (IR.SConst s) = fun "store_cstr" [string t, cstring s, intDec (C.length s)]
setString t (IR.SVarRef svar) = fun "copy" [string t, string svar]
setString t (IR.SRandomString) = fun "random_string" [string t]
setString t (IR.STrans from to s) =
  -- TODO compile transformations into functions. Might require that we add
  -- statefulness to cache them and to output functions outside of main though.
  fun "trans" [string t, cstring from, cstring to, string s]
setString t (IR.SAppendNL a b) = fun "concat_newline" (map string [t, a, b])
setString t (IR.SAppend a b) = fun "concat" (map string [t, a, b])
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
  IR.SIEnd -> stringvar s <> ".len"
  IR.SIMatchStart m -> groupStart m 0
  IR.SIMatchEnd m -> groupEnd m 0
  IR.SIGroupStart m i -> groupStart m i
  IR.SIGroupEnd m i -> groupEnd m i
  where
    groupStart m i = match m <> ".matches[" <> intDec i <> "].rm_so"
    groupEnd m i = match m <> ".matches[" <> intDec i <> "].rm_eo"
