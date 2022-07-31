{-# LANGUAGE OverloadedStrings,GADTs,TypeFamilies,RankNTypes #-}

module Compile (compileIR) where

import Prelude hiding (pred)
import Compiler.Hoopl as H

import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy.Char8 as L
import Data.ByteString.Builder as B

import System.Exit

import AST
import qualified IR
import IR (Program)

-- TODO Include re2c and maxnmatch
-- Include the "runtime" (or inline it)
-- Declare global variables
-- Find and declare all strings, predicates and files
programHeader program = "\n\
    \#include <regex.h>\n\
    \#include <stdbool.h>\n\
    \#include <stdio.h>\n\
    \struct string { char* buf; size_t n; };\n\
    \static int lineNumber;\n\
    \static bool hasPendingIPC;\n" <>
    foldMap (declare "bool" pred) preds <>
    foldMap (declare "string" stringvar) strings <>
    foldMap (declare "FILE*" fd) files <>
    "int main() {"
  where
    declare t s var = stmt ("static " <> t <> " " <> s var)
    preds = IR.allPredicates program
    strings = IR.allStrings program
    files = IR.allFiles program

programFooter = "\n;\n}\n"

compileIR :: Bool -> H.Label -> Program -> S
compileIR _ipc entry program = L.toStrict . toLazyByteString $
  programHeader program
  <> goto entry
  <> foldMap compileBlock blocks
  <> programFooter
  where GMany _ blocks _ = program

-- compileBlock :: Block IR.Insn e x -> Builder
compileBlock block = fold (string8 "\n")
  where
    fold :: Builder -> Builder
    fold = foldBlockNodesF f block
    f :: forall e x . IR.Insn e x -> Builder -> Builder
    f insn builder = compileInsn insn <> builder

goto :: H.Label -> Builder
goto l = stmt ("goto " <> label l)

label l = showB l
string (IR.SVar s) = "&S" <> intDec s
stringvar (IR.SVar s) = "S" <> intDec s
pred (IR.Pred p) = "P" <> intDec p
fd i = "F" <> intDec i
lineNumber = "lineNumber"
hasPendingIPC = "hasPendingIPC"

cstring s = "\"" <> foldMap quoteC (C.unpack s) <> "\""
  where
    quoteC '\n' = "\\n"
    quoteC '\"' = "\\\""
    quoteC c = char8 c

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
unimpl what extra = comment ("UNIMPLEMENTED: " <> what <> ": " <> showB extra)

compileCond cond = case cond of
  IR.Bool b -> showB b
  IR.Line l -> intDec l <> " == " <> lineNumber
  IR.EndLine l -> intDec l <> " < " <> lineNumber
  IR.Match svar re -> fun "checkRE" [string svar, cstring (reString re)]
  -- tracking the last regexp with re2c is, eugh... Should introduce match/RE
  -- variables earlier, so we can map regexps in the code to functions in the
  -- compiled output.
  IR.MatchLastRE svar -> fun "checkLastRE" [string svar]
  IR.AtEOF i -> fun "isEOF" [fd i]
  IR.PendingIPC -> hasPendingIPC

compileInsn :: IR.Insn e x -> Builder
compileInsn (IR.Label lbl) = label lbl <> ":\n"
compileInsn (IR.Branch l) = goto l
compileInsn (IR.SetP p cond) = pred p <> " = " <> compileCond cond <> ";\n"
compileInsn (IR.SetS s expr) = stmt (setString s expr)
compileInsn (IR.If p t f) = fun "if" [pred p] <> goto t <> "else " <> goto f
compileInsn (IR.Listen i maybeHost port) =
  sfun "sock_listen" [fd i, chost maybeHost, intDec port]
  where
    chost (Just host) = cstring host
    chost Nothing = "NULL"
compileInsn (IR.Accept s c) = stmt (fd c <> " = " <> fun "accept" [fd s])
compileInsn (IR.Fork entry next) = sfun "FORK" [label entry, label next]
compileInsn (IR.Redirect i j) = sfun "redirect_file" [fd i, fd j]
compileInsn (IR.CloseFile i) = sfun "close_file" [fd i]

compileInsn (IR.SetLastRE re) = setLastRegex re
compileInsn (IR.Message s) = sfun "send_message" [string s]

compileInsn (IR.PrintConstS i s) = sfun "file_printf" [fd i, "%s\n", cstring s]
compileInsn (IR.Print i s) = sfun "print" [fd i, string s]
-- TODO Make the literal-formatting a string function instead, so that this is
-- not a special Print operation. Likewise for PrintLineNumber.
compileInsn (IR.PrintLiteral w i s) =
  sfun "print_lit" [fd i, intDec w, string s]
compileInsn (IR.PrintLineNumber i) =
    sfun "file_printf" [fd i, cstring "%d\n", lineNumber]
compileInsn (IR.Quit code) = stmt (fun "exit" [c_code code])
  where
    c_code (ExitFailure n) = intDec n
    c_code ExitSuccess = "EXIT_SUCCCESS"
compileInsn (IR.Comment s) = comment (string8 s)

compileInsn (IR.Wait i) = sfun "wait_or_event" [fd i]
compileInsn (IR.Read svar i) = sfun "read_line" [string svar, fd i]
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

setLastRegex re = comment ("Set last regexp to: " <> showB re)

setString :: IR.SVar -> IR.StringExpr -> Builder
setString t (IR.SConst s) = fun "store_cstr" [string t, cstring s]
setString t (IR.SVarRef svar) = fun "copy" [string t, string svar]
setString t (IR.SRandomString) = fun "randomString" [string t]
-- TODO Consider lowering substitutions earlier, e.g. having getmatch and append
-- operations and something for global substitutions.
setString t expr@(IR.SSubst _svar _sub _stype) =
  unimpl "SSubst" (t, expr)
setString t (IR.STrans from to s) =
  fun "trans" [string t, cstring from, cstring to, string s]
setString t (IR.SAppendNL a b) = fun "concat_newline" (map string [t, a, b])
