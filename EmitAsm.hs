{-# LANGUAGE OverloadedStrings,GADTs,TypeFamilies,RankNTypes,TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}

module EmitAsm (compileIR, seditionRuntime) where

import Prelude hiding (pred)
import Compiler.Hoopl as H

import qualified Data.ByteString.Char8 as C
import Data.FileEmbed (embedStringFile)
import Data.String

-- import Debug.Trace

import System.Exit

import AST
import GenAsm
import qualified IR
import IR (Program)
import qualified Regex.Regex as Regex
import qualified Regex.CompileAsm as Regex2Asm

seditionRuntime :: IsString a => a
seditionRuntime = $(embedStringFile "sedition.s")

programHeader program = do
    "default rel\n" :: Builder ()
    foldMap extern externalSymbols
    section ".bss"
    declare ptrSize lastRegex
    declare ptrSize "argc" -- Actually just an int
    declare ptrSize "argv"
    foldMap (declare regexvarSize . regexvar) regexps
    foldMap (declare stringSize . stringvar) strings
    foldMap (declare matchSize . match) matches
    foldMap (declare ptrSize . matchfun) matches
    foldMap (declare boolSize . pred) preds
    foldMap (declare ptrSize . infdvar) files
    foldMap (declare ptrSize . outfdvar) files
    foldMap (declare boolSize . mpred) matches
    section ".text"
    foldMap compileRE allRegexps
    "global main\nmain:\n" :: Builder ()
    prologue
    storeAddr "argc" arg0
    storeAddr "argv" arg1
    sfun "enable_stats_on_sigint" []
    foldMap initRegexp regexps
    sfun "next_input" [loadAddr "argc", loadAddr "argv"]
    storeAddr (infdvar 0) res0
    loadAddr "stdout" res0
    storeAddr (outfdvar 0) res0
  where
    declare t var = var <> ":\n" <> "resb " <> intDec t <> "\n"
    preds = IR.allPredicates program
    strings = IR.allStrings program
    files = IR.allFiles program
    matches = IR.allMatches program
    allRegexps = IR.allRegexps program
    regexps = filter needRegcomp allRegexps
    initRegexp re@IR.RE{..} = sfun "compile_regexp" [regex re, setCString reString, setBool reERE]

programFooter program = label ".exit" <>
    op "mov" ["rbp", reg64 res0] <>
    foldMap closeFile files <>
    foldMap freeRegex regexps <>
    foldMap freeString strings <>
    sfun "tdfa2c_statistics" [] <>
    op "mov" [reg64 res0, "rbp"] <>
    epilogue
  where
    strings = IR.allStrings program
    files = IR.allFiles program
    regexps = filter needRegcomp (IR.allRegexps program)
    freeRegex re = sfun "free_regexp" [regex re]
    freeString s = sfun "free_string" [string s]

compileIR :: Bool -> H.Label -> Program -> S
compileIR _ipc entry program_in = toByteString $
  programHeader program
  <> gotoL entry
  <> foldMap compileBlock blocks
  <> programFooter program
  where
    program@(GMany _ blocks _) = IR.numberAllRegexps program_in

compileBlock block = fold (mempty :: Builder ())
  where
    fold :: Builder () -> Builder ()
    fold = foldBlockNodesF f block
    f :: forall e x . IR.Insn e x -> Builder () -> Builder ()
    f insn builder = builder <> compileInsn insn

string (IR.SVar s) = setAddr ("S" <> intDec s)
stringvar (IR.SVar s) = "S" <> intDec s
pred (IR.Pred p) = "P" <> intDec p
match (IR.MVar m) = "M" <> intDec m
matchref (IR.MVar m) = setAddr ("M" <> intDec m)
matchfun (IR.MVar m) = "MF" <> intDec m
mpred (IR.MVar m) = "MP" <> intDec m
infdvar i = "inF" <> idIntDec i
outfdvar i = "outF" <> idIntDec i
infd i = loadAddr (infdvar i)
outfd i = loadAddr (outfdvar i)

regexvar IR.RE{..} = "RE" <> intDec reID
regexfun IR.RE{..} = "match_RE" <> intDec reID
regex r = setAddr (regexvar r)

lineNumber = "lineNumber"
-- hasPendingIPC = "hasPendingIPC" :: Builder ()
lastRegex = "lastRegex"

compileCond cond t = case cond of
  IR.Line l -> op "cmp" [dword_ptr lineNumber, intDec l] <> je t
  -- if lineNumber > l
  IR.EndLine l -> op "cmp" [dword_ptr lineNumber, intDec l] <> ja t
  IR.IsMatch mvar -> op "cmp" [byte_ptr (mpred mvar), intDec 0] <> jne t
  IR.AtEOF 0 -> sfun "is_all_eof" [setAddr (infdvar 0), loadAddr "argc", loadAddr "argv"] <> jtrue res0 t
  IR.AtEOF i -> sfun "is_eof" [infd i] <> jtrue res0 t
  IR.PendingIPC -> mempty -- hasPendingIPC
  IR.IsStringEmpty svar ->
    -- TODO Unnecessary to load into a register, cmp to 0 instead.
    setStringLen svar res0 <> jz res0 t
  IR.PRef p -> loadInt8 (pred p) res0 <> jtrue res0 t

compileMatch m (IR.Match svar re) = do
  storeCAddr (matchfun m) res0 (regexfun re)
  sfun (regexfun re) [matchref m, string svar, setInt 0]
  storeInt8 (mpred m) res0
compileMatch m (IR.MatchLastRE svar) = do
  loadAddr lastRegex res0
  storeAddr (matchfun m) res0
  sfun (regA res0) [matchref m, string svar, setInt 0]
  storeInt8 (mpred m) res0
compileMatch m (IR.NextMatch m2 s) = do
  loadAddr (matchfun m2) res0
  storeAddr (matchfun m) res0
  sfun "next_match" [matchref m, matchref m2, loadAddr (matchfun m2), string s]
  storeInt8 (mpred m) res0
compileMatch m (IR.MVarRef m2) = do
  sfun "copy_match" [matchref m, matchref m2]
  loadAddr (matchfun m2) res0
  loadInt8 (mpred m2) res1
  storeAddr (matchfun m) res0
  storeInt8 (mpred m) res1

closeFile i = sfun "close_file" [infd i] <> sfun "close_file" [outfd i]

compileInsn :: IR.Insn e x -> Builder ()
compileInsn (IR.Label lbl) = label (lblname lbl)
compileInsn (IR.Branch l) = gotoL l
compileInsn (IR.SetP p value) = storeBool (pred p) value
compileInsn (IR.SetS s expr) = setString s expr
compileInsn (IR.SetM m expr) = compileMatch m expr
compileInsn (IR.If c t f) = compileCond c (lblname t) <> gotoL f
compileInsn (IR.Listen i maybeHost port) =
  sfun "sock_listen" [infd i, chost maybeHost, setInt port]
  where
    chost (Just host) = setCString host
    chost Nothing = setInt 0 -- setNull
compileInsn (IR.Accept s c) = do
  sfun "accept" [infd s]
  storeAddr (infdvar c) res0
compileInsn (IR.Fork entry next) =
  sfun "FORK" [setAddr (lblname entry), setAddr (lblname next)]
compileInsn (IR.Redirect i j) = do
  -- Close i, copy j to i, then clear out j
  closeFile i
  setInt 0 arg2
  loadAddr (infdvar j) arg0
  loadAddr (outfdvar j) arg1
  storeAddr (infdvar i) arg0
  storeAddr (outfdvar i) arg1
  storeAddr (infdvar j) arg2
  storeAddr (outfdvar j) arg2
compileInsn (IR.CloseFile i) = closeFile i

-- Done in initialization
compileInsn (IR.SetLastRE re) = setLastRegex re
compileInsn (IR.Message s) = sfun "send_message" [string s]

compileInsn (IR.Print i s) = sfun "print" [outfd i, string s]
compileInsn (IR.Quit code) =
    setInt (c_code code) rax <> goto ".exit"
  where
    c_code (ExitFailure n) = n
    c_code ExitSuccess = 0
compileInsn (IR.Comment s) = comment (string8 s)

compileInsn (IR.Wait i) = sfun "wait_or_event" [infd i]
compileInsn (IR.Read svar 0) = do
  repeat <- emitNewLabel
  done <- newLabel
  do
    sfun "read_line" [string svar, infd 0]
    jnz res0 done
  do
    -- should not touch output file
    sfun "close_file" [infd 0]
    sfun "next_input" [loadAddr "argc", loadAddr "argv"]
    storeAddr (infdvar 0) res0
    jz res0 ".exit"
    goto repeat
  label done
compileInsn (IR.Read svar i) = sfun "read_line" [string svar, infd i]
compileInsn (IR.GetMessage svar) = sfun "get_message" [string svar]

compileInsn (IR.OpenFile fd write path) =
    sfun "close_file" [loadAddr fdvar] <>
    sfun "open_file" [setCString path, setBool write] <>
    storeAddr fdvar res0
  where
    fdvar = (if write then outfdvar else infdvar) fd
compileInsn (IR.ReadFile svar fd) = sfun "read_file" [string svar, infd fd]
compileInsn (IR.ShellExec svar) = sfun "shell_exec" [string svar]

--compileInsn cmd = fatal ("compileInsn: Unhandled instruction " ++ show cmd)

setLastRegex re = storeCAddr lastRegex res0 (regexfun re)

setString :: IR.SVar -> IR.StringExpr -> Builder ()
setString t (IR.SConst s) | C.null s = sfun "clear_string" [string t]
                          | True     = sfun "set_str_const" [string t, setCString s, setInt (C.length s)]
setString t (IR.SVarRef svar) = sfun "set_str" [string t, string svar]
setString t (IR.SRandomString) = sfun "random_string" [string t]
setString t (IR.STrans from to s) =
  -- TODO compile transformations into functions. Might require that we add
  -- statefulness to cache them and to output functions outside of main though.
  sfun "trans" [string t, setCString from, setCString to, string s]
setString t (IR.SAppend []) = sfun "clear_string" [string t]
setString t (IR.SAppend (x:xs))
    | x == IR.SVarRef t = appendInPlace t xs
    | IR.SVarRef t `elem` xs = error ("Unsafe self-append: " ++ show t ++ " += " ++ show (x:xs))
    | otherwise = setString t x <> appendInPlace t xs
setString t e@(IR.SSubstring _ _ _) =
  sfun "clear_string" [string t] <> appendExpr t e
setString t (IR.SFormatLiteral w s) =
  sfun "format_literal" [string t, setInt w, string s]
setString t (IR.SGetLineNumber) =
  sfun "format_int" [string t, loadInt32 lineNumber]

appendInPlace _ []     = mempty
appendInPlace t (x:xs) = appendExpr t x <> appendInPlace t xs

-- Some duplication between this and setString, but in practice the more
-- complicated setString expressions are only ever used with setString and
-- never appended. (Appends generally come from substitutions.)
appendExpr t (IR.SConst s)
  | len == 0  = mempty
  | len == 1  = sfun "append_char" [string t, setCChar (C.head s)]
  | otherwise = sfun "append_cstr" [string t, setCString s, setInt len]
  where len = C.length s
appendExpr t (IR.SVarRef x) = sfun "append_str" [string t, string x]
appendExpr t (IR.SSubstring s start end) =
  sfun "append_substr" [string t, string s, startix, endix]
  where
      startix = resolveStringIndex s start
      endix = resolveStringIndex s end
appendExpr t (IR.STrans from to s) =
  sfun "append_trans" [string t, setCString from, setCString to, string s]
appendExpr t (IR.SRandomString) = sfun "append_random_string" [string t]
appendExpr _ x = error ("Unimplemented append subexpression: " ++ show x)

setStringLen s reg = loadAddr (offset (stringvar s) stringLenOffset) reg

resolveStringIndex :: IR.SVar -> IR.SIndex -> Reg -> Builder ()
resolveStringIndex s ix = case ix of
  IR.SIStart -> setInt 0
  IR.SIOffset i -> setInt i
  IR.SIEnd -> setStringLen s
  IR.SIMatchStart m -> groupStart m 0
  IR.SIMatchEnd m -> groupEnd m 0
  IR.SIGroupStart m i -> groupStart m i
  IR.SIGroupEnd m i -> groupEnd m i
  where
    groupStart m i = loadAddr (offset (match m) (matchTagOffset (2 * i)))
    groupEnd m i = loadAddr (offset (match m) (matchTagOffset (2 * i + 1)))

forceRegcomp = False

needRegcomp (IR.RE _ s ere _) = forceRegcomp ||
    not (Regex2Asm.isCompatible (Regex.parseString ere s))

compileRE r@IR.RE{..} = wrapper body
  where
    ere = reERE
    s = reString
    usedTags = reUsedTags
    body | needRegexec = regexec
         | Regex.Literal s <- re = literal (C.pack s)
         | Regex.Char c    <- re = literalChar c
         | otherwise   = tdfa2asm re usedTags
    re = Regex.parseString ere s
    isLiteral | Regex.Literal _ <- re = True
              | otherwise             = False
    needRegexec = forceRegcomp || not (Regex2Asm.isCompatible re)
    res = C.pack $ Regex.reString re
    wrapper b =
        label (regexfun r) <>
        comment "(match_t* m, string* s, const size_t orig_offset)" <>
        comment description <>
        comment ("Used tags: " <> showB reUsedTags) <>
        (if isLiteral then comment ("Literal string: " <> showB re) else "") <>
        prologue <> b <> epilogue
    -- regcomp is run at start of main so we just need to forward the arguments.
    regexec = sfun "match_regexp" [already arg0, already arg1, already arg2, regex r]
    literal s = sfun "match_literal" [already arg0, already arg1, already arg2, setCString s, setInt (C.length s)]
    literalChar c = sfun "match_char" [already arg0, already arg1, already arg2, setInt (fromEnum c)]

    description =
        (if ere then "ERE: "  else "BRE: ") <> showB s <>
        " -> ERE: " <> showB res <> " (using " <> engineName <> ")"

    engineName | needRegexec = "regexec"
               | isLiteral = "memmem"
               | otherwise = "Regex2Asm"

tdfa2asm re used = byteString (Regex2Asm.tdfa2asm used re)
