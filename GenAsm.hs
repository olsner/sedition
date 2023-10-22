{-# LANGUAGE OverloadedStrings,GADTs,TypeFamilies,RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module GenAsm where

import qualified Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer

import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy.Char8 as L
import qualified Data.ByteString.Builder as B
import Data.ByteString.Builder as B hiding (Builder, string8, intDec, byteString)
import Data.String

-- TODO Connect to an ABI or something
data Reg = Reg {
  fullRegName :: C.ByteString,
  regName32 :: C.ByteString,
  regName16 :: C.ByteString,
  regName8 :: C.ByteString } deriving (Show, Ord, Eq)

baseReg name byte = Reg ("r" <> name) ("e" <> name) name byte
regReg name = baseReg name (name <> "l")
numReg name = Reg name (name <> "d") (name <> "w") (name <> "l")

rax, rdx, rcx, rbx, rdi, rsi, r8, r9 :: Reg
rax = baseReg "ax" "al"
rdx = baseReg "dx" "dl"
rcx = baseReg "cx" "cl"
rbx = baseReg "bx" "bl"
rdi = regReg "di"
rsi = regReg "si"
r8 = numReg "r8"
r9 = numReg "r9"
r10 = numReg "r10"
r11 = numReg "r11"
r12 = numReg "r12"

-- Shorthands to make things slightly less ABI dependent
res0 = rax
res1 = rdx
arg0 = rdi
arg1 = rsi
arg2 = rdx
arg3 = rcx
arg4 = r8
arg5 = r9
argRegs = [arg0, arg1, arg2, arg3, arg4, arg5]

-- TODO Some of these are callee-save, I think?
tmp0 = r10
tmp1 = r11
tmp2 = r12

-- We don't use a frame pointer, but do it anyway to align stack to 16-byte
-- boundary. It's exactly misaligned by 8 bytes (one return address) on entry
-- to any function.
prologue = op1 "push" "rbp"
epilogue = op1 "pop" "rbp" <> op0 "ret"

type Builder a = WriterT B.Builder (State Int) a

instance Semigroup (Builder ()) where
  x <> y = x >> y
instance Monoid (Builder ()) where
  mempty = return ()
  mappend = (<>)
instance IsString (Builder ()) where
  fromString = tell . fromString

regA, reg64, reg32, reg16, reg8 :: Reg -> Builder ()
-- | Register, sized for holding an address
regA = byteString . fullRegName
-- | Register, sized for holding a 64-bit value
reg64 = byteString . fullRegName
reg32 = byteString . regName32
reg16 = byteString . regName16
reg8 = byteString . regName8
string8 :: String -> Builder ()
string8 = tell . B.string8
intDec :: Int -> Builder ()
intDec = tell . B.intDec
-- word8HexFixed = Builder . B.word8HexFixed
byteString :: C.ByteString -> Builder ()
byteString = tell . B.byteString

setInt :: Int -> Reg -> Builder ()
setInt val reg
  | 0 <- val  = op "xor" [reg32 reg, reg32 reg]
  -- TODO Check the range and switch to movabs if too large.
  -- TODO Check sign/zero-extension
  | otherwise = op "mov" [reg32 reg, intDec val]
  -- | otherwise = error (show val ++ " is out of range")

setCChar val = setInt (fromEnum val)

setCString :: C.ByteString -> Reg -> Builder ()
setCString s reg = do
  l <- emitCString s
  setAddr l reg
setAddr :: Builder () -> Reg -> Builder ()
setAddr var reg = op "lea" [regA reg, byte_ptr var]

loadInt8 var reg = op "movsx" [reg32 reg, byte_ptr var]
loadUInt8 var reg = op "movzx" [reg32 reg, byte_ptr var]
loadInt32 var reg = op "mov" [reg32 reg, mem var]
loadInt64 var reg = op "mov" [reg64 reg, mem var]
loadAddr var reg = op "mov" [regA reg, mem var]

already src dst | dst == src = mempty
                | otherwise  = error ("Expected no movement required but " ++
                                      show src ++ " is not " ++ show dst)

copy src dst = op "mov" [dst, src]

-- TODO Differentiate variables that need to use RIP-relative adddressing from
-- other expressions that would not need that. Otherwise we cannot produce
-- PIE output. Seems to work with -no-pie for now...
storeInt8 var reg = op "mov" [mem var, reg8 reg]
storeInt32 var reg = op "mov" [mem var, reg32 reg]
storeInt64 var reg = op "mov" [mem var, reg64 reg]
storeAddr var reg = op "mov" [mem var, regA reg]
-- load address separately with a RIP-relative address and then store the
-- result. This makes the output PIE compatible.
storeCAddr var reg addr = setAddr addr reg <> storeAddr var reg

storeImm8 var val = op "mov" [byte_ptr var, intDec val]
storeBool var val = storeImm8 var (fromEnum val)

mem x = "[" <> x <> "]"
byte_ptr x = "byte [" <> x <> "]"
dword_ptr x = "dword [" <> x <> "]"
qword_ptr x = "qword [" <> x <> "]"

section :: Builder () -> Builder ()
section s = "section " <> s <> "\n"

emitCString s = do
  section ".rodata"
  l <- emitNewLabel
  "db " <> dbstring s <> "\n"
  section ".text"
  return l

toByteString :: Builder () -> C.ByteString
toByteString = L.toStrict . B.toLazyByteString . flip evalState 1 . execWriterT

newLabel :: Builder (Builder ())
newLabel = lift (get >>= \l -> put (succ l) >> return (".T" <> showB l))

emitNewLabel :: Builder (Builder ())
emitNewLabel = newLabel >>= (\l -> label l >> return l)

label :: Builder () -> Builder ()
label name = name <> ":\n"
goto name = op "jmp" [name]
gotoL :: H.Label -> Builder ()
gotoL l = goto (lblname l)
lblname l = "." <> showB l

cmp x y = op "cmp" [x, y]
inc = op1 "inc"
sub dst val = op "sub" [dst, val]

-- TODO Add variants so we can use reg32, e.g. special for Bool and/or a
-- special calling convention for bool-returning functions.
jz reg label = op "test" [reg64 reg, reg64 reg] >> je label
jnz reg label = op "test" [reg64 reg, reg64 reg] >> jne label

jfalse reg label = op "test" [reg8 reg, reg8 reg] >> je label
jtrue reg label = op "test" [reg8 reg, reg8 reg] >> jne label

je label = op1 "je" label
jne label = op1 "jne" label

-- Above/Below: *Unsigned* comparisons
jb label = op1 "jb" label
jbe label = op1 "jbe" label
ja label = op1 "ja" label
jae label = op1 "jae" label
-- Less/Greater: *Signed* oomparisons

idIntDec i | i >= 0    = intDec i
           | otherwise = "_" <> intDec (negate i)

cchar :: Char -> Builder ()
cchar = showB . fromEnum
dbstring :: C.ByteString -> Builder ()
dbstring s = "'" <> foldMap quoteC (C.unpack s) <> "', 0"
  where
    quoteC c | special c = "', " <> cchar c <> ", '"
    quoteC c = tell (char8 c)
    special '\n' = True
    special '\t' = True
    special '\'' = True
    special '\\' = False
    special c = length (show c) /= 3

setBool :: Bool -> Reg -> Builder ()
setBool x = setInt (fromEnum x)

showB :: Show a => a -> Builder ()
showB x = string8 (show x)

-- TODO intercalateM since it's not builder-specific
intercalateB :: Monoid a => a -> [a] -> a
intercalateB _   [] = mempty
intercalateB sep (x:xs) = x <> foldMap (sep <>) xs

-- fun :: Builder -> [Builder] -> Builder ()
-- fun function args = function <> "(" <> intercalateB ", " args <> ")"

sfun :: Builder () -> [Reg -> Builder ()] -> Builder ()
sfun function argFuns = do
  when (length argFuns > length argRegs) (error "Too many arguments")
  sequence_ (zipWith id argFuns argRegs)
  op1 "call" function

stmt :: Builder () -> Builder ()
stmt builder = builder <> "\n"

op0 :: Builder () -> Builder ()
op0 insn = "\t" <> insn <> "\n"
op1 :: Builder () -> Builder () -> Builder ()
op1 insn operand = op insn [operand]
op :: Builder () -> [Builder ()] -> Builder ()
op insn ops = "\t" <> insn <> "\t" <> intercalateB ", " ops <> "\n"

comment :: Builder () -> Builder ()
comment builder = "\t; " <> builder <> "\n"

-- cIf :: Builder -> Builder -> Builder -> Builder ()
-- cIf cond t f = fun "if " [cond] <> " {\n  " <> t <> "} else {\n  " <> f <> "}\n"
-- cWhen cond t = fun "if " [cond] <> " {\n  " <> t <> "}\n"
-- cWhile cond t = fun "while" [cond] <> "{\n  " <> t <> "}\n"

ptrSize = 8 :: Int
offsetSize = ptrSize
boolSize = 1 :: Int

regexvarSize = 64 :: Int
-- struct string { char* buf; size_t len; size_t alloc; };
stringSize = 3 * ptrSize
-- ptrdiff_t tags[2 * 10]
matchSize = 2 * 10 * offsetSize

stringBufOffset = 0 :: Int
stringLenOffset = 8 :: Int
offset var offs = var <> " + " <> intDec offs
matchTagOffset i = 8 * i :: Int

externalSymbols =
  -- functions
  C.words "enable_stats_on_sigint compile_regexp next_input stdout match_char match_literal match_regexp clear_match copy_match next_match print_match clear_string append_char append_str append_substr append_cstr set_cstrz set_str set_str_const print wait_or_event is_all_eof is_eof read_line open_file read_file close_file free_regexp free_string tdfa2c_statistics random_string append_random_string format_int format_literal trans append_trans" ++
  -- variables
  C.words "lineNumber"

extern s = "extern " <> byteString s <> "\n"

matcherAssemblyHeader = do
  "default rel\n" :: Builder ()
  foldMap extern externalSymbols
  section ".bss"
  "m: resb " <> intDec matchSize <> "\n"
  "s: resb " <> intDec stringSize <> "\n"
  "argc: resq 1\n" :: Builder ()
  "argv: resq 1\n" :: Builder ()
  section ".text"
  label "match"
  prologue
  sfun "clear_match" [setAddr "m"]

matcherAssemblyFooter = do
  epilogue
  "global main\n" :: Builder ()
  label "main"
  prologue
  storeAddr "argc" rdi
  storeAddr "argv" rsi
  setInt 0 rbx
  label ".arg_loop"
  do
    inc (regA rbx)
    cmp (regA rbx) (mem "argc")
    jae ".end"
    loadAddr "argv" arg1
    sfun "set_cstrz" [setAddr "s", loadAddr (regA arg1 <> "+ 8 *" <> regA rbx)]
    sfun "match" [setAddr "m", setAddr "s", setInt 0]
    copy (reg32 res0) (reg32 arg0)
    sfun "print_match" [already arg0, setAddr "m", setAddr "s"]
    goto ".arg_loop"
  label ".end"
  setInt 0 res0
  epilogue
