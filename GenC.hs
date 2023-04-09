{-# LANGUAGE OverloadedStrings,GADTs,TypeFamilies,RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module GenC where

import qualified Compiler.Hoopl as H
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy.Char8 as L
import qualified Data.ByteString.Builder as B
import Data.ByteString.Builder as B hiding (Builder, string8, intDec, byteString)
import Data.Semigroup
import Data.Word

-- newtype Builder = Builder { unC :: B.Builder }
--   deriving (Monoid, Semigroup)
type Builder = B.Builder

string8 = B.string8
intDec = B.intDec
-- word8HexFixed = Builder . B.word8HexFixed
byteString = B.byteString

-- TODO More fun: add a new C builder type that is sensitive to blocks and
-- stuff and does indentation.

toByteString = L.toStrict . B.toLazyByteString

label name = string8 name <> ":\n"
goto name = stmt ("goto " <> string8 name)
gotoL :: H.Label -> Builder
gotoL l = goto (show l)

idIntDec i | i >= 0    = intDec i
           | otherwise = "_" <> intDec (negate i)

cchar :: Char -> Builder
cchar = showB . fromEnum
cstring s = "\"" <> foldMap quoteC (C.unpack s) <> "\""
  where
    quoteC '\n' = "\\n"
    quoteC '\t' = "\\t"
    quoteC '\"' = "\\\""
    quoteC '\\' = "\\\\"
    quoteC c
      -- Add an extra "" pair to terminate the hex escape in case it is
      -- followed by a valid hex digit.
      | length (show c) /= 3 = "\\x" <> word8HexFixed (toWord8 c) <> "\"\""
    quoteC c = char8 c
    toWord8 :: Char -> Word8
    toWord8 = fromIntegral . fromEnum

bool True = "true"
bool False = "false"

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

hsep = stimes (79 :: Int) "/" <> "\n"

cIf :: Builder -> Builder -> Builder -> Builder
cIf cond t f = fun "if " [cond] <> " {\n  " <> t <> "} else {\n  " <> f <> "}\n"
cWhen cond t = fun "if " [cond] <> " {\n  " <> t <> "}\n"
cWhile cond t = fun "while" [cond] <> "{\n  " <> t <> "}\n"

