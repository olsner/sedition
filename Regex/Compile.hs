module Regex.Compile where

import qualified Data.ByteString.Char8 as C
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS

import Debug.Trace

import GenC
import GenAsm
import Regex.CompileAsm (genAsm)
import Regex.CompileIR (genC)
import Regex.IR (Program)
import Regex.Minimize (minimize)
import Regex.OptimizeIR (optimize)
import Regex.Regex
import Regex.TaggedRegex
import Regex.TDFA (genTDFA)
import Regex.TDFA2IR (genIR)
import Regex.TNFA (genTNFA)

re2asm :: Maybe IntSet -> Regex -> C.ByteString
re2asm used = GenAsm.toByteString .
    genAsm .
    -- TODO Allow controlling optimization fuel here, preferrably integrated in
    -- a way that lets you bisect both regex and Sed IR optimizations.
    fst . optimize 1000000 .
    re2ir .
    unusedTags .
    tagRegex
  where unusedTags | Just s <- used = selectTags (\(T t) -> t `IS.member` s)
                   | otherwise = id

re2c :: Maybe IntSet -> Regex -> C.ByteString
re2c used = GenC.toByteString .
    genC .
    -- TODO Allow controlling optimization fuel here, preferrably integrated in
    -- a way that lets you bisect both regex and Sed IR optimizations.
    fst . optimize 1000000 .
    re2ir .
    unusedTags .
    tagRegex
  where unusedTags | Just s <- used = selectTags (\(T t) -> t `IS.member` s)
                   | otherwise = id

re2ir :: TaggedRegex -> Program
re2ir re | hasTags re = genIR . minimize . genTDFA . genTNFA . fixTags $ re
         | otherwise = genIR . minimize . genTDFA . genTNFA . fixTags $ trace ("Could use pure NFA for " ++ show re) re -- TODO pure-NFA

isCompatible :: Regex -> Bool
isCompatible = tdfa2cCompatible

testTDFA2C :: String -> IO ()
testTDFA2C = C.putStrLn . re2c Nothing . parseString True . C.pack

