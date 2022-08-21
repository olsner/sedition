{-# LANGUAGE OverloadedStrings #-}

module RegexParserTest (main) where

import qualified Data.ByteString.Char8 as C
import Data.List (nub)

import System.Exit

import Text.Trifecta hiding (parseString)

import Regex

data Dialect = BRE | ERE | Both deriving (Show,Ord,Eq)

-- Abbreviations for reference results
literal xs = Concat (map Char xs)
star = Repeat 0 Nothing
plus = Repeat 1 Nothing
rep min max = Repeat min (Just max)

spaceToZ = enumFromTo ' ' 'Z'
tabAndSpaceToZ = '\t' : spaceToZ

tests =
  -- Simple
  [ (Both, "a", Char 'a')
  , (Both, "foo", literal "foo")
  , (Both, "/", Char '/')

  -- BRE doesn't have alternation, but we add it anyway.
  , (BRE, "a\\|b", Or [Char 'a', Char 'b'])
  , (ERE, "a|b", Or [Char 'a', Char 'b'])
  -- Escaped/unesacped should be a literal pipe character
  , (BRE, "|", Char '|')
  , (ERE, "\\|", Char '|')

  -- Bracket expressions
  , (Both, "[/]", CClass "/")
  , (Both, "[|]", CClass "|")
  , (Both, "[^/]", CNotClass "/")
  -- ^ is only special when first
  , (Both, "[a^]", CClass "^a")
  , (Both, "[^^]", CNotClass "^")
  -- Escaped bracket in bracket should end it, backslash is not special
  , (Both, "[\\]/]f", Concat (CClass "\\" : map Char "/]f"))
  , (Both, "[\\]", CClass "\\")
  -- Escaped brackets otherwise should be escaped?
  , (Both, "\\[", Char '[')
  , (Both, "\\[]", literal "[]")
  -- Ranges, and non-ranges with - at the end
  , (Both, "[a-cx-z]", CClass "abcxyz")
  , (Both, "[+--]", CClass "+,-")
  , (Both, "[a-]", CClass "-a")
  , (Both, "[^a-]", CNotClass "-a")
  -- ']' first should be itself (otherwise it should terminate the bracket)
  -- (not implemented)
  , (Both, "[]]", CClass "]")
  , (Both, "[^]]", CNotClass "]")
  -- Initial - is also a special case
  , (Both, "[-a]", CClass "-a")
  , (Both, "[^-a]", CNotClass "-a")
  -- Both an initial ] and a trailing -
  , (Both, "[^]-]", CNotClass "-]")
  , (Both, "[]-]", CClass "-]")
  -- And a singleton - which isn't a range but either a trailing or leading -
  , (Both, "[^-]", CNotClass "-")
  , (Both, "[-]", CClass "-")

  -- back refs
  , (BRE, "\\(a\\)\\1", Concat [Group (Char 'a'), BackRef 1])
  , (ERE, "(a)\\1", Concat [Group (Char 'a'), BackRef 1])

  --
  , (Both, ".", Any)

  -- anchoring
  , (Both, "^$", Concat [AnchorStart, AnchorEnd])
  , (Both, "a^", Concat [Char 'a', AnchorStart])
  , (Both, "$a", Concat [AnchorEnd, Char 'a'])

  -- counts
  , (BRE, "a*", star (Char 'a'))
  , (BRE, "a\\+", plus (Char 'a'))
  , (BRE, "a\\?", rep 0 1 (Char 'a'))
  , (BRE, "\\(a\\)*", star (Group (Char 'a')))
  , (BRE, "\\(a\\)\\{1,7\\}", rep 1 7 (Group (Char 'a')))
  , (BRE, "a\\{1,7\\}", rep 1 7 (Char 'a'))
  , (BRE, "a\\{1,\\}", plus (Char 'a'))
  , (BRE, "a\\{1\\}", Char 'a')

  , (ERE, "(a)*", star (Group (Char 'a')))
  , (ERE, "(a)+", plus (Group (Char 'a')))
  , (ERE, "(a)?", rep 0 1 (Group (Char 'a')))
  , (ERE, "(a){1,7}", rep 1 7 (Group (Char 'a')))
  , (ERE, "a{1,7}", rep 1 7 (Char 'a'))
  , (ERE, "a{1,}", plus (Char 'a'))
  , (ERE, "a{1}", Char 'a')

  -- Something from dc.sed (it uses '}' instead of 'Z' as the end of range, but
  -- we don't yet have complete parsing of brackets that contain ']', which is
  -- in that range...)
  , (BRE, "|?#[\t -Z]*", Concat (map Char "|?#" ++ [star (CClass tabAndSpaceToZ)]))
  , (BRE, "[ -Z]", (CClass spaceToZ))
  , (BRE, "[\t -Z]", (CClass tabAndSpaceToZ))
  , (BRE, "[\t }]", (CClass "\t }"))
  , (BRE, "[}]", (CClass "}"))
  , (BRE, "[ ]", (CClass " "))
  , (BRE, "[\t]", (CClass "\t"))

  -- A dash first is also a literal '-' rather than a range...
  , (BRE, "|?!*[-+*/%^<>=]", Concat [Char '|', Char '?', star (Char '!'),
            CClass "%*+-/<=>^"])
  ]

-- Test code

doTest (Both, input, result) = do
    a <- doTest (BRE, input, result)
    b <- doTest (ERE, input, result)
    return (a && b)
doTest (dialect, input, result) =
  case parseOnly (pRegex (dialect == ERE)) input of
   Success p | p == result -> return True -- putStrLn ("pass: " ++ input_str ++ " parsed to " ++ show p) >> return True
             | otherwise   -> putStrLn ("fail: " ++ input_str ++ " did not parse to " ++ show result ++ " but " ++ show p) >> return False
   Failure e -> putStrLn ("fail: " ++ input_str ++ " failed to parse:\n" ++ show e) >> return False
  where
    input_str = show dialect ++ " " ++ show input
doTests = mapM doTest

-- Check that re-parsing the reString output produces the original regexp.
-- We don't validate the reString output itself as the string representation
-- can be a bit different from the input (e.g. variations of {n,m} that are
-- equivalent to *, + or ?).
doTestString input = do
  case parseOnly (pRegex True) (C.pack $ reString input) of
   Success p | p == input -> return True -- putStrLn ("pass: " ++ show input ++ " round-tripped to " ++ show p) >> return True
             | otherwise   -> putStrLn ("fail: " ++ show input ++ " did not roundtrip to itself but " ++ show p) >> return False
   Failure e -> putStrLn ("fail: " ++ show input ++ " failed to roundtrip parse:\n" ++ show e) >> return False

doTestStrings tests = mapM doTestString results
  where
    results = nub $ map (\(_,_,result) -> result) tests

counts :: [Bool] -> (Int,Int)
counts [] = (0,0)
counts (x:xs) | x = (trues + 1, falses)
              | otherwise = (trues, falses + 1)
              where (trues, falses) = counts xs

main = do
    res1 <- doTests tests
    res2 <- doTestStrings tests
    let results = res1 ++ res2
    let (_passes, fails) = counts results
    case fails of
      0 -> putStrLn "OK" >> exitSuccess
      _ -> putStrLn (show fails ++ " tests failed") >> exitFailure
