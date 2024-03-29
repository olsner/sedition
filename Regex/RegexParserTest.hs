{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString.Char8 as C
import Data.List (nub, sort)
import Data.String

import System.Exit

import Text.Trifecta (Result(..))

import Regex.Regex

data Dialect = BRE | ERE | Both deriving (Show,Ord,Eq)

-- Abbreviations for reference results
literal xs = Literal xs
star = Repeat 0 Nothing
plus = Repeat 1 Nothing
rep min max = Repeat min (Just max)

spaceToZ = enumFromTo ' ' 'Z'
tabAndSpaceToZ = '\t' : spaceToZ
spaces = sort " \r\n\t\v\f"

tests =
  -- Simple
  [ (Both, "a", Char 'a')
  , (Both, "foo", literal "foo")
  , (Both, "/", Char '/')
  , (Both, "", Empty)
  -- Literal recognition
  , (Both, "foo.bar", Concat [literal "foo", Any, literal "bar"])

  -- BRE doesn't have alternation, but we add it anyway.
  , (BRE, "a\\|b", Or [Char 'a', Char 'b'])
  , (ERE, "a|b", Or [Char 'a', Char 'b'])
  -- Not quite handling empty alternatives yet.
  --, (ERE, "|b", Or [Empty, Char 'b'])
  --, (ERE, "a|", Or [Char 'a', Empty])
  -- Escaped/unesacped should be a literal pipe character
  , (BRE, "|", Char '|')
  , (ERE, "\\|", Char '|')
  -- Escapes and stuff
  , (ERE, "\\?", Char '?')
  , (ERE, "\x1b", Char '\x1b')
  , (ERE, "\\[", Char '[')

  -- Bracket expressions
  , (Both, "[/]", CClass "/")
  , (Both, "[|]", CClass "|")
  , (Both, "[^/]", CNotClass "/")
  -- ^ is only special when first
  , (Both, "[a^]", CClass "^a")
  , (Both, "[^^]", CNotClass "^")
  -- Escaped bracket in bracket should end it, backslash is not special
  , (Both, "[\\]/]f", Concat [CClass "\\", literal "/]f"])
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
  -- ERE treats these as special anywhere, BRE only at start/end
  , (ERE, "a^", Concat [Char 'a', AnchorStart])
  , (ERE, "$a", Concat [AnchorEnd, Char 'a'])

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
  , (BRE, "|?#[\t -Z]*", Concat [literal "|?#", star (CClass tabAndSpaceToZ)])
  , (BRE, "[ -Z]", (CClass spaceToZ))
  , (BRE, "[\t -Z]", (CClass tabAndSpaceToZ))
  , (BRE, "[\t }]", (CClass "\t }"))
  , (BRE, "[}]", (CClass "}"))
  , (BRE, "[ ]", (CClass " "))
  , (BRE, "[\t]", (CClass "\t"))

  -- A dash first is also a literal '-' rather than a range...
  , (BRE, "|?!*[-+*/%^<>=]", Concat [literal "|?", star (Char '!'),
            CClass "%*+-/<=>^"])

  -- Not actually in BRE or ERE
  , (Both, "\\s", CClass spaces)
  , (Both, "\\S", CNotClass spaces)

  -- Some BRE oddities and special cases
  -- * first is a character, not special
  , (BRE, "*s", literal "*s")
  , (BRE, "*\\|s", Or [Char '*', Char 's'])
  , (BRE, "*\\|^", Or [Char '*', Char '^'])
  , (BRE, "^*", Concat [AnchorStart, Char '*'])
  -- , (BRE, "**", star (Char '*'))

  -- BRE doesn't have to treat ^ and $ as anchors unless they are at the
  -- start/end of the regular expression.
  -- ERE gives ^ and $ their special meanings wherever they appear (even if
  -- that means they will never match).
  , (BRE, "a^", literal "a^")
  , (BRE, "a^*", Concat [Char 'a', star (Char '^')])
  , (BRE, "$a", literal "$a")
  , (BRE, "$\\|a", Or [Char '$', Char 'a'])
  , (BRE, "$\\{1,3\\}", Repeat 1 (Just 3) (Char '$'))
  , (BRE, "$*", star (Char '$'))

  , (BRE, "^\\]", Concat [AnchorStart, Char ']'])
  , (BRE, "^\\", Concat [AnchorStart, Char '\\'])

  -- Evil regexp from Twitter
  , (ERE, "()((()(^|$|$^|^|$|$^^|$|$^|^|$|$^^^^|^|(|)($)|)+|^^|^|(|)($)|)+|)($)()+", Concat [
    Group Empty,
    Group (Or [
        Repeat 1 Nothing (Group (Or [Concat [Group Empty,Repeat 1 Nothing (Group (Or [AnchorStart,AnchorEnd,Concat [AnchorEnd,AnchorStart],AnchorStart,AnchorEnd,Concat [AnchorEnd,AnchorStart,AnchorStart],AnchorEnd,Concat [AnchorEnd,AnchorStart],AnchorStart,AnchorEnd,Concat [AnchorEnd,AnchorStart,AnchorStart,AnchorStart,AnchorStart],AnchorStart,Concat [Group (Or [Empty,Empty]),Group AnchorEnd],Empty]))],Concat [AnchorStart,AnchorStart],AnchorStart,Concat [Group (Or [Empty,Empty]),Group AnchorEnd],Empty])),
        Empty]),
    Group AnchorEnd,
    Repeat 1 Nothing (Group Empty)])
  -- from life-in-sed
  , (ERE, "\x1b\\[\\?25l\x1b\\[H", literal "\x1b[?25l\x1b[H")
  ]

-- Test code

doTest (Both, input, result) = do
    a <- doTest (BRE, input, result)
    b <- doTest (ERE, input, result)
    return (a && b)
doTest (dialect, input, result) =
  case parseOnly (dialect == ERE) input of
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
  case parseOnly True (C.pack $ reString input) of
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
