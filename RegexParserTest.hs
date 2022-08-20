{-# LANGUAGE OverloadedStrings #-}

module RegexParserTest (main) where

import Data.Set (Set)
import qualified Data.Set as S

import System.Exit

import Text.Trifecta hiding (parseString)

import Regex

data Dialect = BRE | ERE | Both deriving (Show,Ord,Eq)

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

-- Abbreviations for reference results
literal xs = Concat (map Char xs)
star = Repeat 0 Nothing
plus = Repeat 1 Nothing
rep min max = Repeat min (Just max)

doTests = mapM doTest

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

  -- No bracket expression parsing yet
  -- , (Both, "[/]", CClass (S.singleton '/'))
  -- , (Both, "[|]", CClass (S.singleton '|'))
  -- , (Both, "[^/]", CNotClass (S.singleton '/'))
  -- TODO read up on escaping brackets or something
  -- , (Both, "\\[", Char '[')
  -- Escaped bracket in bracket should not end it?
  --, ("s/[\\]/]foo/bar/", [Sed Always (subst "[\\]/]foo" "bar")])
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
  ]

counts :: [Bool] -> (Int,Int)
counts [] = (0,0)
counts (x:xs) | x = (trues + 1, falses)
              | otherwise = (trues, falses + 1)
              where (trues, falses) = counts xs

main = do
    results <- doTests tests
    let (_passes, fails) = counts results
    case fails of
      0 -> putStrLn "OK" >> exitSuccess
      -- putStrLn ("Finished " ++ show (length tests) ++ " tests")
      _ -> putStrLn (show fails ++ " tests failed") >> exitFailure
