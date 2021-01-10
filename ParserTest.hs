{-# LANGUAGE OverloadedStrings #-}

module ParserTest (main) where

import System.Exit

import Text.Trifecta

import Parser
import AST

doTest (input, result) = case parseOnly pFile input of
   Success p | p == result -> return True -- putStrLn ("pass: " ++ show input ++ " parsed to " ++ show p) >> return True
             | otherwise   -> putStrLn ("fail: " ++ show input ++ " did not parse to " ++ show result ++ " but " ++ show p) >> return False
   Failure e -> putStrLn ("fail: " ++ show input ++ " failed to parse:\n" ++ show e) >> return False

doTests = mapM doTest

subst' pat rep = Subst (re pat) rep SubstFirst SActionNone
subst pat "" = subst' pat []
subst pat rep = subst' pat [Literal rep]
subst2 pat rep t act = Subst (re pat) [Literal rep] t act
emptySub = Subst Nothing [] SubstFirst SActionNone

tests =
  [ ("a text", [Sed Always (Append "text")])
  , ("a\\\nfoo\\\nbar", [Sed Always (Append "foo\nbar")])
  , ("a\\\nfoo\\r\\nbar\\\nbaz", [Sed Always (Append "foo\r\nbar\nbaz")])
  , ("a text\\\nbar", [Sed Always (Append "text\nbar")])
  , ("A 1 2", [Sed Always (Accept 1 2)])
  , ("A1 2", [Sed Always (Accept 1 2)])

  , ("c\\\nfoo\\\nbar", [Sed Always (Change "foo\nbar")])
  , ("c\\\nfoo\\r\\nbar\\\nbaz", [Sed Always (Change "foo\r\nbar\nbaz")])

  , ("D;d", [Sed Always DeleteFirstLine, Sed Always Delete])

  , ("i text", [Sed Always (Insert "text")])

  , ("l", [Sed Always (PrintLiteral 70)])
  , ("l 123", [Sed Always (PrintLiteral 123)])

  , ("m foo", [Sed Always (Message (Just "foo"))])
  , ("m", [Sed Always (Message Nothing)])
  , ("m  ", [Sed Always (Message Nothing)])

  , ("n 4", [Sed Always (Next 4)])
  , ("N 4", [Sed Always (NextA 4)])

  , ("P 7", [Sed Always (PrintFirstLine 7)])
  , ("P;p", [Sed Always (PrintFirstLine 0), Sed Always (Print 0)])

  , ("q", [Sed Always (Quit True ExitSuccess)])
  , ("q 0", [Sed Always (Quit True ExitSuccess)])
  , ("q 1", [Sed Always (Quit True (ExitFailure 1))])
  , ("Q", [Sed Always (Quit False ExitSuccess)])

  , ("r /dev/stdin", [Sed Always (ReadFile "/dev/stdin")])

  -- subst flags
  , ("s/a/b/g", [Sed Always (subst2 "a" "b" SubstAll SActionNone)])
  , ("s/a/b/p", [Sed Always (subst2 "a" "b" SubstFirst (SActionPrint 0))])
  , ("s/a/b/e", [Sed Always (subst2 "a" "b" SubstFirst SActionExec)])
  , ("s/a/b/1234", [Sed Always (subst2 "a" "b" (SubstNth 1234) SActionNone)])
  , ("s/a/b/w output", [Sed Always (subst2 "a" "b" SubstFirst (SActionWriteFile "output"))])
  -- combinations of SubstNth
  , ("s/a/b/gp", [Sed Always (subst2 "a" "b" SubstAll (SActionPrint 0))])
  , ("s/a/b/1p", [Sed Always (subst2 "a" "b" (SubstNth 1) (SActionPrint 0))])
  , ("s/a/b/p1", [Sed Always (subst2 "a" "b" (SubstNth 1) (SActionPrint 0))])
  -- leaning toothpicks
  , ("s/\\//\\//", [Sed Always (subst "/" "/")])
  , ("s|\\||\\||", [Sed Always (subst "|" "|")])
  , ("s///", [Sed Always emptySub])
  , ("s/\\.//", [Sed Always (subst "\\." "")])
  , ("/\\./ s///", [Sed (At (Match (re "\\."))) emptySub])

  , ("// s///", [Sed (At (Match Nothing)) emptySub])
  , ("\\// s///", [Sed (At (Match Nothing)) emptySub])
  , ("\\|| s|||", [Sed (At (Match Nothing)) emptySub])
  , ("\\/\\//s///", [Sed (At (Match (re "/"))) emptySub])
  , ("\\|\\|| s|||", [Sed (At (Match (re "|"))) emptySub])

  -- Slash (or other separator) should be "escaped" when in brackets. Appears
  -- in GNU's dc.sed (at least).
  , ("s/[/]//", [Sed Always (subst "[/]" "")])
  -- The special handling should probably not be applied in the replacement part.
  , ("s|foo|[|", [Sed Always (subst "foo" "[")])
  -- When the bracket is escaped it should not be treated specially
  , ("s/\\[/]/", [Sed Always (subst "\\[" "]")])
  , ("s|[|]||", [Sed Always (subst "[|]" "")])
  -- Escaped bracket in bracket should not end it.
  --, ("s/[\\]/]foo/bar/", [Sed Always (subst "[\\]/]foo" "bar")])
  , ("s|foo|\\\n|", [Sed Always (subst "foo" "\n")])
  , ("s|foo|\\n|", [Sed Always (subst "foo" "\n")])
  , ("s/./(&)/", [Sed Always (subst' "." [Literal "(", WholeMatch, Literal ")"])])

  , ("t foo;Tfoo;t;T",
        [ Sed Always (Test (Just "foo"))
        , Sed Always (TestNot (Just "foo"))
        , Sed Always (Test Nothing)
        , Sed Always (TestNot Nothing)])

  , ("w /dev/stdin", [Sed Always (WriteFile "/dev/stdin")])

  , ("x", [Sed Always (Exchange Nothing)])
  , ("x reg", [Sed Always (Exchange (Just "reg"))])

  , ("y/abc/def/", [Sed Always (Trans "abc" "def")])

  , ("z", [Sed Always Clear])

  , ("/^$/! p", [Sed (NotAddr (At (Match (re "^$")))) (Print 0)])
  , ("8,13 !p", [Sed (NotAddr (Between (Line 8) (Line 13))) (Print 0)])
  , ("2,/^$/ {}", [Sed (Between (Line 2) (Match (re "^$"))) (Block [])])
  , ("{}", [Sed Always (Block [])])

  , ("=", [Sed Always (PrintLineNumber 0)])
  , ("=73", [Sed Always (PrintLineNumber 73)])
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
