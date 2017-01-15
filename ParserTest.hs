{-# LANGUAGE OverloadedStrings #-}

import System.Exit

import Text.Trifecta

import Parser
import AST

doTest (input, result) = case parseOnly pFile input of
   Success p | p == result -> return True -- putStrLn ("pass: " ++ show input ++ " parsed to " ++ show p) >> return True
             | otherwise   -> putStrLn ("fail: " ++ show input ++ " did not parse to " ++ show result ++ " but " ++ show p) >> return False
   Failure e -> putStrLn ("fail: " ++ show input ++ " failed to parse:\n" ++ show e) >> return False

doTests = mapM doTest

subst pat rep = Subst (re pat) rep SubstFirst SActionNone
subst2 pat rep t act = Subst (re pat) rep t act
emptySub = Subst Nothing "" SubstFirst SActionNone

tests =
  [ ("s/a/b/g", [Sed Always (subst2 "a" "b" SubstAll SActionNone)])
  , ("s/a/b/p", [Sed Always (subst2 "a" "b" SubstFirst (SActionPrint 0))])
  , ("s/a/b/e", [Sed Always (subst2 "a" "b" SubstFirst SActionExec)])
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

  , ("q", [Sed Always (Quit True ExitSuccess)])
  , ("q 0", [Sed Always (Quit True ExitSuccess)])
  , ("q 1", [Sed Always (Quit True (ExitFailure 1))])
  , ("Q", [Sed Always (Quit False ExitSuccess)])
  ]

counts [] = (0,0)
counts (x:xs) | x = (trues + 1, falses)
              | otherwise = (trues, falses + 1)
              where (trues, falses) = counts xs

main = do
    results <- doTests tests
    let (passes, fails) = counts results
    case fails of
      0 -> putStrLn "OK" >> exitSuccess
      -- putStrLn ("Finished " ++ show (length tests) ++ " tests")
      _ -> putStrLn (show fails ++ " tests failed") >> exitFailure
