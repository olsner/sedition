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

tests =
  [ ("s/a/b/g", [Sed Always (Subst (Just (RE "a")) "b" [SubstGlobal])])
  , ("s/\\//\\//", [Sed Always (Subst (Just (RE "/")) "/" [])])
  , ("s|\\||\\||", [Sed Always (Subst (Just (RE "|")) "|" [])])
  , ("s///", [Sed Always (Subst Nothing "" [])])
  , ("s/\\.//", [Sed Always (Subst (Just (RE "\\.")) "" [])])
  , ("/\\./ s///", [Sed (At (Match (Just (RE "\\.")))) (Subst Nothing "" [])])

  , ("// s///", [Sed (At (Match Nothing)) (Subst Nothing "" [])])
  , ("\\// s///", [Sed (At (Match Nothing)) (Subst Nothing "" [])])
  , ("\\|| s|||", [Sed (At (Match Nothing)) (Subst Nothing "" [])])
  , ("\\/\\//s///", [Sed (At (Match (Just (RE "/")))) (Subst Nothing "" [])])
  , ("\\|\\|| s|||", [Sed (At (Match (Just (RE "|")))) (Subst Nothing "" [])])

  , ("q", [Sed Always (Quit ExitSuccess)])
  , ("q 0", [Sed Always (Quit ExitSuccess)])
  , ("q 1", [Sed Always (Quit (ExitFailure 1))])
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
