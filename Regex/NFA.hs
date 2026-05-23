{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances #-}

module Regex.NFA where

import Control.Monad
import Control.Monad.Trans.Writer

-- import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import qualified Regex.TaggedRegex as TR
import Regex.TNFA (StateId(..))

import Regex.NFA.Bitwise
import Regex.NFA.Type
import Regex.NFA.Glushkov hiding (glushkovCompatible)
import qualified Regex.NFA.Glushkov as G

-- API?

simulateNFA :: NFA -> String -> (Bool, [String])
simulateNFA NFA{..} xs = runWriter (go (S.singleton nfaStartState) xs)
  where
    intersects x y = not (S.null (x `S.intersection` y))
    hasFinalState s = s `intersects` nfaFinalStates
    go s []     | hasFinalState s = logFinal s "End -> MATCH: final" >> return True
                | otherwise       = logFinal s "End -> NO MATCH" >> return False
    go s (x:xs) | hasFinalState s = logFinal s "MATCH: final state" >> return True
                | S.null s        = tell ["NO MATCH"] >> return False
                -- Special case only for prettier printouts.
                | S.null s'       = logTrans s x s' >> return False
                | otherwise       = logTrans s x s' >> go s' xs
                where s' = closeAll x s
    closeAll x ss = S.unions (map (close x) (S.toList ss))
    close :: Char -> StateId -> Set StateId
    close x s = findTrans x (M.findWithDefault M.empty s nfaTrans)
    findTrans x m = S.unions [exact, any]
      where
        exact = M.findWithDefault S.empty (C x) m
        any = M.findWithDefault S.empty Any m
    logTrans s x s' | S.null s' = tell [showStates s ++ " -> " ++ show x ++ " -> NO MATCH"]
                    | otherwise = tell [showStates s ++ " -> " ++ show x ++ " -> " ++ showStates s']
    logFinal s msg  = tell [showStates s ++ " -> " ++ msg]
    showStates = unwords . map show . S.toList

-- Test functions

glushkovCompatible = G.glushkovCompatible

removeTags = TR.selectTags (const False)

testCompatible :: String -> IO ()
testCompatible s = do
  putStrLn ("Regular expression: " ++ s)
  let parsed = TR.testParseTagRegex s
  when (TR.hasTags parsed) $ putStrLn "Contains tags (will be stripped for NFA)"
  let re = removeTags parsed
  print re
  when (TR.hasAnchors re) $ putStrLn "Contains anchors - cannot use Glushkov construction"
  when (glushkovCompatible re) $ putStrLn "Can use Glushkov construction"

testLinearize :: String -> LinearRegex
testLinearize = linearize . removeTags . TR.testParseTagRegex

nfaFromRegex = compact . genNFA . removeTags . TR.testParseTagRegex

testCompact :: Bool -> String -> IO ()
testCompact showPre re = do
  let nfa = genNFA . removeTags . TR.testParseTagRegex $ re
  when showPre $ putStr (prettyStates nfa)
  let nfa' = compact nfa
  -- TODO Clean up trace stuff in compact so we don't need an ugly `seq`
  length (prettyStates nfa') `seq` putStrLn ("compacted from " ++ show (nfaNumStates nfa) ++ " to " ++ show (nfaNumStates nfa') ++ " states, " ++ show (nfaNumTrans nfa) ++ " to " ++ show (nfaNumTrans nfa') ++ " transitions")
  putStr (prettyStates nfa')

testNFA :: String -> IO ()
testNFA = putStr . prettyStates . nfaFromRegex

testBitwise :: String -> Maybe (BitNFA Word)
testBitwise = bitwiseNFA . nfaFromRegex

testSimulate :: String -> String -> IO ()
testSimulate re s = putStr (prettyStates nfa) >> mapM_ putStrLn log >> print result
  where (result, log) = simulateNFA nfa s
        nfa = genNFA (removeTags (TR.testParseTagRegex re))

exampleRE = "(a(ab)*)*|(ba)*"
evilRE = "(b|)(^|g)($|q)(z|)(^|f)"
