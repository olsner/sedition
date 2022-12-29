{-# LANGUAGE RecordWildCards #-}

-- Based on https://arxiv.org/pdf/2206.01398.pdf, "A Closer Look at TDFA"
-- Determinization, convert a TNFA to a TDFA state machine.

module TDFA where

import Control.Monad.Trans.State.Strict

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import TaggedRegex
import TNFA (genTNFA, TNFA)
import qualified TNFA

type StateId = Int
type RegId = Int
data RegVal = Nil | Pos deriving (Show, Ord, Eq)
data RegOp
  = SetReg RegId RegVal -- ^ Set register to nil or current position
  | CopyReg RegId RegId -- ^ CopyReg i j => i <- j
  -- Assuming for now that this is re2c-specific, we only use single-value tags.
  -- | CopyAppend RegId [RegVal] -- ^ i <- j <> h
  deriving (Show, Ord, Eq)

type RegOps = [RegOp]
type TDFATrans = (TNFATrans, StateId, RegOps)

data TDFA = TDFA {
    tdfaStartState :: StateId,
    tdfaFinalStates :: Set StateId,
    tdfaFinalRegisters :: Map TagId RegId,
    tdfaFinalFunction :: Map StateId RegOps,
    tdfaTrans :: Map StateId [TDFATrans],
    tdfaTagMap :: FixedTagMap
  }
  deriving (Show, Ord, Eq)

type Prec = [Prio]
-- Output or intermediate data of epsilon closure calculation
type Closure = [(Prio, Map TagId RegId, [Tag], [Tag])]
type StateClosure = [(Prio, Map TagId RegId, [Tag])]

data DetState = DetState {
  maxTag :: Int,
  stateMap :: Map (StateClosure, Prec) StateId,
  -- stateList :: [([(Prio,Map TagId RegId,[Tag])],Prec,StateId)],
  nextState :: StateId
    }
  deriving (Show, Ord, Eq)

initState tnfa = DetState { maxTag = TNFA.maxTag tnfa, stateMap = M.empty,
                            nextState = 1 }

type GenTDFA a = State DetState a

history []            _           = []
history (Tag t':ts)   t | t == t' = Pos : history ts t
history (UnTag t':ts) t | t == t' = Nil : history ts t
history (_:ts)        t           = history ts t

precedence :: Closure -> Prec
precedence = map (\(q,_,_,_) -> q)

stateClosure = map (\(q,s,_,l) -> (q,s,l))

-- Note: more complicated with support for multi-valued tags
regop_rhs :: Map TagId RegId -> [Tag] -> TagId -> [Tag]
-- regop_rhs r ht t | isMultiValuedTag t = M.lookup t r : ht
regop_rhs r ht t = [last ht]

findState :: Closure -> GenTDFA (Maybe StateId)
findState closure = gets (M.lookup (stateClosure closure, precedence closure) . stateMap)

-- mapState :: StateClosure -> StateClosure -> Maybe RegOps
-- mapState s s' = 

addState :: Closure -> RegOps -> GenTDFA (StateId, RegOps)
addState closure ops = return (error "state id here", ops)
  where
    prec = precedence closure

determinize tnfa = do
    return (TDFA {})

genTDFA :: TNFA -> TDFA
genTDFA tnfa = evalState (determinize tnfa) (initState tnfa)

prettyStates :: TDFA -> String
prettyStates TDFA{..} = go S.empty [tdfaStartState] <> fixedTags <> "\n"
  where
    go seen (s:ss)
        | not (S.member s seen) =
            showState s <> showTrans s <>
            go (S.insert s seen) (ss ++ nextStates s)
        | otherwise = go seen ss
    go seen [] = []
    nextStates s =  [t | (_,t,_) <- getTrans s]
    showState s | s == tdfaStartState = "START " ++ show s ++ ":\n"
    showState s | isFinalState s = "FINAL " ++ show s ++ ":\n"
    showState s = "State " ++ show s ++ ":\n"
    showTrans s = concat [ "  " ++ show t ++ " => " ++ show s' ++
                            " | " ++ regOps o ++ "\n"
                           | (t,s',o) <- getTrans s ]
    fixedTags | M.null tdfaTagMap = "(No fixed tags)"
              | otherwise = "Fixed tags:\n" ++
        concat [ "  t" ++ show t ++ " <- t" ++ show b ++ " - " ++ show d ++ "\n"
                 | (t,(FixedTag b d)) <- M.toList tdfaTagMap ]

    regOps ops = intercalate "; " (map show ops)

    getTrans :: StateId -> [TDFATrans]
    getTrans s = fromMaybe [] (M.lookup s tdfaTrans)

    isFinalState s = s `S.member` tdfaFinalStates

testTDFA :: String -> IO ()
testTDFA = putStr . prettyStates . genTDFA . genTNFA . testTagRegex
