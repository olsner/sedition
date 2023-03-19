{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances,FlexibleInstances,FlexibleContexts #-}

module Regex.TDFA2IR where

import Compiler.Hoopl as H hiding (addBlock)

import Control.Monad
import Control.Monad.Trans.State.Strict

import qualified Data.ByteString.Char8 as C

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS

import Debug.Trace

import qualified CharMap as CM
import CharMap (CharMap)

import Regex.Regex (Regex)
import Regex.TaggedRegex as TR
import Regex.TNFA (genTNFA)
import Regex.TDFA as TDFA hiding (initState)
import Regex.IR as IR

data LabelType = Checked | Unchecked deriving (Show, Ord, Eq)
type StateLabel = (StateId, LabelType)

data IRState = IRState {
    firstFreeUnique :: Int,
    graph :: Graph Insn C C,
    labelMap :: Map StateLabel Label,
    matchLabel :: Label
  } deriving (Show)

initState = IRState 0 emptyClosedGraph M.empty undefined

type IRM = State IRState

instance UniqueMonad IRM where
  freshUnique = do
    res <- gets firstFreeUnique
    modify $ \state -> state { firstFreeUnique = res + 1 }
    return res

instance Semigroup (Graph Insn O O) where
  (<>) = (H.<*>)

instance Monoid (Graph Insn O O) where
  mempty = emptyGraph

addLabel st l s@IRState{..} = s { labelMap = M.insert st l labelMap }
getLabel s = do
  existing <- gets (M.lookup s . labelMap)
  case existing of
    Just l -> return l
    Nothing -> do
      l <- freshLabel
      modify (addLabel s l)
      return l
setMatchLabel l = modify $ \s@IRState{..} -> s { matchLabel = l }

addBlock :: Graph Insn C C -> IRM ()
addBlock block = modify $ \s@IRState{..} -> s { graph = graph |*><*| block }

goto :: Label -> Graph Insn O C
goto l = mkLast (Branch l)
gofail :: Graph Insn O C
gofail = mkLast Fallback

checkBounds d eof cont = mkLast (CheckBounds d eof cont)
checkEOF = checkBounds 1

gostate :: StateLabel -> IRM (Graph Insn O C)
gostate s = getLabel s >>= return . goto
gostate_nocheck :: StateId -> IRM (Graph Insn O C)
gostate_nocheck s = (yystats "goto_nocheck" 1 H.<*>) <$> gostate (s, Unchecked)
gostate_check s = gostate (s, Checked)

yystats :: String -> Int -> Graph Insn O O
yystats name inc = emptyGraph

emitRegOp :: RegOp -> Graph Insn O O
emitRegOp (r,val) = mkMiddle (g val) H.<*> yystats "regops" 1
  where
    g (SetReg Pos) = Set r
    g (SetReg Nil) = Clear r
    g (CopyReg r2) = Copy r r2

emitCase :: Set StateId -> TDFATrans -> IRM (Graph Insn O C)
emitCase nocheckStates (s', regops) =
    (foldMap emitRegOp regops H.<*> mkMiddle Next H.<*>) <$>
    (if skipCheck then gostate_nocheck s' else gostate_check s')
    where skipCheck = S.member s' nocheckStates

emitCases :: Set StateId -> CharMap TDFATrans -> IRM (CharMap (Graph Insn O C))
emitCases nocheckStates trans = CM.traverse (emitCase nocheckStates) trans

labelBlock :: Graph Insn O C -> IRM Label
labelBlock b = do
  l <- freshLabel
  addBlock (mkLabel l H.<*> b)
  return l

emitTrans :: Set StateId -> CharMap TDFATrans -> Label -> IRM (Graph Insn O C)
emitTrans nocheckStates trans fail = do
    table <- CM.traverse labelBlock =<< emitCases nocheckStates trans
    return (mkLast (Switch table fail))

emitState :: TDFA -> Map StateId Int -> StateId -> IRM ()
emitState TDFA{..} minLengths s = mdo
  matchL <- gets matchLabel

  fallbackLabel <- labelBlock (fallbackRegOps matchL)
  eolLabel <- labelBlock (eolRegOps matchL)
  entryLabel <- getLabel (s, Checked)
  nocheckLabel <- getLabel (s, Unchecked)
  addBlock (mkLabel nocheckLabel H.<*> maybeSetFallback fallbackLabel H.<*>
            mkBranch body)
  addBlock (mkLabel entryLabel H.<*>
    -- SimulateTDFA does this after incPos for the state we're going to, so
    -- do it first thing in the state block. Should be the same, I hope :)
    maybeSetFallback fallbackLabel H.<*>
    mkBranch (if minLength > 1 then checkMinLength else checkEOFLabel))
  checkMinLength <- labelBlock (checkBounds minLength failLabel body)
  checkEOFLabel <- labelBlock (checkEOF eolLabel body)
  defaultLabel <- if isFinalState
                    then labelBlock (emitEndRegOps tdfaFinalFunction H.<*>
                                     goto matchL)
                    else return failLabel
  failLabel <- labelBlock (mkLast Fallback)
  switch <- emitTrans nocheckStates trans defaultLabel
  body <- labelBlock (yystats "visited_chars" 1 H.<*> switch)
  return ()
  where
    trans = M.findWithDefault CM.empty s tdfaTrans
    isFallbackState = M.member s tdfaFallbackFunction
    isFinalState = M.member s tdfaFinalFunction
    isEOLState = M.member s tdfaEOL

    eolRegOps :: Label -> Graph Insn O C
    eolRegOps matchLabel
      | isEOLState = emitEndRegOps tdfaEOL H.<*> goto matchLabel
      | isFinalState = emitEndRegOps tdfaFinalFunction H.<*> goto matchLabel
      | otherwise = gofail

    fallbackRegOps :: Label -> Graph Insn O C
    fallbackRegOps matchLabel | isFallbackState || isFinalState =
        mkMiddle RestoreCursor H.<*>
        -- debug ("Fell back to " <> show s <> " at {{YYPOS}}") <>
        emitEndRegOps (tdfaFallbackFunction `M.union` tdfaFinalFunction) H.<*>
        goto matchLabel
                              | otherwise = gofail

    emitEndRegOps opfun = foldMap emitRegOp (M.findWithDefault [] s opfun)

    maybeSetFallback l | isFinalState = mkMiddles [SaveCursor, SetFallback l]
                       | otherwise    = emptyGraph

    minLength | Just min <- M.lookup s minLengths, min > 1 = min
              | otherwise = 0

    nocheckStates
      | minLength > 0 = M.keysSet (M.filter (< minLength) minLengths)
      | otherwise = S.empty

emitIR :: TDFA -> IRM Program
emitIR tdfa@TDFA{..} = mdo
  setMatchLabel matchLabel

  mapM_ (emitState tdfa tdfaMinLengths) (tdfaStates tdfa)
  matchLabel <- labelBlock (mkLast (Match finalTagRegMap))

  startLabelNotBOL <- getLabel (tdfaStartStateNotBOL, Checked)
  startLabelBOL <- getLabel (tdfaStartState, Checked)

  let startNotBOL | onlyMatchAtBOL = justFail
                  | otherwise      = startLabelNotBOL

  -- Probably redundant since the checked entry will also check bounds.
  startBOL <- case M.lookup tdfaStartState tdfaMinLengths of
    Just dist -> labelBlock (checkBounds dist justFail startLabelBOL)
    Nothing   -> return justFail

  entry <- labelBlock (mkMiddles [SaveCursor, SetFallback failLabel] H.<*>
    mkLast (IfBOL startBOL startNotBOL))

  -- We get here if we reach the original fallback, i.e. we reach a state where
  -- it's impossible to match the rest of the string.
  failLabel <- labelBlock (mkMiddle RestoreCursor H.<*> checkEOF justFail retry)
  justFail <- labelBlock (mkLast Fail)
  -- We have a check bounds and restore cursor before this so we know we're not
  -- at the end of the string and can safely call Next. Then repeat matching
  -- from the starting not-BOL state.
  retry <- labelBlock (mkMiddles [Next, SaveCursor, SetFallback failLabel]
                       H.<*> goto startNotBOL)
  g <- gets graph
  return (entry, g)

  where
    allTags = S.union (M.keysSet tdfaFixedTags) (M.keysSet tdfaFinalRegisters)
    allRegs = tdfaRegisters tdfa
    tdfaMinLengths = minLengths tdfa
    onlyMatchAtBOL = not (M.member tdfaStartStateNotBOL tdfaMinLengths)

    finalTagRegMap = M.union finalTagRegs fixedTags
    finalTagRegs = M.map (\r -> Reg r 0) tdfaFinalRegisters
    fixedTags = M.map f tdfaFixedTags
      where f (TR.EndOfMatch d) = IR.EndOfMatch d
            f (TR.FixedTag t d) = add d (M.lookup t finalTagRegs)
            add d2 (Just (Reg r d1)) = Reg r (d1 + d2)

genIR :: TDFA -> Program
genIR tdfa = evalState (emitIR tdfa) initState

tdfa2ir :: Maybe IntSet -> Regex -> Program
tdfa2ir used = genIR . genTDFA . genTNFA . fixTags . unusedTags . tagRegex
  where unusedTags | Just s <- used = selectTags (\(T t) -> t `IS.member` s)
                   | otherwise = id

testTDFA2IR :: String -> Program
testTDFA2IR = genIR . genTDFA . genTNFA . testTagRegex
