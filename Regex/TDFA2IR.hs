{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances,FlexibleInstances,FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Regex.TDFA2IR where

import Compiler.Hoopl as H hiding (addBlock)

import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS

import qualified CharMap as CM
import CharMap (CharMap)

import Regex.Regex (Regex)
import Regex.TaggedRegex as TR
import Regex.TNFA (genTNFA)
import Regex.TDFA as TDFA hiding (initState, nextReg, newReg)
import Regex.IR as IR

data LabelType = Checked | Unchecked deriving (Show, Ord, Eq)
type StateLabel = (StateId, LabelType)

data IRState = IRState {
    firstFreeUnique :: Int,
    graph :: Graph Insn C C,
    labelMap :: Map StateLabel Label,
    fallbackReg :: R,
    freeRegister :: R
  } deriving (Show)

nextReg (R r) = R (succ r)
initState r1 = IRState 0 emptyClosedGraph M.empty r1 r2
  where
    r2 = nextReg r1

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

newReg :: IRM R
newReg = do
 r <- gets freeRegister 
 modify $ \s -> s { freeRegister = nextReg r }
 return r

addBlock :: Graph Insn C C -> IRM ()
addBlock block = modify $ \s@IRState{..} -> s { graph = graph |*><*| block }

goto :: Label -> Graph Insn O C
goto l = mkLast (Branch l)
gofail :: Graph Insn O C
gofail = mkLast (Fallback setEmpty)

checkBounds pos eof cont = mkLast (CheckBounds pos eof cont)
checkEOF offset = checkBounds (offset + 1)

gostate :: StateLabel -> IRM (Graph Insn O C)
gostate s = getLabel s >>= return . goto
gostate_nocheck :: StateId -> IRM (Graph Insn O C)
gostate_nocheck s = (yystats "goto_nocheck" 1 H.<*>) <$> gostate (s, Unchecked)
gostate_check s = gostate (s, Checked)

yystats :: String -> Int -> Graph Insn O O
yystats _ _ = emptyGraph

debug _ = emptyGraph
--debug msg = mkMiddle (Trace msg)

moveCursor :: Int -> Graph Insn O O
moveCursor 0 = emptyGraph
moveCursor i | i > 0 = mkMiddle (MoveCursor i)
             | i < 0 = error "Negative cursor movement!"

emitRegOp :: Int -> RegOp -> Graph Insn O O
emitRegOp offset (r,val) = mkMiddle (g val) H.<*> yystats "regops" 1
  where
    g (SetReg Pos) = SaveCursor r offset
    g (SetReg Nil) = Clear r
    g (CopyReg r2) = Copy r r2

emitCase :: Set StateId -> Map StateId Int -> Int -> TDFATrans -> IRM Label
emitCase nocheckStates readOffsets offset (s', regops) = do
  go <- if skipCheck then gostate_nocheck s' else gostate_check s'
  let block = foldMap (emitRegOp offset) regops H.<*> moveCursor neededMove H.<*> go
  labelBlock block
  where skipCheck = S.member s' nocheckStates
        targetOffset = M.findWithDefault 0 s' readOffsets
        neededMove = offset + 1 - targetOffset

emitCases :: Set StateId -> Map StateId Int -> Int -> CharMap TDFATrans -> IRM (CharMap Label)
emitCases nocheckStates readOffsets offset trans = CM.traverse (emitCase nocheckStates readOffsets offset) trans

labelBlock :: Graph Insn O C -> IRM Label
labelBlock b = do
  l <- freshLabel
  addBlock (mkLabel l H.<*> b)
  return l

emitTrans :: Set StateId -> Map StateId Int -> Int -> CharMap TDFATrans -> Label -> IRM (Graph Insn O C)
emitTrans nocheckStates readOffsets offset trans fail | CM.null trans = return (goto fail)
emitTrans nocheckStates readOffsets offset trans fail = do
    table <- emitCases nocheckStates readOffsets offset trans
    return (mkLast (mkSwitch offset table fail))

mkSwitch pos table def | CM.isComplete table = TotalSwitch pos table
                       | otherwise           = Switch pos table def

emitState :: TDFA -> StateId -> IRM ()
emitState tdfa@TDFA{..} s = mdo
  body <- labelBlock (debug ("state " ++ show s) H.<*> yystats "visited_chars" 1 H.<*> switch)
  switch <- emitTrans nocheckStates readOffsets offset trans defaultLabel

  fc <- gets fallbackReg

  matchL <- genMatchCode tdfa offset
  fallbackLabel <- labelBlock (fallbackRegOps fc)
  eolLabel <- labelBlock (eolRegOps matchL)
  entryLabel <- getLabel (s, Checked)
  nocheckLabel <- getLabel (s, Unchecked)
  addBlock (mkLabel nocheckLabel H.<*> maybeSetFallback fc fallbackLabel H.<*>
            mkBranch body)
  addBlock (mkLabel entryLabel H.<*>
    -- SimulateTDFA does this after incPos for the state we're going to, so
    -- do it first thing in the state block. Should be the same, I hope :)
    maybeSetFallback fc fallbackLabel H.<*>
    mkBranch (if minLength > 1 then checkMinLength else checkEOFLabel))
  checkMinLength <- labelBlock (checkBounds (offset + minLength) failLabel body)
  checkEOFLabel <- labelBlock (checkEOF offset eolLabel body)
  defaultLabel <- if isFinalState
                    then labelBlock (debug ("default-transition from final " ++ show s) H.<*>
                                     emitEndRegOps offset tdfaFinalFunction H.<*>
                                     matchL)
                    else return failLabel
  failLabel <- labelBlock (debug ("default-transition from non-final " ++ show s) H.<*> gofail)
  return ()
  where
    trans = M.findWithDefault CM.empty s tdfaTrans
    isFallbackState = M.member s tdfaFallbackFunction
    isFinalState = M.member s tdfaFinalFunction
    isEOLState = M.member s tdfaEOL

    readOffsets = tdfaReadOffsets -- M.empty
    offset = M.findWithDefault 0 s readOffsets

    eolRegOps :: Graph Insn O C -> Graph Insn O C
    eolRegOps matchCode
      | isEOLState = emitEndRegOps offset tdfaEOL H.<*> matchCode
      | isFinalState = emitEndRegOps offset tdfaFinalFunction H.<*> matchCode
      | otherwise = gofail

    fallbackRegOps :: RegId -> Graph Insn O C
    fallbackRegOps fc | isFallbackState || isFinalState =
        mkMiddle (LoadCursor fc) H.<*>
        -- debug ("Fell back to " <> show s <> " at {{YYPOS}}") <>
        emitEndRegOps 0 (tdfaFallbackFunction `M.union` tdfaFinalFunction) H.<*>
        matchCode tdfa fc
                              | otherwise = gofail

    -- TODO Remove the emitted reg ops - since we're already duplicating the
    -- match code we should give that one a map instead.
    emitEndRegOps offset opfun = foldMap (emitRegOp offset) (M.findWithDefault [] s opfun)

    maybeSetFallback fc l | isFinalState = debug ("setting fallback in " ++ show s) H.<*> mkMiddles [SaveCursor fc offset, SetFallback l]
                       | otherwise    = debug ("no fallback from " ++ show s)

    minLength | Just min <- M.lookup s tdfaMinLengths, min > 1 = min
              | otherwise = 0

    nocheckStates
      | minLength > 0 = M.keysSet (M.filter (< minLength) tdfaMinLengths)
      | otherwise = S.empty

emitIR :: TDFA -> IRM Program
emitIR tdfa@TDFA{..} = mdo
  fc <- gets fallbackReg

  entry <- labelBlock (mkMiddles [SaveCursor fc 0, SetFallback failLabel] H.<*>
    mkLast (IfBOL startLabelBOL startNotBOL))

  startLabelNotBOL <- getLabel (tdfaStartStateNotBOL, Checked)
  startLabelBOL <- getLabel (tdfaStartState, Checked)

  mapM_ (emitState tdfa) (tdfaStates tdfa)

  let startNotBOL | onlyMatchAtBOL = justFail
                  | otherwise      = startLabelNotBOL

  -- We get here if we reach the original fallback, i.e. we reach a state where
  -- it's impossible to match the rest of the string.
  -- TODO Instead of just checkEOF, use the min length of startNotBOL (plus one), then use the unchecked label for startNotBOL below.
  failLabel <- labelBlock (mkMiddle (LoadCursor fc) H.<*> checkEOF 0 justFail retry)
  justFail <- labelBlock (mkLast Fail)
  -- We have a check bounds and restore cursor before this so we know we're not
  -- at the end of the string and can safely move the cursor by one at least.
  -- Then repeat matching from the starting not-BOL state.
  retry <- labelBlock (mkMiddles [MoveCursor 1, Trace "retrying", SaveCursor fc 0, SetFallback failLabel]
                       H.<*> goto startNotBOL)
  g <- gets graph
  return (finishProgram entry g)

  where
    onlyMatchAtBOL = not (M.member tdfaStartStateNotBOL tdfaMinLengths)

genMatchCode :: TDFA -> Int -> IRM (Graph Insn O C)
genMatchCode tdfa offset = do
  c <- newReg
  return (mkMiddle (SaveCursor c offset) H.<*> matchCode tdfa c)

matchCode :: TDFA -> R -> Graph Insn O C
matchCode TDFA{..} c = mkLast (Match (finalTagRegMap c))
  where
    finalTagRegMap c = M.union finalTagRegs (fixedTags c)
    finalTagRegs = M.map (\r -> Reg r 0) tdfaFinalRegisters
    fixedTags c = M.map f tdfaFixedTags
      where f (TR.EndOfMatch d) = Reg c d
            f (TR.FixedTag t d) = add d (M.lookup t finalTagRegs)
            add d2 ~(Just (Reg r d1)) = Reg r (d1 + d2)

genIR :: TDFA -> Program
genIR tdfa = evalState (emitIR tdfa) (initState freeReg)
 where freeReg | regs <- tdfaRegisters tdfa, not (null regs) = nextReg (maximum regs)
               | otherwise = R 0

tdfa2ir :: Maybe IntSet -> Regex -> Program
tdfa2ir used = genIR . genTDFA . genTNFA . fixTags . makeSearchRegex . unusedTags . tagRegex
  where unusedTags | Just s <- used = selectTags (\(T t) -> t `IS.member` s)
                   | otherwise = id

testTDFA2IR :: String -> Program
testTDFA2IR = genIR . genTDFA . genTNFA . testTagRegex
