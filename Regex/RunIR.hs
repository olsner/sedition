{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, RecursiveDo, OverloadedStrings, RecordWildCards, ImportQualifiedPost #-}

module Regex.RunIR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict

import Data.Bits
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe

import Debug.Trace

import CharMap as CM
import Regex.IR as IR
import Regex.TaggedRegex (TagId)
import Regex.TDFA2IR (testTDFA2IR)
import Regex.OptimizeIR (optimize)

data S = S { buffer :: String, bufferLength :: Int,
             registers :: Map R Int, program :: Program,
             fallbackLabel :: Maybe Label,
             position :: Int,
             debugEnabled :: Bool }
         deriving (Show)

initState s p = S {
  buffer = s,
  bufferLength = length s,
  registers = M.empty,
  program = p,
  fallbackLabel = Nothing,
  position = 0,
  debugEnabled = True }

showState S{..} = "@" ++ show position -- TODO Restore more printing now that we have a position

blocks S{ program = Program { programGraph = GMany _ blocks _ } } = blocks

type Result = Maybe (Map TagId Int)

type M a = StateT S (Either Result) a

char i = gets (\S{..} -> buffer !! (position + i))
word8 :: (Bits a, Enum a) => Int -> M a
word8 i = toEnum . fromEnum <$> char i
word16 i = do
  w1 <- word8 i
  w2 <- word8 (i + 1)
  return (w1 .|. (w2 `shiftL` 8))
word32 i = do
  w1 <- word16 i
  w2 <- word16 (i + 2)
  return (w1 .|. (w2 `shiftL` 16))

setPos i = modify $ \s -> s { position = i }
getReg r = gets (M.lookup r . registers)
getReg' r = fromJust <$> getReg r
setReg r val = modify $ \s@S{..} -> s { registers = M.insert r val registers }
clearReg r = modify $ \s@S{..} -> s { registers = M.delete r registers }

setReg' r (Just val) = setReg r val
setReg' r Nothing = clearReg r

runIR :: String -> Program -> Result
runIR s p = case evalStateT (runLabel (entryPoint p)) (initState s p) of
    Left res -> res
    Right () -> Nothing

runLabel :: H.Label -> M ()
runLabel entry = do
    block <- gets (mapLookup entry . blocks)
    case block of
      Just block -> runBlock block
      Nothing    -> error ("Entry " ++ show entry ++ " not found in graph?")

traceInsn n = do
  s <- get
  trace (showState s) (return ())
  trace (show n) (return ())

runBlock block = foldBlockNodesF (\n z -> z >> traceInsn n >> run n) block (return ())

run :: Insn e x -> M ()
run (Label _) = return ()

-- O C control flow
run (IfBOL tl fl) = do
  bol <- gets (\s -> position s <= 0)
  runLabel (if bol then tl else fl)
run (Switch offset cm def) = do
  c <- char offset
  runLabel (CM.findWithDefault def c cm)
run (TotalSwitch offset cm) = do
  c <- char offset
  runLabel (fromJust $ CM.lookup c cm)
run (CmpByte offset val tl fl) = do
  c <- word8 offset
  runLabel (if c == val then tl else fl)
run (CmpWord offset val tl fl) = do
  c <- word16 offset
  runLabel (if c == val then tl else fl)
run (CmpDWord offset val tl fl) = do
  c <- word32 offset
  runLabel (if c == val then tl else fl)
run Fail = lift (Left Nothing)
run (Match tagMap) = do
  regs <- gets registers
  pos <- gets position
  lift (Left (Just (resolveTagMap regs pos tagMap)))
run (CheckBounds n eof cont) = do
  S{..} <- get
  runLabel (if position + n > bufferLength then eof else cont)
run (Branch l) = runLabel l

run (Trace msg) = do
    s <- get
    when (debugEnabled s) $ traceM (msg ++ ": " ++ showState s)
run (Clear r) = clearReg r
run (Copy r r2) = setReg' r =<< getReg r2

run (SaveCursor r i) = setReg r =<< gets (\s -> position s + i)
run (LoadCursor r) = setPos =<< getReg' r
run (MoveCursor i) = modify $ \s -> s { position = position s + i }

run (Fallback _) = runLabel =<< gets (fromJust . fallbackLabel)
run (SetFallback l) = modify $ \s -> s { fallbackLabel = Just l }

resolveTagMap regs pos = M.map f
  where
    f (IR.Cursor d) = pos + d
    f (IR.Reg r d) | Just val <- M.lookup r regs = val - d
                   | otherwise = -1
    f (IR.NoTag) = -1

testRunIR :: String -> String -> Result
testRunIR re s = runIR s . fst . optimize 10000 . testTDFA2IR $ re
