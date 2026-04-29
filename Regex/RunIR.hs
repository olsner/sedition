{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, RecursiveDo, OverloadedStrings, RecordWildCards, ImportQualifiedPost #-}

module Regex.RunIR where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict

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
             debugEnabled :: Bool }
         deriving (Show)

initState s p = S {
  buffer = s,
  bufferLength = length s,
  registers = M.empty,
  program = p,
  fallbackLabel = Nothing,
  debugEnabled = True }

showState S{..} = "@" ++ show registers

blocks S{ program = Program { programGraph = GMany _ blocks _ } } = blocks

type Result = Maybe (Map TagId Int)

type M a = StateT S (Either Result) a

char (r, i) = gets (\S{..} -> buffer !! (registers M.! r + i))

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
run (IfBOL r tl fl) = do
  bol <- (<= 0) <$> getReg' r
  runLabel (if bol then tl else fl)
run (Switch offset cm def) = do
  c <- char offset
  runLabel (CM.findWithDefault def c cm)
run (TotalSwitch offset cm) = do
  c <- char offset
  runLabel (fromJust $ CM.lookup c cm)
run Fail = lift (Left Nothing)
run (Match tagMap) = do
  regs <- gets registers
  lift (Left (Just (resolveTagMap regs tagMap)))
run (CheckBounds (r, n) eof cont) = do
  len <- gets bufferLength
  pos <- getReg' r
  trace (show (pos,n,len)) (return ())
  runLabel (if pos + n > len then eof else cont)
run (Branch l) = runLabel l

run (Trace msg) = do
    s <- get
    when (debugEnabled s) $ traceM (msg ++ ": " ++ showState s)
run (Set r (r2, i)) = setReg r =<< (+ i) <$> getReg' r2
run (Clear r) = clearReg r
run (Copy r r2) = setReg' r =<< getReg r2
run (InitCursor r) = setReg r 0

run (Fallback _) = runLabel =<< gets (fromJust . fallbackLabel)
run (SetFallback l) = modify $ \s -> s { fallbackLabel = Just l }

resolveTagMap regs = M.map f
  where
    f (IR.Reg r d) | Just val <- M.lookup r regs = val - d
                   | otherwise = (-1)

testRunIR :: String -> String -> Result
testRunIR re s = runIR s . fst . optimize 10000 . testTDFA2IR $ re
