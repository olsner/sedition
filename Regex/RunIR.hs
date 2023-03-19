{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, RecursiveDo, OverloadedStrings, RecordWildCards, ImportQualifiedPost #-}

module Regex.RunIR where

import Compiler.Hoopl as H

import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import Data.Map qualified as M

import CharMap as CM
import Regex.IR as IR
import Regex.TaggedRegex (TagId)
import Regex.TDFA2IR (testTDFA2IR)

data S = S { char :: Char, buffer :: String, bufferLength :: Int,
             registers :: Map R Int, position :: Int, program :: Program,
             fallbackCursor :: Int, fallbackLabel :: Label }
         deriving (Show)

initState s p = gonext $ S {
  char = error "No char",
  buffer = s,
  bufferLength = length s,
  registers = M.empty,
  position = (-1),
  program = p,
  fallbackCursor = error "Fallback cursor used before init",
  fallbackLabel = error "Fallback label used before init" }

blocks S{ program = (_, GMany _ blocks _) } = blocks

type Result = Maybe (Map TagId Int)

type M a = StateT S (Either Result) a

next :: M ()
next = modify gonext

gonext s@S{..} = case buffer of
    (x:xs) -> s { char = x, buffer = xs, position = succ position }
    [] -> s { position = succ position }

getReg r = gets (M.lookup r . registers)
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

runBlock block = foldBlockNodesF (\n z -> z >> run n) block (return ())

run :: Insn e x -> M ()
run (Label _) = return ()

-- O C control flow
run (IfBOL tl fl) = do
  bol <- gets ((<= 0) . position)
  runLabel (if bol then tl else fl)
run (Switch cm def) = do
  c <- gets char
  runLabel (CM.findWithDefault def c cm)
run Fail = lift (Left Nothing)
run (Match tagMap) = do
  regs <- gets registers
  pos <- gets position
  lift (Left (Just (resolveTagMap pos regs tagMap)))
run (CheckBounds n eof cont) = do
  len <- gets bufferLength
  pos <- gets position
  runLabel (if pos + n > len then eof else cont)
run (Branch l) = runLabel l

run Next = next
run (Set r) = setReg r =<< gets position
run (Clear r) = clearReg r
run (Copy r r2) = setReg' r =<< getReg r2

run Fallback = runLabel =<< gets fallbackLabel
run (SetFallback l) = modify $ \s -> s { fallbackLabel = l }
run SaveCursor = modify $ \s@S{..} -> s { fallbackCursor = position }
run RestoreCursor = modify $ \s@S{..} -> s { position = fallbackCursor }

resolveTagMap pos regs = M.map f
  where
    f (IR.EndOfMatch d) = pos - d
    f (IR.Reg r d) | Just val <- M.lookup r regs = val - d
                   | otherwise = (-1)

testRunIR :: String -> String -> Result
testRunIR re s = runIR s (testTDFA2IR re)
