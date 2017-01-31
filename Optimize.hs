{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

#define DEBUG 0

module Optimize where

import Compiler.Hoopl as H

import Control.Monad
import Control.Monad.Trans.State.Strict

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace

import Parser

import qualified AST

import Compiler.Hoopl

import IR

-- import ConstPred (constPredPass)

type ConstPredFact = Map Pred (WithTop Bool)
constLattice :: DataflowLattice ConstPredFact
constLattice = DataflowLattice
 { fact_name = "Const predicate"
 , fact_bot  = M.empty
 , fact_join = joinMaps (extendJoinDomain constFactAdd) }
 where
   constFactAdd _ (OldFact old) (NewFact new)
       = if new == old then (NoChange, PElem new)
         else               (SomeChange, Top)

constPredTransfer :: FwdTransfer Insn ConstPredFact
constPredTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> ConstPredFact -> ConstPredFact
    -- C O
    first (Label l)  f = f

    -- O O
    middle :: Insn O O -> ConstPredFact -> ConstPredFact
    middle (Set p x)       f = M.insert p (PElem x) f
    middle (AtEOF p)       f = M.delete p f
    middle (Line _ p)      f = M.delete p f
    middle (Match _ p)     f = M.delete p f
    middle (MatchLastRE p) f = M.delete p f

    middle insn f = trace ("Unhandled instruction " ++ show insn) f

    -- O C
    last :: Insn O C -> ConstPredFact -> FactBase ConstPredFact
    last (Branch l) f = mapSingleton l f
    last (If p tl fl) f = mkFactBase constLattice
           [(tl, M.insert p (PElem True)  f),
            (fl, M.insert p (PElem False) f)]
    last (Read _ (Just intr) read) f = boringFactBase f [intr,read]
    last (Read _ Nothing read) f = boringFactBase f [read]
    last (Quit _) f = mkFactBase constLattice []
    -- Is this correct? We probably reset some of these in forkState
    last (Fork a b) f = boringFactBase f [a,b]

    boringFactBase f ls = mkFactBase constLattice [(l, f) | l <- ls]

constPred :: FuelMonad m => FwdRewrite m Insn ConstPredFact
constPred = mkFRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> ConstPredFact -> m (Maybe (Graph Insn e x))
    rw (Label l) f = return Nothing

    rw (Set p x) f = return Nothing

    rw (If p tl fl) f =
      case M.lookup p f of
        Just (PElem b) -> return (Just (mkLast (Branch (if b then tl else fl))))
        _ -> return Nothing

    rw _ f = return Nothing

constPredPass :: FuelMonad m => FwdPass m Insn ConstPredFact
constPredPass = FwdPass
  { fp_lattice = constLattice
  , fp_transfer = constPredTransfer
  , fp_rewrite = constPred {- `thenFwdRw` simplify -} }

openEntry :: LabelsPtr [Label] => MaybeC O [Label]
openEntry = NothingC

optimize' :: (CheckpointMonad m, FuelMonad m) => Graph Insn O C -> m (Graph Insn O C)
optimize' program = do
  (program,_,_) <- analyzeAndRewriteFwd constPredPass openEntry program M.empty
  return program

runSFM :: Fuel -> SimpleFuelMonad a -> a
runSFM fuel m = runSimpleUniqueMonad (runWithFuel fuel m)

optimize fuel p = runSFM fuel (optimize' p)
