{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module ConstPred (constPredPass) where

import Compiler.Hoopl as H

import Data.Map (Map)
import qualified Data.Map as M
--import Debug.Trace

import IR

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
    first (Label _)  f = f

    -- O O
    middle :: Insn O O -> ConstPredFact -> ConstPredFact
    middle (SetP p (Bool x)) f = M.insert p (PElem x) f
    middle (SetP p _)        f = M.insert p Top f

    middle _insn f = {-trace ("Unhandled instruction " ++ show insn)-} f

    -- O C
    last :: Insn O C -> ConstPredFact -> FactBase ConstPredFact
    last (Branch l) f = mapSingleton l f
    last (If p tl fl) f = mkFactBase constLattice
           [(tl, M.insert p (PElem True)  f),
            (fl, M.insert p (PElem False) f)]
    last (Cycle _ intr read eof) f = boringFactBase f [intr,read,eof]
    last (Quit _) _ = mapEmpty
    -- Is this correct? We probably reset some of these in forkState
    last (Fork a b) f = boringFactBase f [a,b]

    boringFactBase f ls = mkFactBase constLattice [(l, f) | l <- ls]

constPred :: FuelMonad m => FwdRewrite m Insn ConstPredFact
constPred = deepFwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> ConstPredFact -> m (Maybe (Graph Insn e x))
    rw (If p tl fl) f =
      case M.lookup p f of
        Just (PElem b) -> return (Just (mkLast (Branch (if b then tl else fl))))
        _ -> return Nothing

    rw _ _ = return Nothing

constPredPass :: FuelMonad m => FwdPass m Insn ConstPredFact
constPredPass = FwdPass
  { fp_lattice = constLattice
  , fp_transfer = constPredTransfer
  , fp_rewrite = constPred }

