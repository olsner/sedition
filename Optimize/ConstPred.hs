{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Optimize.ConstPred (constPredPass) where

import Compiler.Hoopl as H hiding (joinMaps)

import Debug.Trace

import IR
import Collections

type ConstPredFact = PredMap (WithTop Bool)

constLattice :: DataflowLattice ConstPredFact
constLattice = DataflowLattice
 { fact_name = "Const predicate"
 , fact_bot  = mapEmpty
 , fact_join = joinMaps (extendJoinDomain constFactAdd) }
 where
   constFactAdd l (OldFact old) (NewFact new)
       = if new == old then (NoChange, PElem new)
         else               {-trace (show l ++ ": " ++ show old ++ " <> " ++ show new)-} (SomeChange, Top)

constPredTransfer :: FwdTransfer Insn ConstPredFact
constPredTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> ConstPredFact -> ConstPredFact
    -- C O
    first (Label _)  f = f

    -- O O
    middle :: Insn O O -> ConstPredFact -> ConstPredFact
    middle (SetP p x) f = mapInsert p (PElem x) f
    middle _insn f = {-trace ("Unhandled instruction " ++ show insn)-} f

    -- O C
    last :: Insn O C -> ConstPredFact -> FactBase ConstPredFact
    last (Branch l) f = mapSingleton l f
    last (If (PRef p) tl fl) f = mkFactBase constLattice
           [(tl, mapInsert p (PElem True)  f),
            (fl, mapInsert p (PElem False) f)]
    last (If _ tl fl) f = boringFactBase f [tl,fl]
    last (Quit _) _ = mapEmpty
    -- Is this correct? We probably reset some of these in forkState
    last (Fork a b) f = boringFactBase f [a,b]

    boringFactBase f ls = mkFactBase constLattice [(l, f) | l <- ls]

constPred :: FuelMonad m => FwdRewrite m Insn ConstPredFact
constPred = deepFwdRw rw
  where
    rw :: FuelMonad m => Insn e x -> ConstPredFact -> m (Maybe (Graph Insn e x))
    rw (If (PRef p) tl fl) f =
      case mapLookup p f of
        Just (PElem b) | let dest = if b then tl else fl ->
            {-trace (show p ++ " = " ++ show b ++ " -> " ++ show dest) $-}
            return (Just (mkLast (Branch dest)))
        _ -> return Nothing

    rw _ _ = return Nothing

constPredPass :: FuelMonad m => FwdPass m Insn ConstPredFact
constPredPass = FwdPass
  { fp_lattice = constLattice
  , fp_transfer = constPredTransfer
  , fp_rewrite = constPred }
