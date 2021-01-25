{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

-- liveStringPass: Find and remove strings that are never read.

module LiveString (liveStringPass) where

import Compiler.Hoopl as H

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
--import Debug.Trace

import IR

type LiveStringFact = Set SVar
liveLattice :: DataflowLattice LiveStringFact
liveLattice = DataflowLattice
 { fact_name = "Live string"
 , fact_bot  = S.empty
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `S.union` old
              ch = changeIf (S.size j > S.size old)

-- Operations that write to a string variable kill it
kill :: Insn e x -> LiveStringFact -> LiveStringFact
kill (SetS s _) = S.delete s
kill (GetMessage s) = S.delete s
kill (Read s _) = S.delete s
kill _ = id

-- Operations that read from a string variable 'gen' it.
gen :: Insn e x -> LiveStringFact -> LiveStringFact
gen (SetS _ expr) = genS expr
gen (PrintLiteral _ _ s) = S.insert s
gen (Print _ s) = S.insert s
gen (Message s) = S.insert s
gen (ShellExec s) = S.insert s
gen (WriteFile _ s) = S.insert s
gen (SetP _ (Match s _)) = S.insert s
gen (SetP _ (MatchLastRE s)) = S.insert s
gen _ = id

genS :: StringExpr -> LiveStringFact -> LiveStringFact
genS (SVarRef s) = S.insert s
genS (SAppendNL s1 s2) = S.insert s1 . S.insert s2
genS (SSubst s _ _) = S.insert s
genS (STrans _ _ s) = S.insert s
genS (SConst _) = id
genS (SRandomString) = id

liveStringTransfer :: BwdTransfer Insn LiveStringFact
liveStringTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LiveStringFact -> LiveStringFact
    first (Label _)  f = f
    -- TODO Which order should gen and kill be done to work correctly when a
    -- variable is both killed and genned? This matches what we do in LivePred.
    middle :: Insn O O -> LiveStringFact -> LiveStringFact
    middle insn = kill insn . gen insn
    last :: Insn O C -> FactBase LiveStringFact -> LiveStringFact
    last insn = kill insn . gen insn . facts (successors insn)

    fact f l = fromMaybe S.empty (mapLookup l f)
    facts ls f = S.unions (map (fact f) ls)

liveString :: FuelMonad m => BwdRewrite m Insn LiveStringFact
liveString = mkBRewrite rw
  where
    rw :: FuelMonad m => Insn e x -> Fact x LiveStringFact -> m (Maybe (Graph Insn e x))
    rw (SetS s _) f | not (S.member s f) = return (Just emptyGraph)
    -- Read and GetMessage both have side effects, so don't remove those.
    rw _ _ = return Nothing

liveStringPass :: FuelMonad m => BwdPass m Insn LiveStringFact
liveStringPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveStringTransfer
  , bp_rewrite = liveString }


