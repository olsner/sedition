{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

-- liveStringPass: Find and remove strings that are never read.

module LiveString (liveStringPass) where

import Compiler.Hoopl as H

--import Debug.Trace

import Collections
import IR

type LiveStringFact = SVarSet
liveLattice :: DataflowLattice LiveStringFact
liveLattice = DataflowLattice
 { fact_name = "Live string"
 , fact_bot  = setEmpty
 , fact_join = add }
 where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `setUnion` old
              ch = changeIf (setSize j > setSize old)

-- Operations that write to a string variable kill it (i.e. the previous value
-- is now irrelevant).
kill :: Insn e x -> LiveStringFact -> LiveStringFact
kill (SetS s _) = setDelete s
kill (GetMessage s) = setDelete s
kill (Read s _) = setDelete s
kill (ReadFile s _) = setDelete s
kill _ = id

-- Operations that read from a string variable 'gen' it.
gen :: Insn e x -> LiveStringFact -> LiveStringFact
gen (SetS _ expr) = genS expr
gen (SetM _ expr) = genM expr
gen (Print _ s) = setInsert s
gen (Message s) = setInsert s
gen (ShellExec s) = setInsert s
gen _ = id

genM (Match s _) = setInsert s
genM (MatchLastRE s) = setInsert s
genM (NextMatch _ s) = setInsert s
genM (MVarRef _) = id

genS :: StringExpr -> LiveStringFact -> LiveStringFact
genS (SVarRef s) = setInsert s
genS (SAppendNL s1 s2) = setInsert s1 . setInsert s2
genS (SAppend s1 s2) = setInsert s1 . setInsert s2
genS (STrans _ _ s) = setInsert s
genS (SSubstring s _ _) = setInsert s
genS (SFormatLiteral _ s) = setInsert s
genS (SConst _) = id
genS (SRandomString) = id
genS (SGetLineNumber) = id

liveStringTransfer :: BwdTransfer Insn LiveStringFact
liveStringTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LiveStringFact -> LiveStringFact
    first (Label _)  f = f
    middle :: Insn O O -> LiveStringFact -> LiveStringFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LiveStringFact -> LiveStringFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact f l = mapFindWithDefault setEmpty l f
    facts ls f = setUnions (map (fact f) ls)

liveString :: FuelMonad m => BwdRewrite m Insn LiveStringFact
liveString = deepBwdRw rw
  where
    remove :: FuelMonad m => m (Maybe (Graph Insn O O))
    remove = return (Just emptyGraph)
    replace :: FuelMonad m => [Insn O O] -> m (Maybe (Graph Insn O O))
    replace new = return (Just (mkMiddles new))
    dead s f = not (setMember s f)

    rw :: FuelMonad m => Insn e x -> Fact x LiveStringFact -> m (Maybe (Graph Insn e x))
    rw i@(SetS s _) f | dead s f = remove
    -- Read and GetMessage both have side effects, so don't remove those even
    -- if the result is unused.
    rw _ _ = return Nothing

liveStringPass :: FuelMonad m => BwdPass m Insn LiveStringFact
liveStringPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveStringTransfer
  , bp_rewrite = liveString }

