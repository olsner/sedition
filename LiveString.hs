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

-- Operations that write to a string variable kill it (i.e. the previous value
-- is now irrelevant).
kill :: Insn e x -> LiveStringFact -> LiveStringFact
kill (SetS s _) = S.delete s
kill (GetMessage s) = S.delete s
kill (Read s _) = S.delete s
kill _ = id

-- Operations that read from a string variable 'gen' it.
gen :: Insn e x -> LiveStringFact -> LiveStringFact
gen (SetS _ expr) = genS expr
gen (AppendS _ s) = S.insert s
gen (Print _ s) = S.insert s
gen (Message s) = S.insert s
gen (ShellExec s) = S.insert s
gen (SetM _ (Match s _)) = S.insert s
gen (SetM _ (MatchLastRE s)) = S.insert s
gen _ = id

genS :: StringExpr -> LiveStringFact -> LiveStringFact
genS (SVarRef s) = S.insert s
genS (SAppendNL s1 s2) = S.insert s1 . S.insert s2
genS (SAppend s1 s2) = S.insert s1 . S.insert s2
genS (STrans _ _ s) = S.insert s
genS (SSubstring s _ _) = S.insert s
genS (SFormatLiteral _ s) = S.insert s
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

    fact f l = fromMaybe S.empty (mapLookup l f)
    facts ls f = S.unions (map (fact f) ls)

liveString :: FuelMonad m => BwdRewrite m Insn LiveStringFact
liveString = mkBRewrite3 norw rw norw
  where
    remove :: FuelMonad m => m (Maybe (Graph Insn O O))
    remove = return (Just emptyGraph)
    replace :: FuelMonad m => [Insn O O] -> m (Maybe (Graph Insn O O))
    replace new = return (Just (mkMiddles new))
    dead s f = not (S.member s f)

    norw :: FuelMonad m => Insn e x -> Fact x LiveStringFact -> m (Maybe (Graph Insn e x))
    norw _ _ = return Nothing
    rw :: FuelMonad m => Insn O O -> Fact O LiveStringFact -> m (Maybe (Graph Insn O O))
    rw (SetS s _) f | dead s f = remove
    rw (SetS s (SAppend s1 s2)) f
                    | dead s1 f = replace [AppendS s1 s2, SetS s (SVarRef s1)]
    rw (AppendS s _) f | dead s f = remove
    -- Read and GetMessage both have side effects, so don't remove those even
    -- if the result is unused.
    rw _ _ = return Nothing

liveStringPass :: FuelMonad m => BwdPass m Insn LiveStringFact
liveStringPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveStringTransfer
  , bp_rewrite = liveString }

