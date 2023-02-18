{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

-- constLastRegexPass: Inline where LastRegexRE is known
-- liveLastRegexPass: Remove unnecessary updates to LastRegexRE

module LiveLastRegex (liveLastRegexPass, constLastRegexPass) where

import Compiler.Hoopl as H hiding (joinMaps)

import Data.IntSet (IntSet)
import qualified Data.IntSet as S
import Data.List (isInfixOf)

import Debug.Trace

import Collections
import IR

-- TODO We can just do const lastregex, and if we remove every MatchLastRE we
-- can also simply remove all SetLastRegex updates in LiveMatch.
type LastRegexLiveFact = Bool

liveLattice :: DataflowLattice LastRegexLiveFact
liveLattice = DataflowLattice
 { fact_name = "Live lastregex"
 , fact_bot  = False
 , fact_join = add }
 where
    add _ (OldFact old) (NewFact new) = (ch, j)
      where
        j = new || old
        ch = changeIf (j /= old)

kill :: Insn e x -> LastRegexLiveFact -> LastRegexLiveFact
kill (SetLastRE _) = const False
kill _ = id

-- Operations that read from a string variable 'gen' it.
gen :: Insn e x -> LastRegexLiveFact -> LastRegexLiveFact
gen (SetM _ (MatchLastRE _)) = const True
gen _ = id

liveLastRegexTransfer :: BwdTransfer Insn LastRegexLiveFact
liveLastRegexTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LastRegexLiveFact -> LastRegexLiveFact
    first (Label _)  f = f
    middle :: Insn O O -> LastRegexLiveFact -> LastRegexLiveFact
    middle insn = gen insn . kill insn
    last :: Insn O C -> FactBase LastRegexLiveFact -> LastRegexLiveFact
    last insn = gen insn . kill insn . facts (successors insn)

    fact :: FactBase LastRegexLiveFact -> Label -> LastRegexLiveFact
    fact f l = mapFindWithDefault False l f
    facts :: [Label] -> FactBase LastRegexLiveFact -> LastRegexLiveFact
    facts ls f = or (map (fact f) ls)

liveLastRegex :: FuelMonad m => BwdRewrite m Insn LastRegexLiveFact
liveLastRegex = deepBwdRw rw
  where
    remove :: FuelMonad m => m (Maybe (Graph Insn O O))
    remove = return (Just emptyGraph)

    rw :: FuelMonad m => Insn e x -> Fact x LastRegexLiveFact -> m (Maybe (Graph Insn e x))
    rw (SetLastRE _) False = remove
    rw _ _ = return Nothing

liveLastRegexPass :: FuelMonad m => BwdPass m Insn LastRegexLiveFact
liveLastRegexPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveLastRegexTransfer
  , bp_rewrite = liveLastRegex }

-- Bottom = don't know (yet), Top = can be anything
type ConstLastRegexFact = WithTopAndBot RE

constLattice :: DataflowLattice ConstLastRegexFact
constLattice = addPoints' "Const LastRegex" join
 where
   join _ (OldFact old) (NewFact new)
       = if new == old then (NoChange, PElem new)
         else               (SomeChange, Top)

constLastRegexTransfer :: FwdTransfer Insn ConstLastRegexFact
constLastRegexTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> ConstLastRegexFact -> ConstLastRegexFact
    first (Label _)  f = f
    middle :: Insn O O -> ConstLastRegexFact -> ConstLastRegexFact
    middle (SetLastRE re) _ = PElem re
    middle _              f = f
    last :: Insn O C -> ConstLastRegexFact -> FactBase ConstLastRegexFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase constLattice [(l, f) | l <- ls]

constLastRegex :: FuelMonad m => FwdRewrite m Insn ConstLastRegexFact
constLastRegex = deepFwdRw rw
  where
    replace :: FuelMonad m => [Insn O O] -> m (Maybe (Graph Insn O O))
    replace new = return (Just (mkMiddles new))

    rw :: FuelMonad m => Insn e x -> ConstLastRegexFact -> m (Maybe (Graph Insn e x))
    rw (SetM m (MatchLastRE s)) (PElem re) = replace [SetM m (Match s re)]
    rw _ _ = return Nothing

constLastRegexPass :: FuelMonad m => FwdPass m Insn ConstLastRegexFact
constLastRegexPass = FwdPass
  { fp_lattice = constLattice
  , fp_transfer = constLastRegexTransfer
  , fp_rewrite = constLastRegex }
