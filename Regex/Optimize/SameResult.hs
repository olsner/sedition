{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.SameResult (sameResultPass) where

{- "Same result" optimization
 -
 - Skip over code that eventually leads to a known end result, e.g. a failed
 - match or a match with no tags. Matches with tags could be supported
 - eventually but requires more analysis to track equivalency between matched
 - results and not remove any necessary register operations or similar.
 -}

import Compiler.Hoopl as H

import qualified Data.Map as M
--import Debug.Trace

import Regex.IR

-- For now, we don't even try to handle matches that set tags
data SameResult = WillFail | MatchWithNoTags deriving (Eq,Ord)
type SameResultFact = WithTopAndBot SameResult

sameResultLattice :: DataflowLattice SameResultFact
sameResultLattice = addPoints' "Same result" add
 where add _ (OldFact old) (NewFact new)
         | old == new = (NoChange, PElem old)
         | otherwise  = (SomeChange, Top)

sameResultTransfer :: BwdTransfer Insn SameResultFact
sameResultTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> SameResultFact -> SameResultFact
    first (Label _) f            = f
    middle :: Insn O O -> SameResultFact -> SameResultFact
    middle _        f            = f
    last :: Insn O C -> FactBase SameResultFact -> SameResultFact
    last Fail       _            = PElem WillFail
    last (Match m)  _ | M.null m  = PElem MatchWithNoTags
                      | otherwise = Top
    last insn       f            = joinOutFacts sameResultLattice insn f

sameResult :: FuelMonad m => BwdRewrite m Insn SameResultFact
sameResult = mkBRewrite3 first middle last
  where
    first _ _ = return Nothing
    -- Skip all operations on the way to an inevitable result
    middle _ (PElem _) = return (Just emptyGraph)
    middle _ _ = return Nothing
    --  Replace branches to inevitable results with the inevitable result
    last i f | PElem res <- join i f = rwRes i res
    last _ _ = return Nothing

    join = joinOutFacts sameResultLattice
    rwRes old WillFail = rwLast old Fail
    rwRes old MatchWithNoTags = rwLast old (Match M.empty)
    rwLast _ new = return (Just (mkLast new))

sameResultPass :: FuelMonad m => BwdPass m Insn SameResultFact
sameResultPass = BwdPass
  { bp_lattice = sameResultLattice
  , bp_transfer = sameResultTransfer
  , bp_rewrite = sameResult }
