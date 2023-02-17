{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

-- liveMatchPass: Find and remove matches and submatches that are not used.

module LiveMatch (liveMatchPass, canApplyLiveMatch) where

import Compiler.Hoopl as H hiding (joinMaps)

import Data.IntSet (IntSet)
import qualified Data.IntSet as S
import Data.List (isInfixOf)

import Debug.Trace

import Collections
import IR

type LiveMatchFact = MVarMap IntSet
liveLattice :: DataflowLattice LiveMatchFact
liveLattice = DataflowLattice
 { fact_name = "Live match"
 , fact_bot  = mapEmpty
 , fact_join = joinMaps add }
 where
    add _ (OldFact old) (NewFact new) = (ch, j)
      where
        j = new `S.union` old
        ch = changeIf (S.size j > S.size old)

-- Tag indices for groups
startOfMatch = 0
endOfMatch = 1
startOfGroup i = 2 * i + 0
endOfGroup i = 2 * i + 1

mapSetInsert k v = mapInsertWith S.union k (S.singleton v)
-- Everything known about 'old' is now known about 'new', and 'old' is deleted.
-- E.g. 'old' is a match register being overwritten.
mapRename new old
    | new /= old = mapDelete old . (mapInsertWith S.union new =<< mapFindWithDefault S.empty old)
    | otherwise = error ("In-place modification of " ++ show new)

transferM :: MVar -> MatchExpr -> LiveMatchFact -> LiveMatchFact
transferM t (Match _ _) = mapDelete t
-- We have a separate pass that removes all resolvable LastRegex references,
-- but if that fails we'll just skip this optimization pass for the program.
-- See Optimize.hs.
transferM _ (MatchLastRE _) = error "Can't optimize LiveMatch with MatchLastRE"
transferM t (NextMatch m _) = mapSetInsert m endOfMatch . mapRename m t
-- Going backwards, t := s means that anything used in t after this needs to
-- be considered used in s as well.
transferM t (MVarRef s) = mapRename s t

genS :: StringExpr -> LiveMatchFact -> LiveMatchFact
genS (SSubstring _ i j) = genSI i . genSI j
genS _ = id

genSI :: SIndex -> LiveMatchFact -> LiveMatchFact
genSI (SIMatchStart m) = mapSetInsert m startOfMatch
genSI (SIMatchEnd m) = mapSetInsert m endOfMatch
genSI (SIGroupStart m i) = mapSetInsert m (startOfGroup i)
genSI (SIGroupEnd m i) = mapSetInsert m (endOfGroup i)
genSI SIStart = id
genSI SIEnd = id

liveMatchTransfer :: BwdTransfer Insn LiveMatchFact
liveMatchTransfer = mkBTransfer3 first middle last
  where
    first :: Insn C O -> LiveMatchFact -> LiveMatchFact
    first (Label _)  f = f
    middle :: Insn O O -> LiveMatchFact -> LiveMatchFact
    middle (SetS _ expr) = genS expr
    middle (SetM m expr) = transferM m expr
    middle _ = id
    last :: Insn O C -> FactBase LiveMatchFact -> LiveMatchFact
    last i@(If (IsMatch m) _ _) = mapInsertWith S.union m S.empty . facts i
    last insn = facts insn

    fact :: FactBase LiveMatchFact -> Label -> LiveMatchFact
    fact f l = mapFindWithDefault mapEmpty l f
    facts :: Insn O C -> FactBase LiveMatchFact -> LiveMatchFact
    facts insn f = foldr (mapUnionWithKey (\_ -> S.union)) mapEmpty (map (fact f) (successors insn))

liveMatch :: FuelMonad m => BwdRewrite m Insn LiveMatchFact
liveMatch = deepBwdRw rw
  where
    remove :: FuelMonad m => m (Maybe (Graph Insn O O))
    remove = return (Just emptyGraph)
    replace :: FuelMonad m => [Insn O O] -> m (Maybe (Graph Insn O O))
    replace new = return (Just (mkMiddles new))

    rw :: FuelMonad m => Insn e x -> Fact x LiveMatchFact -> m (Maybe (Graph Insn e x))
    rw (SetM m (Match s re@RE{ reUsedTags = used' })) f
      | used@(Just _) <- mapLookup m f =
        if used /= used'
        --trace (show m ++ ": " ++ show used) $
          then replace [SetM m (Match s re{ reUsedTags = used })]
          else return Nothing
      | otherwise = remove
    rw _ _ = return Nothing

interesting (SetM _ _) = True
-- interesting (SetP _ _) = True
interesting (SetS _ (SSubstring _ _ _)) = True
interesting (If (IsMatch _) _ _) = True
interesting _ = False

enableTrace = False

addTracing
  | enableTrace = debugBwdTransfers trace show (\insn _ -> interesting insn)
  | otherwise = id

liveMatchPass :: FuelMonad m => BwdPass m Insn LiveMatchFact
liveMatchPass = addTracing $ BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveMatchTransfer
  , bp_rewrite = liveMatch }

canApplyLiveMatch program = not ("MatchLastRE" `isInfixOf` show program)
