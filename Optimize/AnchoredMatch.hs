{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts, RecordWildCards, OverloadedStrings #-}

-- anchoredMatchPass: Find and apply optimizations based on anchored regular
-- expressions.
--
-- Anchored at start:
-- * SIMatchStart = SIStart -> leads to possibly removing tags
-- * NextMatch will never match
--
-- Wild-card beginning (.*foo) will always match at the start of the string,
-- but can be repeated. So we could do something with the first match and
-- maybe if there's no repeated match that would remove the initial tag?
--
-- Anchored at end:
-- * SIMatchEnd = SIEnd -> possibly removing tags
--   end of match is generally always known since that's where we terminated
--   matching? But it could be useful to know that we don't even need to track
--   that, e.g. that we don't need to know what part matches. Opens up more
--   optimizations for ending matching early.
-- * NextMatch will never match (the first match could only match if it matched
--   up until the end of string).

module Optimize.AnchoredMatch (anchoredMatchPass) where

import Compiler.Hoopl as H hiding (joinMaps)

import Debug.Trace

import Collections
import IR
import qualified Regex.Regex as Regex

data AnchoredFact = A {
    anchoredAtStart :: Bool,
    anchoredAtEnd :: Bool,
    matchImpossible :: Bool }
  deriving (Eq)
unanchored = A False False False
nextMatchFact a@A{..} = a {
  -- Any "next match" is not going to match at the beginning, OTOH it won't
  -- match at all? But this prevents rewriting substring expressions which would
  -- be confusing and look very wrong to do after a NextMatch.
  anchoredAtStart = False,
  matchImpossible = anchoredAtStart || anchoredAtEnd }

instance Show AnchoredFact where
  show (A _ _ True) = "<no-match>"
  show (A True True _) = "^$"
  show (A True False _) = "^"
  show (A False True _) = "$"
  show (A False False _) = "?"

reFact :: RE -> AnchoredFact
reFact RE{..} = A (Regex.anchoredAtStart re) (Regex.anchoredAtEnd re) (not (Regex.canMatch re))
  where
    re = Regex.parseString reERE reString

type AnchoredMatchFact = MVarMap AnchoredFact
anchoredLattice :: DataflowLattice AnchoredMatchFact
anchoredLattice = DataflowLattice
 { fact_name = "Anchored match"
 , fact_bot  = mapEmpty
 , fact_join = joinMaps add }
 where
    add _ (OldFact old) (NewFact new) = (ch, j)
      where
        -- Shouldn't be possible as facts are constant here?
        j = new { matchImpossible = matchImpossible new && matchImpossible old }
        ch = changeIf (old /= new)

copyFact f src dst fb
  | src /= dst, Just fact <- mapLookup src fb = mapInsert dst (f fact) fb
  | otherwise = fb

transferM :: MVar -> MatchExpr -> AnchoredMatchFact -> AnchoredMatchFact
transferM t (Match _ re) = mapInsert t (reFact re)
transferM t (MatchLastRE _) = mapInsert t unanchored
transferM t (NextMatch m _) = copyFact nextMatchFact m t
transferM t (MVarRef s) = copyFact id s t

anchoredMatchTransfer :: FwdTransfer Insn AnchoredMatchFact
anchoredMatchTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> AnchoredMatchFact -> AnchoredMatchFact
    first (Label _)  f = f
    middle :: Insn O O -> AnchoredMatchFact -> AnchoredMatchFact
    middle (SetM m expr) = transferM m expr
    middle _ = id
    last :: Insn O C -> AnchoredMatchFact -> FactBase AnchoredMatchFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase anchoredLattice [(l, f) | l <- ls]

anchoredMatch :: FuelMonad m => FwdRewrite m Insn AnchoredMatchFact
anchoredMatch = deepFwdRw rw
  where
    remove _old = {-trace ("Removed: " ++ show _old) $-} return (Just emptyGraph)
    replace :: FuelMonad m => Insn O O -> [Insn O O] -> m (Maybe (Graph Insn O O))
    replace _old new = {-trace (show _old ++ " -> " ++ show new) $-} return (Just (mkMiddles new))
    rwLast :: FuelMonad m => Insn O C -> Insn O C -> m (Maybe (Graph Insn O C))
    rwLast _old new = {-trace (show _old ++ " -> " ++ show new) $-} return (Just (mkLast new))

    rw :: FuelMonad m => Insn e x -> AnchoredMatchFact -> m (Maybe (Graph Insn e x))
    rw i@(SetS d e)           f | Just e' <- rwE e f    = replace i [SetS d e']
    rw i@(SetS d (SVarRef s)) _ | s == d                = remove i
    rw i@(If (IsMatch m) _ l) f | isMatchImpossible m f = rwLast i (Branch l)
    rw _                      _                         = return Nothing

rwE (SSubstring s i j) f | Just i' <- rwIx i f   = Just (SSubstring s i' j)
                         | Just j' <- rwIx j f   = Just (SSubstring s i j')
                         | i == j                = Just (SConst "")
rwE (SAppend [])       _                         = Just (SConst "")
rwE (SAppend [x])      _                         = Just x
rwE (SAppend xs)       f | Just xs' <- rwEs xs f = Just (SAppend xs')
rwE _                  _                         = Nothing

-- In normal order, rewrite one thing at a time to make it behave well with
-- optimization fuel. Not the most efficient with repeated rewrites though?
rwEs (SConst "":xs) _                 = Just xs
rwEs (SConst s1:SConst s2:xs) _       = Just (SConst (s1 <> s2) : xs)
rwEs (SSubstring s1 i1 j1:SSubstring s2 i2 j2:xs) _
              | s1 == s2, j1 == i2    = Just (merged:xs)
              where merged = SSubstring s1 i1 j2
rwEs (x:xs) f | Just x'  <- rwE x f   = Just (x' : xs)
              | Just xs' <- rwEs xs f = Just (x : xs')
rwEs _      _                         = Nothing

rwIx (SIMatchStart m) f | isAnchoredAtStart m f = Just SIStart
rwIx (SIMatchEnd m)   f | isAnchoredAtEnd m f   = Just SIEnd
rwIx _                _                         = Nothing

isAnchoredAtStart m f = anchoredAtStart (mapFindWithDefault unanchored m f)
isAnchoredAtEnd m f = anchoredAtEnd (mapFindWithDefault unanchored m f)
isMatchImpossible m f = matchImpossible (mapFindWithDefault unanchored m f)

interesting (SetM _ _) = True
interesting _ = False

enableTrace = False

addTracing
  | enableTrace = debugFwdTransfers trace show (\insn _ -> interesting insn)
  | otherwise = id

anchoredMatchPass :: FuelMonad m => FwdPass m Insn AnchoredMatchFact
anchoredMatchPass = addTracing $ FwdPass
  { fp_lattice = anchoredLattice
  , fp_transfer = anchoredMatchTransfer
  , fp_rewrite = anchoredMatch }
