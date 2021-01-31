{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts, LambdaCase #-}

-- sameStringPass: Find cases where a string variable is set to the same other
-- variable on every incoming branch. Should rewrite many uses of
-- S{pattern-space} when we know statically which pattern-space value is being
-- referred to.

module SameString (sameStringPass) where

import Compiler.Hoopl as H hiding ((<*>))

import Data.Map (Map)
import qualified Data.Map as M
--import Debug.Trace

import IR

type SameStringFact = Map SVar (WithTop SVar)
constLattice :: DataflowLattice SameStringFact
constLattice = DataflowLattice
 { fact_name = "Same string"
 , fact_bot  = M.empty
 , fact_join = joinMaps (extendJoinDomain constFactAdd) }
 where
   constFactAdd _ (OldFact old) (NewFact new)
       = if new == old then (NoChange, PElem new)
         else               (SomeChange, Top)

cleanup var to = M.mapMaybe $ \case
    PElem s | s == var -> Nothing
    f -> Just f

forward s to = M.insert s to . cleanup s to

sameStringTransfer :: FwdTransfer Insn SameStringFact
sameStringTransfer = mkFTransfer3 first middle last
  where
    first :: Insn C O -> SameStringFact -> SameStringFact
    -- C O
    first (Label _)  f = f

    -- O O
    middle :: Insn O O -> SameStringFact -> SameStringFact
    -- When changing s, we also need to invalidate other references to s in the
    -- *values* of the fact base. That's annoying.
    -- Let's have a think about what it means to find "(s, PElem t)" in the
    -- map... It should mean that any subsequent reference to s can be safely
    -- replaced with a reference to t. Why do we do this?
    -- * remove S{pattern} and S{hold} with specific variables/values where
    --   possible. Not always possible where two divergent executions merge.
    --   this is supposed to expose future optimizations based on the values of
    --   strings.
    -- * remove subsequently dead assignments
    -- * avoid work done by those assignments
    -- When is that no longer safe?
    -- * t is modified after copying (e.g. tmp <- pattern, modify pattern, foo <- tmp)
    -- * would it work to just M.insert s2 Top?
    middle (SetS s (SVarRef s2)) = forward s (PElem s2)
    middle (SetS s _)            = forward s Top
    middle (GetMessage s)        = forward s Top
    middle (Read s _)            = forward s Top

    middle _insn = \f -> {-trace ("Unhandled instruction " ++ show insn)-} f

    -- Exchange (original behavior):
    -- (Let O{2,3,{pattern}{hold}} denote the original values of all variables)
    --
    -- S2 <- S{pattern}
    --   S2: PElem S{pattern}
    -- S3 <- S{hold}
    --   S2: PElem S{pattern}
    --   S3: PElem S{hold}
    -- S{pattern} <- S3
    --   S2: PElem S{pattern}
    --   S3: PElem S{hold}
    --   S{pattern}: PElem S3
    -- S{hold} <- S2
    --   S2: PElem S{pattern}
    --   S3: PElem S{hold}
    --   S{pattern}: PElem S3
    --   S{hold}: PElem S2
    -- [some instruction reading from S{pattern}, S{hold}, S2 or S3]
    --
    -- What's actually rewritable according to original rules:
    -- S2 -> S{pattern} [wrong!]
    -- S3 -> S{hold} [wrong!]
    -- S{pattern} -> S3 [correct]
    --         *and* S3 -> S{hold} [wrong!]
    -- S{hold} -> S2 [correct]
    --      *and* S2 -> S{pattern} [wrong!]
    -- The latter two could also result in a rewriting loop, from S{pattern} to
    -- S3, S{hold}, S2 and then back to S{pattern}...
    --
    -- What should be permissible to rewrite afterwards?
    -- S{pattern} -> S3
    -- S{hold} -> S2
    -- S2 -> O{pattern} (if remembered, otherwise no rewrite)
    -- S3 -> O{hold} (if remembered)

    -- Exchange (delete s2 . insert s):
    -- (Let O{2,3,{pattern}{hold}} denote the original values of all variables)
    --
    -- S2 <- S{pattern}
    --   S2: PElem S{pattern}
    -- S3 <- S{hold}
    --   S2: PElem S{pattern}
    --   S3: PElem S{hold}
    -- S{pattern} <- S3
    --   S2: PElem S{pattern}
    --   S{pattern}: PElem S3
    -- S{hold} <- S2
    --   S{pattern}: PElem S3
    --   S{hold}: PElem S2
    -- [some instruction reading from S{pattern}, S{hold}, S2 or S3]
    --
    -- What is permissible to rewrite afterwards?
    -- S{pattern} -> S3
    -- S{hold} -> S2
    --
    -- Kind of looks correct, hm.

    -- O C
    last :: Insn O C -> SameStringFact -> FactBase SameStringFact
    last insn f = boringFactBase f (successors insn)

    boringFactBase f ls = mkFactBase constLattice [(l, f) | l <- ls]

sameString :: FuelMonad m => FwdRewrite m Insn SameStringFact
sameString = deepFwdRw rw
  where
    -- Operations that read from a string variable can be rewritten to use the
    -- incoming variable instead, if that is constant.
    -- TODO Annoying duplication of return/Just/mkMiddle and pattern matching
    -- on the helpers. And where is fuel consumed? Perhaps every variable
    -- replaced should consume its own fuel so that we can bisect with enough
    -- detail.
    rw :: FuelMonad m => Insn e x -> SameStringFact -> m (Maybe (Graph Insn e x))
    rw (SetS s expr) f | Just expr' <- rwE expr f = return (Just (mkMiddle (SetS s expr')))
    rw (SetP p cond) f | Just cond' <- rwC cond f = return (Just (mkMiddle (SetP p cond')))
    rw (Print fd s) f | Just s' <- var s f = return (Just (mkMiddle (Print fd s')))
    -- rw (Message s) =
    -- rw (PrintLiteral _ _ s) =
    -- rw (ShellExec s) =
    -- rw (WriteFile _ s) =
    rw _ _ = return Nothing

    rwE (SVarRef s)        f = SVarRef <$> var s f
    rwE (SAppendNL s1 s2)  f = SAppendNL <$> var s1 f <*> var s2 f
    rwE (SSubst s r a)     f = SSubst <$> var s f <*> pure r <*> pure a
    rwE (STrans from to s) f = STrans from to <$> var s f
    rwE _                  _ = Nothing

    rwC (Match s re)       f = Match <$> var s f <*> pure re
    rwC (MatchLastRE s)    f = MatchLastRE <$> var s f
    rwC _                  _ = Nothing

    var s f | Just (PElem t) <- M.lookup s f = Just t
            | otherwise                      = Nothing


sameStringPass :: FuelMonad m => FwdPass m Insn SameStringFact
sameStringPass = FwdPass
  { fp_lattice = constLattice
  , fp_transfer = sameStringTransfer
  , fp_rewrite = sameString }

