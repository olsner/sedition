{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances,FlexibleInstances,FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- TODO Rename this module and cursorOps, e.g. readoffsets? "cursor" doesn't
-- make sense.
module Regex.Cursor (cursorOps) where

import Compiler.Hoopl as H hiding (joinMaps, successors)

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

-- Calculate the offset in each state from either the starting state(s) or any
-- common preceding state. Quite inspired by a Hoopl forward pass.

type Offset = Int

cursorOps :: (Show s, Ord s) => Map s [s] -> [s] -> Map s Int
cursorOps successorMap startStates = resolve $ transferToFix 0 (fwdTransfer successorMap) (joinMaps joinFact) startMap (S.fromList startStates)
  where
    startMap = M.fromList [(s, 0) | s <- startStates]
    -- This falls back to 0 in case of conflicts, but there are actually some
    -- options we can choose fairly arbitrarily.
    -- To make it safe against out of bounds reads etc I think you can pick
    -- anything between 0 and the min of both branches.
    -- But if you have to move the cursor position you might as well move it
    -- all the way to zero out the offset?
    joinFact (OldFact x) (NewFact y) | x == y = (NoChange, x)
                                     | x > 0 = (SomeChange, 0)
                                     | otherwise = (NoChange, x)
    -- Saves some space I guess?
    resolve = id -- M.filter (> 0)

fwdTransfer :: Ord s => Map s [s] -> s -> Offset -> Map s Offset
fwdTransfer successors s f = M.fromList [(l, succ f) | l <- M.findWithDefault [] s successors]

type JoinFunc f = OldFact f -> NewFact f -> (ChangeFlag, f)
type JoinMapFunc k f = OldFact (Map k f) -> NewFact (Map k f) -> (Set k, Map k f)

joinMaps :: Ord k => JoinFunc f -> JoinMapFunc k f
joinMaps join (OldFact old) (NewFact new) = (changedSet, joinedMap)
  where
    -- M.union is left-biased
    joinedMap = M.map snd joinedFacts `M.union` addedFacts `M.union` old
    -- facts only in the new map are added as is
    addedFacts = M.difference new old
    changedSet = M.keysSet addedFacts `S.union` changedJoinedFacts
    joinedFacts = M.intersectionWith join (M.map OldFact old) (M.map NewFact new)
    changedJoinedFacts = M.keysSet (M.filter (\(c,_) -> c == SomeChange) joinedFacts)

transferToFix :: Ord s => f -> (s -> f -> Map s f) -> JoinMapFunc s f -> Map s f -> Set s -> Map s f
transferToFix bot transfer join facts todo = go facts todo (S.toList todo)
  where 
    go facts _       []           = facts
    go facts todoSet (first:rest) = go newFacts newTodoSet (rest ++ addTodo)
      where todoRest = S.delete first todoSet
            firstFact = M.findWithDefault bot first facts
            addFacts = transfer first firstFact
            (changed, newFacts) = join (OldFact facts) (NewFact addFacts)
            addTodo = S.toList (changed `S.difference` todoRest)
            newTodoSet = S.union todoRest changed

traceTransfer bot transfer join = transferToFix bot transfer' join'
  where
    transfer' s f | fb <- transfer s f = trace (show s ++ ": " ++ show f ++ " -> " ++ show fb) fb
    join' (OldFact old) (NewFact new) | joined <- join (OldFact old) (NewFact new) = trace ("join: " ++ show old ++ " <> " ++ show new ++ " -> " ++ show joined) joined
