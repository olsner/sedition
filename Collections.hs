{-# LANGUAGE TypeFamilies,GeneralizedNewtypeDeriving,DeriveTraversable #-}

module Collections where

import Compiler.Hoopl as H hiding (joinMaps)

import qualified Data.IntSet as S
import qualified Data.IntMap as M
import Data.Foldable ()
import Data.Traversable ()

import IR (Pred(..), SVar(..))

newtype PredMap a = PM (M.IntMap a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance IsMap PredMap where
  type KeyOf PredMap = Pred

  mapNull (PM m) = M.null m
  mapSize (PM m) = M.size m
  mapMember (Pred k) (PM m) = M.member k m
  mapLookup (Pred k) (PM m) = M.lookup k m
  mapFindWithDefault def (Pred k) (PM m) = M.findWithDefault def k m

  mapEmpty = PM M.empty
  mapSingleton (Pred k) v = PM (M.singleton k v)
  mapInsert (Pred k) v (PM m) = PM (M.insert k v m)
  mapInsertWith f (Pred k) v (PM m) = PM (M.insertWith f k v m)
  mapDelete (Pred k) (PM m) = PM (M.delete k m)

  mapUnion (PM x) (PM y) = PM (M.union x y)
  mapUnionWithKey f (PM x) (PM y) = PM (M.unionWithKey (f . Pred) x y)
  mapDifference (PM x) (PM y) = PM (M.difference x y)
  mapIntersection (PM x) (PM y) = PM (M.intersection x y)
  mapIsSubmapOf (PM x) (PM y) = M.isSubmapOf x y

  mapMap f (PM m) = PM (M.map f m)
  mapMapWithKey f (PM m) = PM (M.mapWithKey (f . Pred) m)
  mapFold k z (PM m) = M.foldr k z m
  mapFoldWithKey k z (PM m) = M.foldrWithKey (k . Pred) z m
  mapFilter f (PM m) = PM (M.filter f m)

  mapElems (PM m) = M.elems m
  mapKeys (PM m) = map Pred (M.keys m)
  mapToList (PM m) = [(Pred k, v) | (k,v) <- M.toList m]
  mapFromList assocs = PM (M.fromList [(k, v) | (Pred k, v) <- assocs])
  mapFromListWith f assocs = PM (M.fromListWith f [(k, v) | (Pred k, v) <- assocs])

joinMaps :: IsMap m => JoinFun v -> JoinFun (m v)
joinMaps eltJoin l (OldFact old) (NewFact new) = mapFoldWithKey add (NoChange, old) new
  where
    add k new_v (ch, joinmap) =
      case mapLookup k joinmap of
        Nothing    -> (SomeChange, mapInsert k new_v joinmap)
        Just old_v -> case eltJoin l (OldFact old_v) (NewFact new_v) of
                        (SomeChange, v') -> (SomeChange, mapInsert k v' joinmap)
                        (NoChange,   _)  -> (ch, joinmap)

newtype SVarSet = SVS S.IntSet

instance IsSet SVarSet where
  type ElemOf SVarSet = SVar

  setNull (SVS s) = S.null s
  setSize (SVS s) = S.size s
  setMember (SVar k) (SVS s) = S.member k s

  setEmpty = SVS S.empty
  setSingleton (SVar k) = SVS (S.singleton k)
  setInsert (SVar k) (SVS s) = SVS (S.insert k s)
  setDelete (SVar k) (SVS s) = SVS (S.delete k s)

  setUnion (SVS x) (SVS y) = SVS (S.union x y)
  setDifference (SVS x) (SVS y) = SVS (S.difference x y)
  setIntersection (SVS x) (SVS y) = SVS (S.intersection x y)
  setIsSubsetOf (SVS x) (SVS y) = S.isSubsetOf x y

  setFold k z (SVS s) = S.foldr (k . SVar) z s

  setElems (SVS s) = map SVar (S.elems s)
  setFromList ks = SVS (S.fromList [k | SVar k <- ks])

newtype PredSet = PS S.IntSet

instance IsSet PredSet where
  type ElemOf PredSet = Pred

  setNull (PS s) = S.null s
  setSize (PS s) = S.size s
  setMember (Pred k) (PS s) = S.member k s

  setEmpty = PS S.empty
  setSingleton (Pred k) = PS (S.singleton k)
  setInsert (Pred k) (PS s) = PS (S.insert k s)
  setDelete (Pred k) (PS s) = PS (S.delete k s)

  setUnion (PS x) (PS y) = PS (S.union x y)
  setDifference (PS x) (PS y) = PS (S.difference x y)
  setIntersection (PS x) (PS y) = PS (S.intersection x y)
  setIsSubsetOf (PS x) (PS y) = S.isSubsetOf x y

  setFold k z (PS s) = S.foldr (k . Pred) z s

  setElems (PS s) = map Pred (S.elems s)
  setFromList ks = PS (S.fromList [k | Pred k <- ks])