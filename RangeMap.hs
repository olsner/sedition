{-# LANGUAGE TupleSections #-}

module RangeMap (
    RangeMap(),
    -- construction
    empty, singleton, fromList,
    RangeMap.null,
    -- access/update
    RangeMap.lookup, findWithDefault, insert, delete,
    -- conversion/extraction
    elems, elemSet, toList, toRanges, fromRanges,
    RangeMap.traverse, RangeMap.map,
    isComplete, RangeMap.const,
    union
    ) where

import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

-- Consecutive entries (k1, v1) and (k2, v2) mean that k1 <= k < k2 all have
-- value v1. A final entry (k1, v) means that all k >= k1 have value v.
-- Consecutive entries with the same value can always be removed.
--
-- One niggle: an entry like (minBound, Nothing) is possible but equivalent to
-- an empty map, and the derived Eq, Ord instances won't be correct. Can any
-- sequence of operations produce that?
--
-- TODO Use IntMap instead of Map?
newtype RangeMap k v = RangeMap (Map k (Maybe v)) deriving (Show, Ord, Eq)

empty = RangeMap M.empty
singleton k v = insert k v empty

null (RangeMap m) = M.null m

elems (RangeMap m) = catMaybes (M.elems m)
elemSet m = S.fromList (elems m)

lookup :: Ord k => k -> RangeMap k a -> Maybe a
lookup k (RangeMap m) | Just (_,v) <- M.lookupLE k m = v
                      | otherwise = Nothing

findWithDefault :: (Bounded k, Enum k, Ord k) => a -> k -> RangeMap k a -> a
findWithDefault def k = fromMaybe def . RangeMap.lookup k

toList :: (Bounded k, Enum k, Ord k, Ord v) => RangeMap k v -> [(k, v)]
toList m = [(k, v) | (k1,k2,v) <- toRanges' m, k <- [k1..k2]]

toRanges :: (Bounded k, Enum k, Ord k, Ord v) => RangeMap k v -> [([(k, k)], v)]
toRanges m = uniqRanges (toRanges' m)

toRanges' :: (Bounded k, Enum k, Ord k, Ord v) => RangeMap k v -> [(k, k, v)]
toRanges' (RangeMap m) = go0 (M.toList m)
  where
    -- go0: last entry seen was Nothing, or start of list (i.e. iterating range
    -- that is not present in map)
    go0 [] = []
    go0 ((_, Nothing):xs) = trace "should be impossible?" $ go0 xs
    go0 ((k, Just v):xs) = go1 k v xs
    -- go1: last entry had a value, so we're iterating a range that has a value.
    go1 k1 v [] = [(k1, maxBound, v)]
    go1 k1 v ((k2, w):xs) = (k1, pred k2, v) : case w of
      Nothing -> go0 xs
      Just v2 | v == v2 -> error "Consecutive keys with same value"
      Just v2 -> go1 k2 v2 xs

uniqRanges :: Ord v => [(k, k, v)] -> [([(k, k)], v)]
uniqRanges = Prelude.map (\(v,ks) -> (ks,v)) . M.toList . M.unionsWith (<>) .
  Prelude.map (\(k1,k2,v) -> M.singleton v [(k1,k2)])

fromRanges' :: (Bounded k, Enum k, Ord k, Eq v) => [(k, k, v)] -> RangeMap k v
fromRanges' xs = foldl f empty xs
  where f r (k1,k2,v) | k2 == maxBound = r'
                      | otherwise = insert' k2' (RangeMap.lookup k2' r) r'
                      where r' = insert' k1 (Just v) r
                            k2' = succ k2

fromRanges :: (Bounded k, Enum k, Ord k, Eq v) => [([(k, k)], v)] -> RangeMap k v
fromRanges = fromRanges' . concatMap f'
  where
    f' (ks, v) = Prelude.map (\(k1,k2) -> (k1,k2,v)) ks

fromList :: (Bounded k, Enum k, Eq k, Ord k, Eq v) => [(k,v)] -> RangeMap k v
fromList = foldr (uncurry insert) empty

-- Insert (k,v) and (k+1,value[k+1]). If the next entry in the map is (k2,v2)
-- this first sets [k..k2-1] to v then restores [k+1..k2-1] to v1 where v1 may
-- be Nothing.
insert :: (Bounded k, Ord k, Enum k, Eq v) => k -> v -> RangeMap k v -> RangeMap k v
insert k v r | k == maxBound = r'
             | otherwise     = insert' k' (RangeMap.lookup k' r) r'
             where r' = insert' k (Just v) r
                   k' = succ k

-- "half" insert: Set [k..] to v but avoid adding duplicate values if the
-- current value is already v at (or before) k.
insert' :: (Ord k, Eq v) => k -> Maybe v -> RangeMap k v -> RangeMap k v
insert' k v r@(RangeMap m) = case M.lookupLT k m of
  -- Don't look directly at k (since that will be replaced), but what's before
  -- it. If it's the same, delete k if present.
  Just (_,v1) | v1 == v      -> RangeMap (M.delete k m)
  -- k is before (or at) the first entry in the map and we're deleting.
  Nothing     | Nothing <- v -> RangeMap (M.delete k m)
  -- Otherwise, look at what's after k. If it's the same, delete it and add k.
  _ -> case M.lookupGT k m of
    Just (k2,v1) | v1 == v -> RangeMap (M.insert k v (M.delete k2 m))
    _ -> RangeMap (M.insert k v m)

delete k = insert' k Nothing

isComplete (RangeMap m) = M.member minBound m && not (Nothing `elem` M.elems m)

traverse :: (Bounded k, Enum k, Ord k, Eq b, Ord a, Applicative f) => (a -> f b) -> RangeMap k a -> f (RangeMap k b)
traverse f r = fromRanges <$> Prelude.traverse f' (toRanges r)
  where
    f' (ks, v) = (ks,) <$> f v

map :: (Bounded k, Enum k, Ord k, Eq b, Ord a) => (a -> b) -> RangeMap k a -> RangeMap k b
map f = fromRanges . Prelude.map f' . toRanges
  where
    f' (ks, v) = (ks, f v)

const :: Bounded k => v -> RangeMap k v
const def = RangeMap (M.singleton minBound (Just def))

union m n = fromRanges' (go minBound (toRanges' m) (toRanges' n))
  where
    go _ [] [] = []
    go _ [] ys = ys
    go _ xs [] = xs
    go k (x@(k1,k2,_):xs) (y@(l1,l2,w):ys)
      -- left range is first, add it and continue until there's an overlap
      | k2 < l1 = trace_ "case1" (x : go k2 xs (y:ys))
      -- right range is first, so we must be in a hole in left map that we
      -- should fill.
      | l2 < k1 = trace_ "case2" (y : go l2 (x:xs) ys)
      -- right range is entirely contained in the left one, discard it.
      -- keep x since it may also overlap the next range
      | k1 <= l1 && l2 <= k2 = trace_ "case3" (go k (x:xs) ys)
      -- Knowledge from previous tests failing: l1 <= k2, k1 <= l2, k2 < l2
      -- left range is first, take the whole left range first and continue with
      -- the tail of the right range. The tail is not empty since we check for
      -- containment above.
      | k1 <= l1 = trace_ "case4" (x : if k2 == maxBound then [] else go k2 xs ((succ k2,l2,w):ys))
      -- right range is first, take the first part of the right range then
      -- continue with the left range and the tail of the right range.
      | k1 < l2 && l1 < k1 = trace_ "case5" ((l1, pred k1, w) : go k1 (x:xs) ((k1,l2,w):ys))
      | otherwise = error ("Unhandled case: " ++ show x ++ " <> " ++ show y)
      where trace_ s = id -- trace (unwords [s, show k, show x, show y])
