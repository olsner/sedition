{-# LANGUAGE TupleSections #-}

module CharMap (
    CharMap(),
    -- construction
    empty, singleton, fromList,
    CharMap.null,
    -- access/update
    CharMap.lookup, findWithDefault, insert, delete,
    -- conversion/extraction
    elems, elemSet, toList, toRanges,
    CharMap.traverse,
    isComplete) where

import Data.List (sort)

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

-- Make this e.g. RangeMap k v, then add CharMap a = RangeMap Char a
-- That would allow adding a few metavalues besides char?
newtype CharMap a = CharMap (Map Char a) deriving (Show, Ord, Eq)

empty = CharMap (M.empty)
singleton k v = insert k v empty

null (CharMap m) = M.null m

elems (CharMap m) = M.elems m
elemSet (CharMap m) = S.fromList (M.elems m)

backward :: Ord a => CharMap a -> Map a [Char]
backward (CharMap m) = foldr multiMapInsert M.empty (M.toList m)

multiMapInsert :: Ord a => (Char, a) -> Map a [Char] -> Map a [Char]
multiMapInsert (k,v) = M.insertWith (<>) v [k]

lookup :: Char -> CharMap a -> Maybe a
lookup k (CharMap m) = M.lookup k m

findWithDefault :: a -> Char -> CharMap a -> a
findWithDefault def k (CharMap m) = M.findWithDefault def k m

toList :: Ord a => CharMap a -> [([Char], a)]
toList m = [(ks, v) | (v,ks) <- M.toList (backward m)]

toRanges :: Ord a => CharMap a -> [([(Char, Char)], a)]
toRanges = map (\(cs, a) -> (checkRanges cs (ranges cs), a)) . toList
  where
    -- Since cs comes from M.toList it should already be sorted!
    ranges :: [Char] -> [(Char,Char)]
    ranges cs | cs /= sort cs = error "double-check failed"
    ranges [] = []
    ranges (c:cs) = go c c cs
    go :: Char -> Char -> [Char] -> [(Char,Char)]
    go min max (c:cs) | c == succ max = go min c cs
    go min max cs = (min,max) : ranges cs

    checkRanges cs rs | cs == expandRanges rs = rs
                      | otherwise = error "expandRanges check failed"
    expandRanges [] = []
    expandRanges ((min,max):cs) = [min..max] ++ expandRanges cs

fromList = CharMap . M.fromList

insert :: Char -> a -> CharMap a -> CharMap a
insert k v (CharMap m) = CharMap (M.insert k v m)

delete k (CharMap m) = CharMap (M.delete k m)

-- Cheating here - Char has a large range but we'll work like Char8 here.
isComplete (CharMap m) = S.toList (M.keysSet m) == ['\0'..'\xff']

traverse :: (Ord a, Applicative f) => (a -> f b) -> CharMap a -> f (CharMap b)
traverse f cm = fromList . concat <$> Prelude.traverse f' (toList cm)
  where
    f' (ks,v) = (\v' -> (,v') <$> ks) <$> f v
