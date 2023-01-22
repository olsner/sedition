module CharMap (
    CharMap(),
    -- construction
    empty, singleton, fromList,
    -- access/update
    CharMap.lookup, insert, delete,
    -- conversion/extraction
    elems, toList, toRanges) where

import Data.List (sort)

import Data.Map (Map)
import qualified Data.Map as M

newtype CharMap a = CharMap (Map Char a) deriving (Show, Ord, Eq)

empty = CharMap (M.empty)
singleton k v = insert k v empty

elems (CharMap m) = M.elems m

backward :: Ord a => CharMap a -> Map a [Char]
backward (CharMap m) = foldr multiMapInsert M.empty (M.toList m)

multiMapInsert :: Ord a => (Char, a) -> Map a [Char] -> Map a [Char]
multiMapInsert (k,v) = M.insertWith (<>) v [k]

lookup :: Char -> CharMap a -> Maybe a
lookup k (CharMap m) = M.lookup k m

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
