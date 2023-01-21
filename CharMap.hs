module CharMap (
    CharMap(),
    empty, singleton, elems,
    CharMap.lookup, insert, delete,
    toList, fromList) where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

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

fromList = CharMap . M.fromList

insert :: Char -> a -> CharMap a -> CharMap a
insert k v (CharMap m) = CharMap (M.insert k v m)

delete k (CharMap m) = CharMap (M.delete k m)
