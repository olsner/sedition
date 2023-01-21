module CharMap (CharMap(), CharMap.lookup, insert, delete, toList, fromList) where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

newtype CharMap a = CharMap (Map Char a) deriving (Show, Ord, Eq)

backward :: Ord a => CharMap a -> Map a (Set Char)
backward (CharMap m) = foldr multiMapInsert M.empty (M.toList m)

multiMapInsert :: Ord a => (Char, a) -> Map a (Set Char) -> Map a (Set Char)
multiMapInsert (k,v) = M.insertWith S.union v (S.singleton k)

lookup :: Char -> CharMap a -> Maybe a
lookup k (CharMap m) = M.lookup k m

toList :: Ord a => CharMap a -> [(Set Char, a)]
toList m = [(ks, v) | (v,ks) <- M.toList (backward m)]

fromList = CharMap . M.fromList

insert :: Char -> a -> CharMap a -> CharMap a
insert k v (CharMap m) = CharMap (M.insert k v m)

delete k (CharMap m) = CharMap (M.delete k m)
