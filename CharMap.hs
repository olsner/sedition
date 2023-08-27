{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}

module CharMap (
    CharMap(),
    -- construction
    empty, singleton, fromList,
    CharMap.null,
    -- access/update
    CharMap.lookup, findWithDefault, insert, delete,
    -- conversion/extraction
    elems,
    elemSet,
    fromRanges,
    toRanges,
    CharMap.traverse, CharMap.map,
    isComplete, CharMap.const,
    union
    ) where

import Data.List (sort)

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Word (Word8)

import RangeMap (RangeMap)
import qualified RangeMap as RM

#if 0

-- Make this e.g. RangeMap k v, then add CharMap a = RangeMap Char a
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

allChars = ['\0'..'\xff']

-- Cheating here - Char has a large range but we'll work like Char8 here.
isComplete (CharMap m) = S.toList (M.keysSet m) == allChars

traverse :: (Ord a, Applicative f) => (a -> f b) -> CharMap a -> f (CharMap b)
traverse f cm = fromList . concat <$> Prelude.traverse f' (toList cm)
  where
    f' (ks,v) = (\v' -> (,v') <$> ks) <$> f v

const def = fromList [(k, def) | k <- allChars]

union (CharMap m) (CharMap n) = CharMap (M.union m n)

#else

type CharMap a = RangeMap Word8 a -- deriving (Show, Ord, Eq)

w8 :: Char -> Word8
w8 = toEnum . fromEnum

c :: Word8 -> Char
c = toEnum . fromEnum

c2 (x,y) = (c x, c y)
w2 (x,y) = (w8 x, w8 y)

empty = RM.empty
null = RM.null

singleton k = RM.singleton (w8 k)
fromList xs = RM.fromList [(w8 k, v) | (k,v) <- xs]

lookup k = RM.lookup (w8 k)
findWithDefault def k = RM.findWithDefault def (w8 k)

insert k = RM.insert (w8 k)
delete k = RM.delete (w8 k)

elems :: CharMap a -> [a]
elems = RM.elems
elemSet :: Ord a => CharMap a -> Set a
elemSet = S.fromList . RM.elems

toRanges :: Ord a => CharMap a -> [([(Char,Char)],a)]
toRanges m = [ (Prelude.map c2 ks, v) | (ks,v) <- RM.toRanges m ]

fromRanges :: Ord a => [([(Char,Char)],a)] -> CharMap a
fromRanges xs = RM.fromRanges [ (Prelude.map w2 ks, v) | (ks,v) <- xs ]

traverse :: (Eq b, Ord a, Applicative f) => (a -> f b) -> CharMap a -> f (CharMap b)
traverse = RM.traverse

map :: (Eq b, Ord a) => (a -> b) -> CharMap a -> CharMap b
map = RM.map

isComplete :: (Ord a) => CharMap a -> Bool
isComplete = RM.isComplete

const :: a -> CharMap a
const = RM.const

union :: (Ord a, Show a) => CharMap a -> CharMap a -> CharMap a
union = RM.union

#endif
