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

import Data.Set (Set)
import qualified Data.Set as S
import Data.Word (Word8)

import RangeMap (RangeMap)
import qualified RangeMap as RM

type CharMap a = RangeMap Word8 a

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
