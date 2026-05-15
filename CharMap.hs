module CharMap (
    CharMap(),
    -- construction
    empty, singleton, fromList, toList,
    CharMap.null,
    -- access/update
    CharMap.lookup, findWithDefault, insert, delete,
    -- conversion/extraction
    elems,
    elemSet,
    fromRanges, toRanges,
    CharMap.traverse, CharMap.map,
    isComplete, CharMap.const,
    union
    ) where

import Control.Arrow (first)

import Data.List (sort)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Word (Word8)

import RangeMap (RangeMap)
import qualified RangeMap as RM

newtype CharMap a = CM { cm :: RangeMap Word8 a } deriving (Eq, Ord)

instance (Ord a, Show a) => Show (CharMap a) where
  show cm = showRanges (sort (toSimpleRanges cm)) ""

showRanges :: (Ord a, Show a) => [((Char,Char),a)] -> ShowS
showRanges xs = showChar '{' . showCommasWith showAssoc xs . showChar '}'
    where
      showCommasWith _ [] = id
      showCommasWith f [x] = f x
      showCommasWith f (x:xs) = f x . showString ", " . showCommasWith f xs
      showAssoc ((k1,k2),v) | k1 == k2  = shows k1 . showString ": " . shows v
                            | otherwise = shows k1 . showString ".." . shows k2 . showString ": " . shows v

w8 :: Char -> Word8
w8 = toEnum . fromEnum

c :: Word8 -> Char
c = toEnum . fromEnum

c2 (x,y) = (c x, c y)
w2 (x,y) = (w8 x, w8 y)

lift f (CM c) = CM (f c)

empty = CM RM.empty
null (CM m) = RM.null m

singleton k v = CM (RM.singleton (w8 k) v)
fromList xs = CM (RM.fromList [(w8 k, v) | (k,v) <- xs])
toList :: Eq a => CharMap a -> [(Char, a)]
toList = Prelude.map (first c) . RM.toList . cm

lookup k = RM.lookup (w8 k) . cm
findWithDefault def k = RM.findWithDefault def (w8 k) . cm

insert k v = lift (RM.insert (w8 k) v)
delete k = lift (RM.delete (w8 k))

elems :: CharMap a -> [a]
elems = RM.elems . cm
elemSet :: Ord a => CharMap a -> Set a
elemSet = S.fromList . RM.elems . cm

toRanges :: Ord a => CharMap a -> [([(Char,Char)],a)]
toRanges (CM m) = [ (Prelude.map c2 ks, v) | (ks,v) <- RM.toRanges m ]

toSimpleRanges :: Ord a => CharMap a -> [((Char,Char),a)]
toSimpleRanges = concatMap (\(ks,v) -> [(k,v) | k <- ks]) . toRanges

fromRanges :: Ord a => [([(Char,Char)],a)] -> CharMap a
fromRanges xs = CM (RM.fromRanges [ (Prelude.map w2 ks, v) | (ks,v) <- xs ])

traverse :: (Eq b, Ord a, Applicative f) => (a -> f b) -> CharMap a -> f (CharMap b)
traverse f (CM c) = CM <$> RM.traverse f c

map :: (Eq b, Ord a) => (a -> b) -> CharMap a -> CharMap b
map f = lift (RM.map f)

isComplete :: (Ord a) => CharMap a -> Bool
isComplete (CM m) = RM.isComplete m

const :: a -> CharMap a
const = CM . RM.const

union :: (Ord a, Show a) => CharMap a -> CharMap a -> CharMap a
union (CM l) (CM r) = CM (RM.union l r)
