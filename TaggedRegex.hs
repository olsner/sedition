-- Convert parsed regexes with groups (all groups are numbered/capturing) into
-- regexes with explicit tag numbers. Tag 0 and 1 are the start/end of the
-- whole match.

module TaggedRegex where

import Control.Monad.Trans.State.Strict

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import Regex (Regex)
import qualified Regex

type TagId = Int
type Prio = Int

data Tag = NoTag | UnTag TagId | Tag TagId deriving (Show, Ord, Eq)

-- Convenient for the TNFA conversion, but the Eps transition is not used here.
-- Wouldn't be too much work to translate in TNFA and have distinct types...
data TNFATrans
  = BOL
  | Any
  | EOL
  | Symbol Char
  | CClass [Char]
  | CNotClass [Char]
  | Eps Prio Tag
  deriving (Show, Ord, Eq)

data TaggedRegex
  = Empty
  | Term TNFATrans
  | TagTerm TagId
  | Cat TaggedRegex TaggedRegex
  | Or TaggedRegex TaggedRegex
  | Repeat Int (Maybe Int) TaggedRegex
  deriving (Show, Ord, Eq)

cat Empty x = x
cat x Empty = x
cat (Cat x y) z = cat x (cat y z)
cat x y = Cat x y

-- Could optimize or regularize more stuff here, but regrouping and reordering
-- does affect the priority of alternative parses so it might not be completely
-- safe to do that. Better done as part of determinization?
or_ Empty Empty = Empty
or_ x y = Or x y

cat3 x y z = cat x (cat y z)

tagRegex :: Regex -> TaggedRegex
tagRegex re = evalState (go (Regex.Group re)) 0
  where
    go Regex.Empty = return Empty
    go Regex.Any = return (Term Any)
    go (Regex.Char c) = return (Term (Symbol c))
    go (Regex.CClass cs) = return (Term (CClass cs))
    go (Regex.CNotClass cs) = return (Term (CNotClass cs))
    go Regex.AnchorStart = return (Term BOL)
    go Regex.AnchorEnd = return (Term EOL)
    go (Regex.Concat xs) = foldr1 cat <$> mapM go xs
    go (Regex.Or xs) = foldr1 or_ <$> mapM go xs
    go (Regex.Group x) = do
      tStart <- tag
      tEnd <- tag
      tre <- go x
      return (cat3 tStart tre tEnd)
    go (Regex.Repeat n m x) = Repeat n m <$> go x
    -- Could still be supported in TaggedRegex though!
    go (Regex.BackRef _) = error "Back-references not supported in TDFA"

    tag = gets TagTerm <* modify succ

testTagRegex :: String -> (TaggedRegex, FixedTagMap)
testTagRegex = fixTags . tagRegex . Regex.parseString True . C.pack

-- Based on usgae information, eliminate some of the tags in a regex.
selectTags :: (TagId -> Bool) -> TaggedRegex -> TaggedRegex
selectTags used = go
  where
    go re@(TagTerm tag) | used tag  = re
                        | otherwise = Empty
    go (Or x y) = or_ (go x) (go y)
    go (Cat x y) = cat (go x) (go y)
    go (Repeat n m x) = Repeat n m (go x)
    go re = re

data FixedTag = FixedTag TagId Int deriving (Show, Ord, Eq)

type FixedTagMap = Map TagId FixedTag

type FixTagM a = State FixedTagMap a

fixedTags :: TagId -> Maybe Int -> Maybe Int -> TaggedRegex -> FixTagM (TagId, Maybe Int, Maybe Int)
fixedTags t d k = go
  where
    go Empty = return (t, d, k)
    -- TODO Optimize: if BOL matches, we know the distance is 0 from the start
    go (Term BOL) = return (t, d, k)
    go (Term EOL) = return (t, d, k)
    go (Term _) = return (t, succ <$> d, succ <$> k)
    go (Or x y) = do
      (_,_,k1) <- fixedTags (-1) Nothing (Just 0) x
      (_,_,k2) <- fixedTags (-1) Nothing (Just 0) y
      if eqJust k1 k2
        then return (t, (+) <$> k1 <*> d, (+) <$> k1 <*> d)
        else return (t, Nothing, Nothing)
    go (Cat x y) = do
      (t2, d2, k2) <- fixedTags t d k y
      fixedTags t2 d2 k2 x
    go (Repeat n m x) = do
      (_, _, k1) <- fixedTags (-1) Nothing (Just 0) x
      let addOffset x = (+) <$> ((* n) <$> k1) <*> x
      if Just n == m
        then return (t, addOffset d, addOffset k)
        else return (t, Nothing, Nothing)
    go (TagTerm tag) =
      if t /= -1 && isJust d
        then modify (M.insert tag (FixedTag t (fromJust d))) >>
             return (t, d, k)
        else return (tag, Just 0, k)

    eqJust (Just x) (Just y) = x == y
    eqJust _ _ = False


-- Remove tags that can be calculated from other tags, and produce a map of how
-- to calculate them. Run after removing otherwise unused tags to avoid having
-- to think about dependencies from used fixed tags on otherwise unused tags.
fixTags :: TaggedRegex -> (TaggedRegex, FixedTagMap)
fixTags re = (removeFixedTags m re, m)
    where
      -- TODO There should be a special fixed tag denoting the end of match,
      -- since that is always known when matching and can eliminate some tags.
      m = execState (fixedTags (-1) (Just 0) (Just 0) re) M.empty

-- After calculating fixed tags, remove the tag terms from the regex so the
-- rest of the engine doesn't need to consider them.
removeFixedTags :: FixedTagMap -> TaggedRegex -> TaggedRegex
removeFixedTags m = selectTags (\t -> not (M.member t m))
