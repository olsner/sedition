-- Convert parsed regexes with groups (all groups are numbered/capturing) into
-- regexes with explicit tag numbers. Tag 0 and 1 are the start/end of the
-- whole match.

module TaggedRegex where

import Control.Monad.Trans.State.Strict

-- import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Maybe
-- import Data.Set (Set)
-- import qualified Data.Set as S

-- import Debug.Trace

import Regex (Regex)
import qualified Regex

newtype Prio = P Int deriving (Show, Ord, Eq)

newtype TagId = T Int deriving (Ord, Eq)
instance Show TagId where
  show (T x) = 't' : show x
data Tag = NoTag | UnTag TagId | Tag TagId deriving (Ord, Eq)
instance Show Tag where
  show NoTag = "e"
  show (Tag (T x)) = 't' : show x
  show (UnTag (T x)) = '-' : 't' : show x

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
  deriving (Ord, Eq)

instance Show TaggedRegex where
  show Empty = "()"
  show (Term BOL) = "^"
  show (Term Any) = "."
  show (Term EOL) = "$"
  show (Term (Symbol c)) = show c
  show (Term t) = "(" ++ show t ++ ")"
  show (TagTerm t) = show t
  show (Cat x y) = concatMap show $ catList (Cat x y)
  show (Or x y) = "(" ++ (intercalate " | " . map show $ orList (Or x y)) ++ ")"
  show (Repeat n m x) = "(" ++ show x ++ ")" ++ showRep n m

showRep :: Int -> Maybe Int -> String
showRep 0 Nothing = "*"
showRep 0 (Just 1) = "?"
showRep 1 Nothing = "+"
showRep n Nothing = "{" ++ show n ++ ",}"
showRep n (Just m) | m == n    = "{" ++ show n ++ "}"
                   | otherwise = "{" ++ show n ++ "," ++ show m ++ "}"

catList :: TaggedRegex -> [TaggedRegex]
catList Empty = []
catList (Cat Empty y) = catList y
catList (Cat x y) = x : catList y
catList x = [x]

orList :: TaggedRegex -> [TaggedRegex]
orList Empty = []
orList (Or Empty y) = orList y
orList (Or x y) = x : orList y
orList x = [x]

cat :: TaggedRegex -> TaggedRegex -> TaggedRegex
cat Empty x = x
cat x Empty = x
cat (Cat x y) z = cat x (cat y z)
cat x y = Cat x y

-- Could optimize or regularize more stuff here, but regrouping and reordering
-- does affect the priority of alternative parses so it might not be completely
-- safe to do that. Better done as part of determinization?
or_ :: TaggedRegex -> TaggedRegex -> TaggedRegex
or_ Empty Empty = Empty
or_ x y = Or x y

cat3 :: TaggedRegex -> TaggedRegex -> TaggedRegex -> TaggedRegex
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

    tag = gets (TagTerm . T) <* modify succ

testParseTagRegex :: String -> TaggedRegex
testParseTagRegex = tagRegex . Regex.parseString True . C.pack
testTagRegex :: String -> (TaggedRegex, FixedTagMap)
testTagRegex = fixTags . testParseTagRegex

testTagRegexFind :: String -> (TaggedRegex, FixedTagMap)
testTagRegexFind = fixTags . adjustForFind . testParseTagRegex

-- Note that this should/must be run before fixing tags, otherwise you'll have
-- tags incorrectly fixed to end-of-match that should go before the tail. The
-- tail is "wrong" too, it should be handled in the TDFA stage.
adjustForFind re = cat3 anyStar re anyStar
  where anyStar = Repeat 0 Nothing (Term Any)

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

-- Distance *to* the tag, i.e. t1 := FixedTag t2 d => t1 <- t2 - d
data FixedTag = FixedTag TagId Int | EndOfMatch Int deriving (Show, Ord, Eq)

type FixedTagMap = Map TagId FixedTag

-- Writer (TagId, FixedTag) a, or something?
type FixTagM a = State FixedTagMap a

setOffset :: FixedTag -> Int -> FixedTag
setOffset (FixedTag t1 _) d = FixedTag t1 d
setOffset (EndOfMatch _) d = EndOfMatch d

-- Tag fixing proceeds backwards, starting with a distance 0 from the
-- EndOfMatch reference.
-- d is the distance to the reference tagid (if known)
-- k is the distance to the end of the current "level", i.e. used to track
-- the fixed length of a subexpression (if possible). If this is output as
-- Just k, the subexpression has a constant length that will be propagated.
fixedTags :: Maybe FixedTag -> Maybe Int -> Maybe Int -> TaggedRegex -> FixTagM (Maybe FixedTag, Maybe Int, Maybe Int)
fixedTags t d k = go
  where
    go Empty = return (t, d, k)
    go (Term BOL) = return (t, d, k)
    -- If we match EOL, we know that EndOfMatch can't be more than 0 away.
    -- (If that is false, this is an impossible match, but we're not worrying
    -- about those yet.)
    -- Note that EOL could appear in the middle of a match if we did multiline
    -- matching, which we might want to add at some point. (GNU extension.)
    go (Term EOL) | Nothing <- t =
        return (Just (EndOfMatch 0), Just 0, k)
    go (Term EOL) = return (t, d, k)
    go (Term _) = return (t, succ <$> d, succ <$> k)
    go (Or x y) = do
      (_,_,k1) <- fixedTags Nothing Nothing (Just 0) x
      (_,_,k2) <- fixedTags Nothing Nothing (Just 0) y
      if eqJust k1 k2
        then return (t, (+) <$> k1 <*> d, (+) <$> k1 <*> d)
        else return (t, Nothing, Nothing)
    go (Cat x y) = do
      (t2, d2, k2) <- fixedTags t d k y
      fixedTags t2 d2 k2 x
    go (Repeat n m x) = do
      (_, _, k1) <- fixedTags Nothing Nothing (Just 0) x
      let addOffset = ((+) <$> ((* n) <$> k1) <*>)
      if Just n == m
        then return (t, addOffset d, addOffset k)
        else return (t, Nothing, Nothing)
    go (TagTerm tag) | Just t' <- t, Just d' <- d =
        modify (M.insert tag (setOffset t' d')) >> return (t, d, k)
                     | otherwise = return (Just (FixedTag tag 0), Just 0, k)

    eqJust (Just x) (Just y) = x == y
    eqJust _ _ = False


-- Remove tags that can be calculated from other tags, and produce a map of how
-- to calculate them. Run after removing otherwise unused tags to avoid having
-- to think about dependencies from used fixed tags on otherwise unused tags.
fixTags :: TaggedRegex -> (TaggedRegex, FixedTagMap)
fixTags re = (removeFixedTags m re, m)
    where
      m = execState (fixedTags (Just (EndOfMatch 0)) (Just 0) (Just 0) re) M.empty

-- After calculating fixed tags, remove the tag terms from the regex so the
-- rest of the engine doesn't need to consider them.
removeFixedTags :: FixedTagMap -> TaggedRegex -> TaggedRegex
removeFixedTags m = selectTags (\t -> not (M.member t m))

type TagMap = Map TagId Int

resolveFixedTags :: FixedTagMap -> Int -> TagMap -> TagMap
resolveFixedTags fts pos ts = foldr f ts (M.toList fts)
  where
    f (t, FixedTag b d) ts = M.alter (\_ -> (subtract d) <$> M.lookup b ts) t ts
    f (t, EndOfMatch d) ts = M.insert t (pos - d) ts

--  An example from the TDFA paper: (1a2)∗3(a|4b)5b∗
exampleTaggedRegex = foldr cat Empty [
    Repeat 0 Nothing (foldr cat Empty [TagTerm (T 0), Term (Symbol 'a'), TagTerm (T 1)]),
    TagTerm (T 2),
    or_ (Term (Symbol 'a')) (cat (TagTerm (T 3)) (Term (Symbol 'b'))),
    TagTerm (T 4),
    Repeat 0 Nothing (Term (Symbol 'b'))]
