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
import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

import Regex (Regex)
import qualified Regex

type TagId = Int
type Prio = Int

data Tag = NoTag | UnTag TagId | Tag TagId deriving (Show, Ord, Eq)

-- Convenient for the TNFA conversion, but the Eps transition is not used here.
-- Wouldn't be too much work to translate in TNFA.
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
    go (Regex.Concat xs) = foldr1 Cat <$> mapM go xs
    go (Regex.Or xs) = foldr1 Or <$> mapM go xs
    go (Regex.Group x) = do
      tStart <- tag
      tEnd <- tag
      tre <- go x
      return (cat3 tStart tre tEnd)
    go (Regex.Repeat n m x) = Repeat n m <$> go x
    go (Regex.BackRef i) = error "Back-references not supported in TDFA"

    tag = gets TagTerm <* modify succ
    cat3 x y z = Cat x (Cat y z)

testTagRegex :: String -> TaggedRegex
testTagRegex = tagRegex . Regex.parseString True . C.pack
