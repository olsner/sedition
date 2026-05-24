{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances,FlexibleContexts #-}

-- Type for NFA automaton without tags, and possible with BOL and EOL
-- transitions although Glushkov's construction will not use them.

module Regex.NFA.Bitwise where

import Control.Monad

import Data.Array.Unboxed
import Data.Array.ST
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Regex.NFA.Type
import Regex.TNFA (StateId(..))

data BitNFA w = BitNFA
  { bitInitStates :: w
  , bitFinalStates :: w
  , bitNumStates :: Int
  , bitMinLength :: Int
  , bitT :: UArray w w
  -- Reverse T array, i.e. mask of all preceding states for each state mask.
  , bitTR :: UArray w w
  -- For compact printing etc, but expected to be a 256-word array in the
  -- end.
  , bitCommonB :: w
  , bitB :: Map Char w
  }

class (IArray UArray w, Ix w, Bits w, Num w) => BitNFAWord w where

instance BitNFAWord Word where

deriving instance Show (BitNFA Word)

-- Pretty low number - at least 16 is somewhat reasonable. Mainly this blows
-- up the printouts in ghci :)
-- Note: could also implement splitting of tables - e.g. two 8-bit tables for
-- the two halves of a 16-bit state word reduces space from 128kB to 1kB.
maxBitwiseStates = 10

bitwiseNFA :: NFA -> Maybe (BitNFA Word)
bitwiseNFA nfa@NFA{..} | nfaNumStates > maxBitwiseStates = Nothing
                       | otherwise = Just $ BitNFA {
    bitInitStates = bit nfaStartState,
    bitFinalStates = bits nfaFinalStates,
    bitT = t, bitCommonB = commonB, bitB = bmap,
    bitTR = tr,
    bitNumStates = nfaNumStates,
    bitMinLength = nfaMinLength nfa }
  where
    or = foldr (.|.) zeroBits
    and = foldr (.&.) oneBits
    bit (S i) = 1 `shiftL` i
    bits s = or (map bit (S.toList s))
    follow = tmReach nfaTrans
    fbits = M.map bits follow
    -- b = listArray (0, 255) (map getB ['\000'..'\255'])
    bmap = M.fromList [(c,b) | c <- ['\000'..'\255'], let b = getB c .&. (complement commonB), b /= 0]
    charsets = M.map bits (M.unionsWith S.union (M.elems nfaTrans))
    anyB = M.findWithDefault 0 Any charsets
    getB c = M.findWithDefault 0 (C c) charsets
    commonB = and (map getB ['\000'..'\255']) .|. anyB

    buildT tbits = runSTUArray $ do
      arr <- newArray (0, 1 `shiftL` nfaNumStates - 1) (0 :: Word)
      forM_ (nfaStates nfa) $ \s ->
        forM_ [0 .. bit s - 1] $ \j -> do
          t_j <- readArray arr j
          writeArray arr (bit s + j) (t_j .|. M.findWithDefault 0 s tbits)
      return arr
    t = buildT fbits

    precede = invertMap follow
    pbits = M.map bits precede
    tr = buildT pbits

bitMatchesEmpty BitNFA{..} =  0 /= (bitInitStates .&. bitFinalStates)

prevState :: BitNFAWord w => BitNFA w -> Char -> w -> w
prevState BitNFA{..} c d = bitTR ! (d .&. (M.findWithDefault 0 c bitB .|. bitCommonB))
nextState :: (IArray UArray w, Ix w, Bits w, Num w) => BitNFA w -> Char -> w -> w
nextState BitNFA{..} c d = (bitT ! d) .&. (M.findWithDefault 0 c bitB .|. bitCommonB)

data MatchResult = MatchedAt Int | FailedAt Int deriving (Show, Eq)

isMatch (MatchedAt _) = True
isMatch (FailedAt _) = False

matchWith :: (BitNFAWord w) =>
             (BitNFA w -> Char -> w -> w) -> (BitNFA w -> w) -> (BitNFA w -> w)
          -> BitNFA w -> String -> MatchResult
matchWith transF init final nfa = go 0 (init nfa)
  where
    trans = transF nfa
    isMatch d = 0 /= (d .&. final nfa)

    go pos d _ | isMatch d = MatchedAt pos
    go pos _ [] = FailedAt pos
    go pos d (c:cs) = go (pos + 1) (trans c d) cs

-- Note takes a reversed String
matchReverse :: (BitNFAWord w) => BitNFA w -> String -> MatchResult
matchReverse = matchWith prevState bitFinalStates bitInitStates

matchForward :: (BitNFAWord w) => BitNFA w -> String -> MatchResult
matchForward = matchWith nextState bitInitStates bitFinalStates

findBitwise nfa [] = bitMatchesEmpty nfa
findBitwise nfa@BitNFA{..} s
  | Just prefix <- maybeTake n s =
    case matchReverse nfa (reverse prefix) of
      FailedAt m -> findBitwise nfa (drop (max 1 (n - m)) s)
      -- TODO Isn't it guaranteed that a reverse match is a forward match?
      -- (Note in this case we do not care about the exact location of the
      -- first match - using this approach for proper regexes would need that.)
      MatchedAt _ -> isMatch (matchForward nfa s)
  | otherwise = False
  where
    maybeTake n s | prefix <- take n s, length prefix == n = Just prefix
                  | otherwise = Nothing
    n = bitMinLength
