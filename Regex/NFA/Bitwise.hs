{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances #-}

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
  -- Used for reverse matching
  -- , bitFollows :: Array w w
  , bitT :: UArray w w
  -- For compact printing etc, but expected to be a 256-word array in the
  -- end.
  , bitCommonB :: w
  , bitB :: Map Char w
  }

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
    bitNumStates = nfaNumStates }
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

    t = runSTUArray $ do
      arr <- newArray (0, 1 `shiftL` nfaNumStates - 1) 0
      forM_ (nfaStates nfa) $ \s ->
        forM_ [0 .. bit s - 1] $ \j -> do
          t_j <- readArray arr j
          writeArray arr (bit s + j) (t_j .|. M.findWithDefault 0 s fbits)
      return arr
