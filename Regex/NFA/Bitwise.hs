{-# LANGUAGE RecordWildCards,RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving,FlexibleInstances,FlexibleContexts #-}

-- Type for NFA automaton without tags, and possible with BOL and EOL
-- transitions although Glushkov's construction will not use them.

module Regex.NFA.Bitwise where

import Control.Monad
import Control.Monad.Trans.Writer

import Data.Array.Unboxed
import Data.Array.ST
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Numeric

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

class (IArray UArray w, Ix w, Bits w, Num w, Integral w) => BitNFAWord w where

instance BitNFAWord Word where

deriving instance Show (BitNFA Word)

bitwiseNFA :: Int -> NFA -> Maybe (BitNFA Word)
bitwiseNFA maxBits nfa@NFA{..} | nfaNumStates > maxBits = Nothing
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
bitAllStates BitNFA{..} = (1 `shiftL` bitNumStates) - 1

prevState :: BitNFAWord w => BitNFA w -> Char -> w -> w
prevState BitNFA{..} c d = bitTR ! (d .&. (M.findWithDefault 0 c bitB .|. bitCommonB))
nextState :: (IArray UArray w, Ix w, Bits w, Num w) => BitNFA w -> Char -> w -> w
nextState BitNFA{..} c d = (bitT ! d) .&. (M.findWithDefault 0 c bitB .|. bitCommonB)

data MatchResult = MatchedAt Int | FailedAt Int deriving (Show, Eq)

isMatch (MatchedAt _) = True
isMatch (FailedAt _) = False

matchWith :: (BitNFAWord w) =>
             Bool
          -> (BitNFA w -> Char -> w -> w)
          -> (BitNFA w -> w)
          -> (BitNFA w -> w)
          -> BitNFA w -> String -> Writer String MatchResult
matchWith earlyOut transF init final nfa = go 0 (init nfa)
  where
    trans = transF nfa
    isMatch d = 0 /= (d .&. final nfa)

    log s = tell s >> tell "\n"
    logState pos d msg = log ("@" ++ show pos ++ " " ++ showHex d ": " ++ msg)

    -- The initial state when searching backwards will always be accepting
    -- since it includes all states, so delay the isMatch check until we've
    -- tried at least one character?
    go pos d [] | isMatch d = logState pos d "EOL/match" >> return (MatchedAt pos)
                | otherwise = logState pos d "EOL/failed" >> return (FailedAt pos)
    go pos d _ | d == 0 = logState pos d "no active states" >> return (FailedAt pos)
               | earlyOut && isMatch d = logState pos d "match" >> return (MatchedAt pos)
    go pos d (c:cs) = logState pos d (show c) >> go (succ pos) (trans c d) cs

-- Note takes a reversed String
-- Check if the reversed string matches a revese prefix of the pattern.
matchReversePrefix :: (BitNFAWord w) => BitNFA w -> String -> Writer String MatchResult
matchReversePrefix = matchWith False prevState bitAllStates bitInitStates

matchForward :: (BitNFAWord w) => BitNFA w -> String -> Writer String MatchResult
matchForward = matchWith True nextState bitInitStates bitFinalStates

findBitwise :: (BitNFAWord w) => BitNFA w -> String -> Writer String Bool
findBitwise nfa@BitNFA{..} s
  | Just prefix <- maybeTake n s = do
    log ("Trying reverse match on: " ++ show prefix)
    rm <- q $ matchReversePrefix nfa (reverse prefix)
    log ("Reverse match result: " ++ show rm)
    case rm of
      FailedAt m -> do
        let skip = max 1 (n - m)
        log ("Skipping by " ++ show skip)
        findBitwise nfa (drop skip s)
      -- Note that what we find is not exactly that the backwards pattern
      -- matched, but rather we matched something that is a possible prefix of
      -- a true match. For strings or fixed-length patterns, it is the same and
      -- we don't need to verify anything, but for regular expressions we do
      -- need it.
      MatchedAt _ -> do
        match <- q $ matchForward nfa s
        log ("Forward-match test: " ++ show match)
        if isMatch match then return True else log "Skipping by 1" >> findBitwise nfa (tail s)
  | bitMatchesEmpty nfa = log "End: matched empty" >> return True
  | otherwise = log "String too short => no match" >> return False
  where
    maybeTake n s | prefix <- take n s, length prefix == n = Just prefix
                  | otherwise = Nothing
    n = bitMinLength
    log :: String -> Writer String ()
    log s = tell s >> tell "\n"
    q = censor (const mempty)
