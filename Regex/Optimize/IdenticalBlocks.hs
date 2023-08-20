{-# LANGUAGE FlexibleInstances, GADTs, TypeFamilies, StandaloneDeriving, CPP, ScopedTypeVariables, FlexibleContexts #-}

module Regex.Optimize.IdenticalBlocks (mergeIdenticalBlocks) where

{- "Identical blocks" optimization
 -
 - Find basic blocks that are the same / equivalent and merge them.
 -}

import Compiler.Hoopl as H hiding ((<*>))

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)

import Debug.Trace

import qualified CharMap as CM
import Regex.IR

type BlockTail = ([Insn O O], Insn O C)

mergeIdenticalBlocks :: Label -> Graph Insn C C -> (Label, Graph Insn C C)
mergeIdenticalBlocks entry graph = (tLabel entry m, merge m graph)
  where (bm,m) = blockMap graph

blocks (GMany _ bs _) = bs

blockMap :: Graph Insn C C -> (Map BlockTail Label, Map Label Label)
blockMap graph = foldr f (M.empty, M.empty) (blocks graph)
  where
    f' block (bm, lm) = trace ("blockMap: f' " ++ show (bm, lm)) (f block (bm,lm))
    -- First found duplicate wins here, would be nicer to always choose the
    -- lower label as "the" one though. Then again, we may already know that
    -- the blocks are in order by label.
    f block (bm, lm) | Just l <- M.lookup key bm = (bm, M.insert label l lm)
                     | otherwise                 = (M.insert key label bm, lm)
      where (Label label, body, tail) = blockSplit block
            key = (blockToList body, tail)

tLabel l = M.findWithDefault l l
tLabelSet ls = setFromList <$> mapM tLabel (setElems ls)
tLabelMap cm m = CM.map (flip tLabel m) cm

tInsn :: forall e x . Insn e x -> Map Label Label -> Insn e x
tInsn (Label l) = pure (Label l)
tInsn (Branch l) = Branch <$> tLabel l
tInsn (IfBOL l1 l2) = IfBOL <$> tLabel l1 <*> tLabel l2
tInsn (Switch cm l) = Switch <$> tLabelMap cm <*> tLabel l
tInsn (TotalSwitch cm) = TotalSwitch <$> tLabelMap cm
tInsn (CheckBounds b eof cont) = CheckBounds b <$> tLabel eof <*> tLabel cont
tInsn (Fallback ls) = Fallback <$> tLabelSet ls
tInsn (SetFallback l) = SetFallback <$> tLabel l
tInsn insn = pure insn

merge m = mapGraph (\i -> tInsn i m)
