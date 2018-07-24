{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert
module Data.Graph.Inductive.Query.InfiniteDelay where

-- import Data.Ord (comparing)
import Data.Maybe(fromJust)
import Control.Monad (liftM, foldM, forM, forM_)

import System.Random
import Control.Monad.Random


-- import Control.Monad.ST
-- import Data.STRef

-- import Data.Functor.Identity (runIdentity)
-- import qualified Control.Monad.Logic as Logic
import Data.List(foldl', intersect,foldr1, partition)

import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
-- import Data.Graph.Inductive.Query.DFS (reachable)
-- import Data.Graph.Inductive.Query.Dominators (dom, iDom)
-- import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Data.Graph.Inductive.Query.BalancedSCC (samplePathsFor)




-- import Algebra.Lattice
-- import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)

import Util
import Unicode



-- import Data.Graph.Inductive.Query.TransClos
-- import Data.Graph.Inductive.Basic hiding (postorder)
-- import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.DFS (reachable)

import Data.Graph.Inductive.Query.NTICD
-- import Data.Graph.Inductive.Query.LCA


import Debug.Trace
import Control.Exception.Base (assert)


inSameBranch g = \start n m -> {-(m `elem` reachable n g) ∧ -} (n `elem` reachable start g   ∧   m `elem` reachable start g)  ∧  (
        -- let pns = Set.fromList [ p | (p,ns) <- Map.assocs nticd, p `elem` reachable start g, n ∈ ns ]
        --     pms = Set.fromList [ p | (p,ns) <- Map.assocs nticd, p `elem` reachable start g, m ∈ ns ]
        -- in pns == pms  ∧  (not $ Set.null pms) ∧  (∀) pms (\p ->  (∃) (suc g p) (\x -> n ∈ sinkdom ! x  ∧  m ∈ sinkdom ! x))
        (∃) (Map.assocs nticd) (\(p,ns) -> p `elem` reachable start g   ∧    m ∈ ns   ∧         n ∈ ns  ∧  (∃) (suc g p) (\x -> n ∈ sinkdom ! x  ∧  m ∈ sinkdom ! x))
      -- ∨ (∀) (Map.assocs nticd) (\(p,ns) -> (not $ m ∈ ns)  ∧  (not $ n ∈ ns))
      ∨ (Set.fromList [n,m] ⊆ reachableFrom sinkdom (Set.fromList [start]) (Set.empty))
    )
  where nticd = nticdF3 g
        sinkdom = sinkdomOfGfp g

delayedInfinitely g = \trace m -> case trace of
    []        -> False
    (start:_) -> (not $ m `elem` trace) ∧ (∃) (trace) (\n ->  insame start n m)
  where insame = inSameBranch g


sampleLoopPathsFor :: (Eq b, Graph gr)             => Int -> Integer ->  gr a b ->   [[LEdge b]]
sampleLoopPathsFor seed k g = fmap reverse $ evalRand (sampleLoopPaths k g) (mkStdGen seed)

sampleLoopPaths :: (MonadRandom m, Graph gr, Eq b) =>        Integer -> gr a b -> m [[LEdge b]]
sampleLoopPaths         k g
  | null (nodes g) = return []
  | otherwise      = sampleSome [] 0
     where 
        sample :: MonadRandom m => [t] -> m t
        sample xs = do
          i <- getRandomR (1, length xs)
          return $ xs !! (i-1)
        sampleSome sampled i
          | i >= k            = return $ sampled
          | otherwise         = do
              n0 <- sample $ nodes g
              newTrace <- sampleTrace n0 []
              sampleSome (newTrace:sampled) (i+1)
        sampleTrace n trace
          | looped              = return trace
          | finished            = return []
          | otherwise = do
               (m,e) <- sample successors
               sampleTrace m ((n,m,e):trace)
         where finished   = null successors
               successors = lsuc g n
               looped     = n `elem` (fmap (\(n,_,_) -> n) trace)
