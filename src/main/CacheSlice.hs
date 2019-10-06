{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheSlice where

import qualified Data.List as List

import Data.Bits (xor, (.&.), shiftL, shiftR)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Algebra.Lattice(JoinSemiLattice(..), BoundedJoinSemiLattice(..))

import Debug.Trace (traceShow)
import Control.Exception.Base (assert)


import Control.Monad.State
import Control.Monad.List


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic (grev)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.DFS (dfs, rdfs, topsort)
import Data.Graph.Inductive.Query.TransClos (trc)

import Unicode
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
import IRLSOD (CFGNode, CFGEdge, isGlobalName, use, def)
import qualified IRLSOD as IRLSOD (Input)


import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)

import CacheExecution (csdMergeDirectOf, csdMergeOf, cacheCostDecisionGraph)
import Data.Graph.Inductive.Query.DataDependence (dataDependence)
import Data.Graph.Inductive.Query.TSCD (timDFFromFromItimdomMultipleOfFastCost)

cacheTimingSliceFor :: forall gr. (DynGraph gr) => 
    (gr CFGNode CFGEdge -> Node -> Map Node (Set Node))
  -> gr CFGNode CFGEdge
  -> Node
  -> Set Node
  -> Set Node
cacheTimingSliceFor csd g n0 = \ms -> combinedBackwardSlice (undefined :: gr CFGNode CFGEdge) (tscd' ⊔ dd' ⊔ csd') Map.empty ms
  where tscd'  =            timDFFromFromItimdomMultipleOfFastCost ccg costF
        dd'    = invert'' $ dataDependence                         ccg vars  n0
        csd'   = invert'' $ csd                                      g       n0

        vars = Set.fromList [ var | n <- nodes g, var <- Set.toList $ use g n ∪ def g n, isGlobalName var]

        (ccg, cost) = cacheCostDecisionGraph g n0
        costF n m = cost ! (n,m)


cacheTimingSlice         g n0 = cacheTimingSliceFor csdMergeDirectOf g n0
cacheTimingSliceViaReach g n0 = cacheTimingSliceFor csdMergeOf       g n0


