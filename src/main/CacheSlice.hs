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
import Data.Graph.Inductive.Query.SP (sp)
import Data.Graph.Inductive.Query.TransClos (trc)

import Data.Graph.Inductive.Util (fromSuccMapWithEdgeAnnotation)

import Unicode
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
import IRLSOD (CFGNode, CFGEdge, isGlobalName, use, def)
import qualified IRLSOD as IRLSOD (Input)


import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)

import CacheExecution (csdMergeDirectOf, csdMergeOf, cacheCostDecisionGraph)
import Data.Graph.Inductive.Query.DataDependence (dataDependence)
import Data.Graph.Inductive.Query.TSCD (timDFFromFromItimdomMultipleOfFastCost)

cacheTimingSliceFor :: forall gr. (Show (gr CFGNode CFGEdge), DynGraph gr) => 
    (gr CFGNode CFGEdge -> Node -> Map Node (Set Node))
  -> gr CFGNode CFGEdge
  -> Node
  -> Set Node
  -> Set Node
cacheTimingSliceFor csd g n0 = \ms ->
    traceShow ("ccg",         ccg) $
    -- traceShow ("tscd", hide $ tscd') $
    -- traceShow ("dd",   hide $ dd') $ 
    -- traceShow ("csd",  hide $ csd') $
 -- combinedBackwardSlice  (tscd' ⊔ dd' ⊔ csd') Map.empty ms
    traceShow (3, 19, path 3 19) $
    traceShow (3, 20, path 3 20) $
    traceShow (3, 22, path 3 22) $
    traceShow (3, 23, path 3 23) $ 
    combinedBackwardSlice3  tscd'   dd'   csd'            ms
  where tscd'  =            timDFFromFromItimdomMultipleOfFastCost ccg costF
        dd'    = invert'' $ dataDependence                         ccg vars  n0
        csd'   = invert'' $ csd                                      g       n0

        vars = Set.fromList [ var | n <- nodes g, var <- Set.toList $ use g n ∪ def g n, isGlobalName var]

        (ccg, cost) = cacheCostDecisionGraph g n0
        costF n m = cost ! (n,m)

        hide = Map.filter (not . Set.null)

        path n m = zipWith f p (tail p)
          where Just p = sp n m depCostGraph
                f n m = (n, toDep n m, m)

        toDep n m = [ l | (m',l) <- lsuc depGraph n, m' == m ]
          
        
        depGraph = (
              fromSuccMapWithEdgeAnnotation
            $ fmap (Set.map (\n -> (n, TSCD))) tscd'
            ⊔ fmap (Set.map (\n -> (n, DD  ))) dd'
            ⊔ fmap (Set.map (\n -> (n, CSD ))) csd'
          ) :: Gr () DepEdge
          
        depCostGraph = emap depCost depGraph
          where depCost _ = 1


data DepEdge = TSCD | DD | CSD deriving (Show, Eq, Ord)


cacheTimingSlice         g n0 = cacheTimingSliceFor csdMergeDirectOf g n0
cacheTimingSliceViaReach g n0 = cacheTimingSliceFor csdMergeOf       g n0



combinedBackwardSlice3 :: Map Node (Set Node) -> Map Node (Set Node) -> Map Node (Set Node) -> Set Node -> Set Node
combinedBackwardSlice3 tscd' dd' csd' = \ms ->
     let result = slice Set.empty ms 
         slice s workset
             | Set.null workset = s
             | otherwise        =
                 -- (let nnew = fromTSCD ∖ s' in if Set.null nnew then id else traceShow (m, "newTSCD", nnew)) $ 
                 -- (let nnew = fromDD   ∖ s' in if Set.null nnew then id else traceShow (m, "newDD  ", nnew)) $ 
                 -- (let nnew = fromCSD  ∖ s' in if Set.null nnew then id else traceShow (m, "newCSD ", nnew)) $ 
                 slice s' workset'
           where (m, workset0) = Set.deleteFindMin workset
                 s'  = Set.insert m s
                 new = (fromTSCD ∪ fromDD ∪ fromCSD) ∖ s'
                 workset' = workset0 ∪ new

                 fromTSCD = Map.findWithDefault Set.empty m tscd'
                 fromDD   = Map.findWithDefault Set.empty m dd'
                 fromCSD  = Map.findWithDefault Set.empty m csd'
     in result


