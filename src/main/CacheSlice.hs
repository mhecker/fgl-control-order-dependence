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
import qualified Data.Graph.Inductive.Query.SP (sp)

import Data.Graph.Inductive.Query.TransClos (trc)

import Data.Graph.Inductive.Util (fromSuccMapWithEdgeAnnotation)

import Unicode
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
import IRLSOD (CFGNode, CFGEdge, isGlobalName, use, def)
import qualified IRLSOD as IRLSOD (Input)


import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)

import MicroArchitecturalDependence (CsGraph, muMergeDirectOf, cacheCostDecisionGraphFor)

import CacheExecution (CacheSize)
import qualified CacheStateDependence          as Precise   (cacheAbstraction)
import qualified CacheStateDependenceImprecise as Imprecise (cacheAbstraction)
import qualified CacheStateDependenceAgeSets   as AgeSets   (cacheAbstraction)
import qualified CacheStateDependenceAgeSetsDataDep
                                               as AgeSetsDD (allFromDataDep, allFromDataDepJoined)

import qualified CacheStateDependenceReach     as Reach     (csdMergeOf)

import Data.Graph.Inductive.Query.DataDependence (dataDependence)
import Data.Graph.Inductive.Query.TSCD (timDFFromFromItimdomMultipleOfFastCost)

sp :: (Real b, Graph gr) => Node -> Node -> gr a b -> Maybe Path
#if MIN_VERSION_fgl(5,5,4)
sp = Data.Graph.Inductive.Query.SP.sp
#else
sp n m g = Just $ Data.Graph.Inductive.Query.SP.sp n m g
#endif

cacheTimingSliceFor :: forall gr a e. (Show (gr CFGNode CFGEdge), DynGraph gr) =>
    CacheSize 
  -> (CsGraph a e, Map Node (Set Node), (gr CFGNode CFGEdge, Map (Node, Node) Integer))
  -> gr CFGNode CFGEdge
  -> [Node]
  -> Node
  -> Set Node
  -> Set Node
cacheTimingSliceFor cacheSize (csGraph, csd, (ccg, cost)) g debugNs n0 = \ms ->
{-
       slice = combinedBackwardSlice  (tscd' ⊔ dd' ⊔ csd') Map.empty ms'
    in slice
-}
    require (     ms ⊆ Set.fromList (nodes g)) $
    require (debugNS ⊆ Set.fromList (nodes g)) $
    let ms'      = Set.fromList [ m' | (m', m) <- labNodes ccg, m ∈ ms]
        debugNs' = Set.fromList [ n' | (n', n) <- labNodes ccg, n ∈ debugNS]
        slice' = combinedBackwardSlice3  tscd'   dd'   csd'            ms'
        slice  = Set.fromList [ m | m' <- Set.toList slice', let Just m = lab ccg m' ]
        trace = foldr (.) id [ traceShortestPath ms' slice' n | n <- debugNs]
    in trace slice

  where tscd'  =            timDFFromFromItimdomMultipleOfFastCost ccg costF
        dd'    = invert'' $ dataDependence                         ccg vars  n0
        csd'   = invert'' $ csd

        vars = Set.fromList [ var | n <- nodes g, var <- Set.toList $ use g n ∪ def g n, isGlobalName var]

        costF n m = cost ! (n,m)


        debugNS = Set.fromList debugNs

        traceShortestPath ms slice n
           | Set.size ms == 1 = trace
           | otherwise        = id
         where trace 
                 | n ∈ slice = traceShow (m, n, path m n)
                 | otherwise = id
               [m] = Set.toList ms
        
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

-- TODO: Arrow?
both f1 f2 cacheSize g n0  = (f1 cacheSize g n0, f2 cacheSize g n0)

fromMu mu g n0 = (csGraph, csd, (ccg, costs))
  where (csd, edgeCosts, csGraph) = muMergeDirectOf mu g n0
        (ccg, costs) = cacheCostDecisionGraphFor g csGraph edgeCosts

fromAll all g n0 = (csGraph, csd, (ccg, costs))
  where (csd, edgeCosts, csGraph) = all g n0
        (ccg, costs) = cacheCostDecisionGraphFor g csGraph edgeCosts

cacheTimingSlice               cacheSize g n0 = cacheTimingSliceFor cacheSize  (fromMu  (  Precise.cacheAbstraction     cacheSize) g n0) g [] n0
cacheTimingSliceImprecise      cacheSize g n0 = cacheTimingSliceFor cacheSize  (fromMu  (Imprecise.cacheAbstraction     cacheSize) g n0) g [] n0
cacheTimingSliceAgeSets        cacheSize g n0 = cacheTimingSliceFor cacheSize  (fromMu  (  AgeSets.cacheAbstraction     cacheSize) g n0) g [] n0
cacheTimingSliceAgeDDeps       cacheSize g n0 = cacheTimingSliceFor cacheSize  (fromAll (AgeSetsDD.allFromDataDep       cacheSize) g n0) g [] n0
cacheTimingSliceAgeDDepsJoined cacheSize g n0 = cacheTimingSliceFor cacheSize  (fromAll (AgeSetsDD.allFromDataDepJoined cacheSize) g n0) g [] n0
cacheTimingSliceViaReach       cacheSize g n0 = cacheTimingSliceFor cacheSize  (fromAll (    Reach.csdMergeOf           cacheSize) g n0) g [] n0



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


