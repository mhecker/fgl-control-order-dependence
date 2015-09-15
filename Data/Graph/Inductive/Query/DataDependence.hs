{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.DataDependence where


import Unicode

import IRLSOD
import Program

import Algebra.Lattice

import Data.Char

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.Dataflow
import Data.Graph.Inductive.Query.Dependence


{- Es passt schon die default Instanziierung:
   instance BoundedJoinSemiLattice (Map Var (Set Node))
-}

dependenceAnalysis :: Set Var -> DataflowAnalysis (Map Var (Set (LEdge CFGEdge))) CFGEdge
dependenceAnalysis vars = DataflowAnalysis {
    transfer = transfer,
    initial = initial
  }
 where
  initial = Map.fromList [ (var, Set.empty) | var <- Set.toList vars ]

  transfer e@(_,_,Guard _ _)  reachingDefs = reachingDefs
  transfer e@(_,_,Assign x _) reachingDefs = Map.insert x (Set.singleton e) reachingDefs
  transfer e@(_,_,Read   x _) reachingDefs = Map.insert x (Set.singleton e) reachingDefs
  transfer e@(_,_,Print  _ _) reachingDefs = reachingDefs
  transfer e@(_,_,Spawn)       _           = Map.empty



dataDependence :: DynGraph gr => gr CFGNode CFGEdge -> Set Var -> Node -> Map Node (Set Node)
dataDependence graph vars entry = Map.fromList [
      (n, Set.fromList $
          [ reachedFromN | reachedFromN <- nodes graph,
                           let edges :: Map Var (Set (LEdge CFGEdge))
                               edges = reaching ! reachedFromN,
                           let nodes :: Map Var (Set (Node))
                               nodes = fmap (\set -> Set.map (\(n,_,_) -> n) set) edges,
                           var <- Set.toList $ use graph reachedFromN,
                           n `Set.member` (nodes ! var)]
      )
     | n <- nodes graph
    ]
  where reaching :: Map Node (Map Var (Set (LEdge CFGEdge)))
        reaching = analysis (dependenceAnalysis vars) graph entry

dataDependenceGraph :: DynGraph gr => gr CFGNode CFGEdge -> Set Var -> Node -> gr CFGNode Dependence
dataDependenceGraph graph vars entry = mkGraph (labNodes graph) [ (n,n',DataDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = dataDependence graph vars entry


dataDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
dataDependenceGraphP p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    foldr mergeTwoGraphs empty [ dataDependenceGraph (nfilter (\node -> staticThreadOf node == thread) tcfg)
                                                     (vars p)
                                                     (entryOf thread)
                                 | thread <- Set.toList staticThreads ]
