module Data.Graph.Inductive.Query.PostDominance.Abstract where

import Debug.Trace (traceShow)

import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive



import Unicode
import Data.Graph.Inductive.Util (delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominance (sinkdomNaiveGfp)

abstractOf :: (Ord b, DynGraph gr) => gr a b -> (Node -> Set Node) -> gr (Set Node) b
abstractOf graph abstraction = mkGraph nodes' edges'
  where nodes' = zip [100..] (Set.toList $ Set.fromList   [           ns                    | n            <-    nodes graph, let ns  = abstraction n ])
        edges' =              Set.toList $ Set.fromList $ [(toNode' ! ns, toNode' ! ns', l) | (n, n', l) <- labEdges graph, let ns  = abstraction n ,
                                                                                                                            let ns' = abstraction n' ]
        toNode' = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes'

type AbstractNode = Set Node


decidingAbstractNodes :: DynGraph gr => gr a b -> Map Node AbstractNode -> Set AbstractNode
decidingAbstractNodes graph abstractionM = 
      Set.fromList [ ns | ns <- Map.elems abstractionM,
                          (∃) ns (\n -> (∃) (suc graph n) (\m1 -> (∃) (suc graph n) (\m2 -> 
                            (not $ m1 == n) ∧ (not $ m2 == n) ∧ (m1 /= m2)
                          )))]

abstractSlice :: (DynGraph gr, Ord b) => gr a b -> Map Node AbstractNode -> Set AbstractNode -> Set AbstractNode
-- abstractSlice :: (Show b, Ord b) => Gr a b -> Map Node AbstractNode -> Set AbstractNode -> Set AbstractNode
abstractSlice graph abstractionM ms =
    -- traceShow deciding' $
    -- traceShow sinkdom' $
    -- traceShow abstractGraph' $ 
    ms ∪ Set.fromList [ ns | (n', ns) <- labNodes abstractGraph', ns ∈ deciding',  Set.null $ sinkdom' ! n' ∩ msInAbstractGraphS ]
  where msL = Set.toList 
        abstractGraph = abstractOf graph a
          where a n = abstractionM ! n

        msInAbstractGraph = [ n' | (n', ns) <- labNodes abstractGraph, ns ∈ ms ]
        msInAbstractGraphS = Set.fromList msInAbstractGraph

        msInGraph = [ n | ns <- Set.toList $ ms, n <- Set.toList ns ]

        abstractGraph' =
          let { toMs = subgraph (rdfs msInAbstractGraph abstractGraph) abstractGraph } in foldr (flip delSuccessorEdges) toMs msInAbstractGraph
        graph' = 
          let { toMs = subgraph (rdfs msInGraph                 graph)         graph } in foldr (flip delSuccessorEdges) toMs msInGraph

        deciding' = decidingAbstractNodes graph' abstractionM
        sinkdom' = sinkdomNaiveGfp abstractGraph' 


