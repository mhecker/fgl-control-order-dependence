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


decidingAbstractNodes :: DynGraph gr => gr a b -> Map Node AbstractNode -> Map AbstractNode (Set AbstractNode) -> Set AbstractNode
decidingAbstractNodes graph' abstractionM sinkdom' = 
      Set.fromList [ ns | n <- nodes graph', let ns = abstractionM ! n,
                          (∃) (suc graph' n) (\m1 -> (∃) (suc graph' n) (\m2 -> (if ns == Set.fromList [3,4,12] then traceShow (m1,m2, (abstractionM ! m1), (abstractionM ! m2)) else id) $ 
                            (not $ m1 == n) ∧ (not $ m2 == n) ∧ (m1 /= m2) ∧ (Set.null $ (sinkdom' ! (abstractionM ! m1)) ∩ (sinkdom' ! (abstractionM ! m2)))
                          ))]

--abstractSlice :: (DynGraph gr, Ord b) => gr a b -> Map Node AbstractNode -> Set AbstractNode -> Set AbstractNode
abstractSlice :: (Show a, Show b, Ord b) => Gr a b -> Map Node AbstractNode -> Set AbstractNode -> Set AbstractNode
abstractSlice graph abstractionM ms =
    -- traceShow deciding' $
    -- traceShow sinkdom' $
    -- traceShow abstractGraph' $
    -- traceShow graph' $
    -- traceShow sinkdom'Nodes $
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

        deciding' = decidingAbstractNodes graph' abstractionM sinkdom'Nodes
        sinkdom' = sinkdomNaiveGfp abstractGraph'
        sinkdom'Nodes :: Map AbstractNode (Set AbstractNode)
        sinkdom'Nodes = Map.fromList [ (ns, Set.fromList [ ms | m' <- Set.toList doms, let Just ms = lab abstractGraph' m' ])  | (n', ns) <- labNodes abstractGraph', let doms = sinkdom' ! n'  ]


