{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.PostDominance.GraphTransformations where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic(grev)
import Data.Graph.Inductive.Query.Dominators (iDom)


import Unicode
import Data.Graph.Inductive.Util(controlSinks)
import Data.Graph.Inductive.Query.Util.GraphTransformations (sinkShrinkedGraph)


isinkdomOfSinkContraction :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfSinkContraction graph = fmap (Set.delete endNode) $ 
                                  Map.fromList [ (x, idomClassic ! x)  | x <- nodes graph, not $ x ∈ sinkNodes ]
                                ⊔ Map.fromList [ (x, Set.fromList [y]) | (s:sink) <- sinks, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
                                ⊔ Map.fromList [ (x, Set.empty)        | x <- nodes graph]
    where [endNode] = newNodes 1 graph
          sinks = controlSinks graph
          idomClassic = fmap (\x -> Set.fromList [x]) $ Map.fromList $ iDom (grev $ sinkShrinkedGraph graph endNode) endNode
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]
