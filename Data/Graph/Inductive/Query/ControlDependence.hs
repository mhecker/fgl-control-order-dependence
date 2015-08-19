{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.ControlDependence where



import Data.Maybe(fromJust)

import Data.List(foldl')

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import IRLSOD

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.Dominators

controlDependence :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
controlDependence graph entry label exit =
    Map.fromList
    [ (n, Set.fromList $
          [ controlledByN | controlledByN <- nodes graph,
                            n `Set.member` (postDomFronts ! controlledByN),
                            n /= controlledByN])
     | n <- nodes graph
    ]
  where postDomFronts = domFront (grev $ insEdge (entry, exit, label) graph) exit



domFront :: DynGraph gr => gr a b -> Node -> Map Node (Set Node)
domFront g root = foldl' (nodeDomFront g doms) initEmpty $ nodes g
    where doms :: Map Node Node
          doms = Map.fromList $ iDom g root
          initEmpty = Map.fromList $ [ (n, Set.empty) | n <- nodes g]


nodeDomFront :: DynGraph gr =>
                gr a b
             -> Map Node Node
             -> Map Node (Set Node)
             -> Node
             -> Map Node (Set Node)
nodeDomFront g doms df b = case preds of
        _:_:_ -> foldl' addDoms df preds
        _     -> df
    where  preds = pre g b
           addDoms :: Map Node (Set Node)
                   -> Node
                   -> Map Node (Set Node)
           addDoms df' p = foldl' addDom df' (follow p)

           addDom :: Map Node (Set Node)
                  -> Node
                  -> Map Node (Set Node)
           addDom = flip $ Map.adjust (Set.insert b)

           domsb = doms ! b

           follow :: Node -> [Node]
           follow r
            | r == domsb = []
            | otherwise = r : follow (doms ! r)
