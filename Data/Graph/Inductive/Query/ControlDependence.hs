{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.ControlDependence where

import Data.Maybe(fromJust)

import Data.List(foldl')

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import IRLSOD
import Program

import Data.Graph.Inductive.Basic 
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Query.Dependence


controlDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
controlDependenceGraphP p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    foldr mergeTwoGraphs empty [ insEdge (entry,exit, ControlDependence) $
                                 controlDependenceGraph (insEdge (entry, exit, false) $ nfilter (\node -> staticThreadOf node == thread) tcfg)
                                                        exit
                                 | thread <- Set.toList staticThreads, let entry = entryOf thread, let exit = exitOf thread ]

controlDependenceGraph :: DynGraph gr => gr a b -> Node -> gr a Dependence
controlDependenceGraph graph exit = mkGraph (labNodes graph) [ (n,n',ControlDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = controlDependence  graph exit

controlDependence :: DynGraph gr => gr a b ->  Node -> Map Node (Set Node)
controlDependence graph exit =
    Map.fromList
    [ (n, Set.fromList $
          [ controlledByN | controlledByN <- nodes graph,
                            n /= controlledByN,
                            n `Set.member` (postDomFronts ! controlledByN)
                            ])
     | n <- nodes graph
    ]
  where postDomFronts = domFront (grev graph) exit



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
        []    -> df
        [_]   -> df
        _     -> foldl' addDoms df preds
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
