{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.NTICD where

import Data.Maybe(fromJust)

import Data.List(foldl')

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import IRLSOD
import Program

import Unicode


import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic 
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.Dependence


import Debug.Trace

tr msg x = seq x $ trace msg x

nticdGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdGraphP p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    foldr mergeTwoGraphs empty [ nticdGraph (nfilter (\node -> staticThreadOf node == thread) tcfg)
                                                        (entryOf thread)
                                                        (false)
                                                        (exitOf thread)
                                 | thread <- Set.toList staticThreads ]

nticdGraph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
nticdGraph graph entry label exit = mkGraph (labNodes graph) [ (n,n',ControlDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = nticd graph entry label exit



type T n = (n, n)






f :: DynGraph gr => gr a b -> [Node] -> Map (Node,Node) (Set (T Node)) -> Map (Node,Node) (Set (T Node))
f graph condNodes s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (length $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $  
                   Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- condNodes, p /= n,
                                                             (Set.size $ s ! (m,n)) == (length $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]

                 ⊔ Map.fromList [ ((m,n), s ! (n,n)) | n <- condNodes, m <- suc graph n, m /= n ]

snm :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snm graph = (𝝂) smnInit (f graph condNodes)  
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, reachable x m]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x n = n `elem` (suc trncl x)
        trncl = trc graph


nticd :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
nticd graph entry label exit =
      Map.fromList [ (n, Set.empty) | n <- nodes graph']
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph', m /= n, 
                                            let tmn = Set.size $ s ! (m,n),
                                            0 < tmn, tmn < (length $ suc graph' n)
                                      ]
                     ) | n <- condNodes
                  ]
    ⊔ Map.fromList [ (entry, Set.fromList [ exit]) ]
  where graph' = insEdge (entry, exit, label) graph 
        s = snm graph' 
        condNodes = [ n | n <- nodes graph', length (suc graph' n) > 1 ]
