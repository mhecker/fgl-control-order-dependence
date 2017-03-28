{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.NTICD where

import Data.Maybe(fromJust)

import Data.List(foldl', intersect)

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

cdepGraphP :: DynGraph gr => (gr CFGNode CFGEdge -> Node -> CFGEdge -> Node -> gr CFGNode Dependence) -> Program gr -> gr CFGNode Dependence 
cdepGraphP graphGen  p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    foldr mergeTwoGraphs empty [ graphGen (nfilter (\node -> staticThreadOf node == thread) tcfg)
                                          (entryOf thread)
                                          (false)
                                          (exitOf thread)
                               | thread <- Set.toList staticThreads ]

cdepGraph :: DynGraph gr => (gr a b -> Node -> b -> Node -> Map Node (Set Node)) -> gr a b -> Node -> b -> Node -> gr a Dependence
cdepGraph cdGen graph entry label exit = mkGraph (labNodes graph) [ (n,n',ControlDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = cdGen graph entry label exit



nticdGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdGraphP = cdepGraphP nticdGraph

nticdGraph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
nticdGraph = cdepGraph nticd 


type T n = (n, n)

type SmnFunctional = Map (Node,Node) (Set (T Node)) -> Map (Node,Node) (Set (T Node))
type SmnFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> SmnFunctional


f :: DynGraph gr => SmnFunctionalGen gr a b
f graph condNodes _ _ s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $
                   Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- condNodes, p /= n,
                                                             (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]

                 ⊔ Map.fromList [ ((m,n), s ! (n,n)) | n <- condNodes, m <- suc graph n, m /= n ]



f3 :: DynGraph gr => SmnFunctionalGen gr a b
f3 graph condNodes _ nextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $
                   Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x], 
                                                                  (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]




snmGfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmGfp graph f = (𝝂) smnInit (f3 graph condNodes reachable nextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, m `elem` reachable x]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        trncl = trc graph

snm :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snm graph = snmGfp graph f3


ntXcd :: DynGraph gr => (gr a b -> Map (Node, Node) (Set (T Node))) -> gr a b -> Node -> b -> Node -> Map Node (Set Node)
ntXcd snm graph entry label exit = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph']
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph', m /= n, 
                                            let tmn = Set.size $ s ! (m,n),
                                            0 < tmn, tmn < (Set.size $ Set.fromList $ suc graph' n)
                                      ]
                     ) | n <- condNodes
                  ]
    ⊔ Map.fromList [ (entry, Set.fromList [ exit]) ]
  where graph' = insEdge (entry, exit, label) graph 
        s = snm graph' 
        condNodes = [ n | n <- nodes graph', length (suc graph' n) > 1 ]


nticd :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
nticd = ntXcd snm


























ntscdGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdGraphP p = cdepGraphP ntscdGraph p

ntscdGraph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
ntscdGraph = cdepGraph ntscd 

ntscd :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
ntscd = ntXcd snmSensitive 

snmLfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmLfp graph f = (㎲⊒) smnInit (f graph condNodes reachable nextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        trncl = trc graph

snmSensitive :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmSensitive graph = snmLfp graph f4

f4 graph condNodes _ _ s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $
                   Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- condNodes, p /= n,
                                                             (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]






ntscdGraphP' :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdGraphP' = cdepGraphP ntscdGraph'

ntscdGraph' :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
ntscdGraph' = cdepGraph ntscd'

ntscd' :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
ntscd' = ntXcd snmSensitive' 

snmSensitive' :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmSensitive' graph = snmLfp graph f3







nextCondNode graph n = nextCondSeen [n] n
    where nextCondSeen seen n = case suc graph n of
            []    -> Nothing
            [ n'] -> if n' `elem` seen then Nothing else nextCondSeen (n':seen) n'
            (_:_) -> Just n







