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


type T n = (n, n)

type SmnFunctional = Map (Node,Node) (Set (T Node)) -> Map (Node,Node) (Set (T Node))
type SmnFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> SmnFunctional


{- Generic utility functions -}

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


snmGfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmGfp graph f = (𝝂) smnInit (f3 graph condNodes reachable nextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, m `elem` reachable x]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        trncl = trc graph

snmLfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmLfp graph f = (㎲⊒) smnInit (f graph condNodes reachable nextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        trncl = trc graph

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




{- The functional from [1] Figure 5, which yields an *incorrect* implementation of nticd, both if we take its least or greatest fixed point.

   [1] "A New Foundation for Control Dependence and Slicing for Modern Program Structures", Journal Version

       http://doi.acm.org/10.1145/1275497.1275502

       VENKATESH PRASAD RANGANATH, TORBEN AMTOFT,
       ANINDYA BANERJEE, and JOHN HATCLIFF
       Kansas State University

       and
       MATTHEW B. DWYER
       University of Nebraska
-}

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




{- two correct nticd implementations, using the gfp of functional f3/f3' -}
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


f3' :: DynGraph gr => SmnFunctionalGen gr a b
f3' graph condNodes _ nextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $
                   Map.fromList [ ((m,p),
                        Set.fromList [ (p,m) | m `elem` suc graph p ]
                      ⊔ (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n]
                      ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x],
                                                (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                      ]
                    ) | m <- nodes graph, p <- condNodes ]


nticdF3GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3GraphP = cdepGraphP nticdF3Graph

nticdF3Graph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
nticdF3Graph = cdepGraph nticdF3

nticdF3 :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
nticdF3 = ntXcd snmF3

snmF3 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3 graph = snmGfp graph f3


nticdF3'GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'GraphP = cdepGraphP nticdF3'Graph

nticdF3'Graph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
nticdF3'Graph = cdepGraph nticdF3'

nticdF3' :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
nticdF3' = ntXcd snmF3'

snmF3' :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3' graph = snmGfp graph f3'



{- A Worklist-Implementation of nticd, based on f3 -}
nticdF3WorkListGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3WorkListGraphP = cdepGraphP nticdF3WorkListGraph

nticdF3WorkListGraph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
nticdF3WorkListGraph = cdepGraph nticdF3WorkList

nticdF3WorkList :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
nticdF3WorkList = ntXcd snmF3WorkListGfp

snmF3WorkListGfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3WorkListGfp graph = snmWorkList (Set.fromList [ (m,p) | m <- nodes graph, p <- condNodes ]) smnInit
  where snmWorkList :: Set (Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' =   Set.fromList [ (p,m) | m `elem` suc graph p ]
                           ⊔ (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n]
                           ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x],
                                                     (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                           ]
                    influenced = if (smp == smp')
                      then Set.empty
                      else   Set.fromList [ (n,p) | [ n ] <- [suc graph m] ]
                           ⊔ Set.fromList [ (m,n) | n <- condNodes, x <- (suc graph n), Just p == nextCond x ]

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, m `elem` reachable x]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        trncl = trc graph



{- A correct implementation of ntscd, as given in [1], Figure 4,
   using the lfp of functional f4
-}
ntscdF4GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF4GraphP p = cdepGraphP ntscdF4Graph p

ntscdF4Graph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
ntscdF4Graph = cdepGraph ntscdF4 

ntscdF4 :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
ntscdF4 = ntXcd snmF4

snmF4 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF4 graph = snmLfp graph f4

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




{- A correct implementation of ntscd,
   using the lfp of functional f3.

   This shows that ntscd and nticd are, essentially, the lfp/gfp (respectively) of the *same* functional f3.
-}
ntscdF3GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF3GraphP = cdepGraphP ntscdF3Graph

ntscdF3Graph :: DynGraph gr => gr a b -> Node -> b -> Node -> gr a Dependence
ntscdF3Graph = cdepGraph ntscdF3

ntscdF3 :: DynGraph gr => gr a b -> Node -> b -> Node -> Map Node (Set Node)
ntscdF3 = ntXcd snmF3Lfp

snmF3Lfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3Lfp graph = snmLfp graph f3







{- Utility functions -}
nextCondNode graph n = nextCondSeen [n] n
    where nextCondSeen seen n = case suc graph n of
            []    -> Nothing
            [ n'] -> if n' `elem` seen then Nothing else nextCondSeen (n':seen) n'
            (_:_) -> Just n







