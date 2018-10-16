{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert
#define PDOMUSESDF
module Data.Graph.Inductive.Query.NTICD where

import Data.Ord (comparing)
import Data.Maybe(fromJust)
import Control.Monad (liftM, foldM, forM, forM_)

import Control.Monad.ST
import Data.STRef

import Data.Functor.Identity (runIdentity)
import qualified Control.Monad.Logic as Logic
import Data.List(foldl', intersect,foldr1, partition)

import qualified Data.Tree as Tree
import Data.Tree (Tree(..))

import qualified Data.PQueue.Prio.Max as Prio.Max

import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive.Query.NTICDNumbered (iPDomForSinks)
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)


import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)
import Data.Dequeue.SimpleDequeue (SimpleDequeue)


import qualified Data.Foldable as Foldable
import IRLSOD
import Program

import Util(the, invert', invert'', invert''', foldM1, reachableFrom, reachableFromM, isReachableFromM, treeDfs, toSet, fromSet, reachableFromTree, fromIdom, fromIdomM, roots, dfsTree, restrict, isReachableFromTreeM, without, findCyclesM, treeLevel, isReachableBeforeFromTreeM)
import Unicode



import Data.Graph.Inductive.Query.LCA

import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic hiding (postorder)
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs, rdfs, rdff, reachable)

import Debug.Trace
import Control.Exception.Base (assert)

tr msg x = seq x $ trace msg x


type T n = (n, n)

type SmnFunctional = Map (Node,Node) (Set (T Node)) -> Map (Node,Node) (Set (T Node))
type SmnFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> SmnFunctional


{- Generic utility functions -}

cdepGraphP :: DynGraph gr => (gr CFGNode CFGEdge -> gr CFGNode Dependence) -> Program gr -> gr CFGNode Dependence 
cdepGraphP graphGen  p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    foldr mergeTwoGraphs callDependenceGraph
                               [ insEdge (entry, exit, ControlDependence) $ 
                                 graphGen (insEdge (entry, exit, false) $ nfilter (\node -> staticProcedureOf node == procedure)
                                                                        $ efilter (\(_,_,l) -> isIntraCFGEdge l)
                                                                        $ tcfg
                                          )
                               | procedure <- Set.toList staticProcedures,  let entry = entryOf procedure, let exit = exitOf procedure ]
  where callDependenceGraph = mkGraph (labNodes tcfg) [ (call, entry, CallDependence) | (call, entry, Call) <- labEdges tcfg]
        
cdepGraph :: DynGraph gr => (gr a b -> Map Node (Set Node)) -> gr a b -> gr a Dependence
cdepGraph cdGen graph  = mkGraph (labNodes graph) [ (n,n',ControlDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = cdGen graph


snmGfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmGfp graph f = (𝝂) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

snmLfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmLfp graph f = (㎲⊒) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

ntXcd :: DynGraph gr => (gr a b -> Map (Node, Node) (Set (T Node))) -> gr a b -> Map Node (Set Node)
ntXcd snm graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            m /= n,
                                            let tmn = Set.size $ s ! (m,n),
                                            0 < tmn, tmn < (Set.size $ Set.fromList $ suc graph n)
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snm graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]




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

f5 :: DynGraph gr => SmnFunctionalGen gr a b
f5 graph condNodes _ _ _ s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- condNodes, p /= n,
                                                             (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]

                 ⊔ Map.fromList [ ((m,n), s ! (n,n)) | n <- condNodes, m <- suc graph n, m /= n ]


nticdF5GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF5GraphP = cdepGraphP nticdF5Graph

nticdF5Graph :: DynGraph gr => gr a b -> gr a Dependence
nticdF5Graph = cdepGraph nticdF5

nticdF5 :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF5 = ntXcd snmF5

snmF5 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF5 graph = snmLfp graph f5





{- two correct nticd implementations, using the gfp of functional f3/f3' -}
f3 :: DynGraph gr => SmnFunctionalGen gr a b
f3 graph condNodes reachable nextCond toNextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                  -- m ∊ reachable x,
                                                                  m ∊ toNextCond x]
                                  ) | m <- nodes graph, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                  m ∊ reachable x,
                                                                  Just n <- [nextCond x], 
                                                                  (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]

f3' :: DynGraph gr => SmnFunctionalGen gr a b
f3' graph condNodes reachable nextCond toNextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,p),
                        Set.fromList  [ (p,x) | x <- (suc graph p), m ∊ reachable x,
                                                                    m ∊ toNextCond x]
                      ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), m ∊ reachable x,
                                                                    Just n <- [nextCond x],
                                                (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                      ]
                    ) | m <- nodes graph, p <- condNodes]


nticdF3GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3GraphP = cdepGraphP nticdF3Graph

nticdF3Graph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3Graph = cdepGraph nticdF3

nticdF3 :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3 = ntXcd snmF3

snmF3 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3 graph = snmGfp graph f3


nticdF3'GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'GraphP = cdepGraphP nticdF3'Graph

nticdF3'Graph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3'Graph = cdepGraph nticdF3'

nticdF3' :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3' = ntXcd snmF3'

snmF3' :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3' graph = snmGfp graph f3'



f3'dual :: DynGraph gr => SmnFunctionalGen gr a b
f3'dual graph condNodes reachable nextCond toNextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,p), (
                        Set.fromList  [ (p,x) | x <- (suc graph p), not $ m ∊ toNextCond x, Just n <- [nextCond x], (Set.size $ s ! (m,n)) /= 0 ]
                    ) ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), not $ m ∊ reachable x ]
                   ) | m <- nodes graph, p <- condNodes]
  where all p m = [ (p,x) | x <- (suc graph p)]


nticdF3'dualGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'dualGraphP = cdepGraphP nticdF3'dualGraph

nticdF3'dualGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdF3'dualGraph = cdepGraph nticdF3'dual

nticdF3'dual :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdF3'dual = ntXcd snmF3'dual

snmF3'dual :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3'dual graph = snmLfp graph f3'dual


nticdF3'dualWorkListGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'dualWorkListGraphP = cdepGraphP nticdF3'dualWorkListGraph

nticdF3'dualWorkListGraph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3'dualWorkListGraph = cdepGraph nticdF3'dualWorkList

nticdF3'dualWorkList :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3'dualWorkList = ntXcd snmF3'dualWorkListLfp

snmF3'dualWorkListLfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3'dualWorkListLfp graph = snmWorkList (Set.fromList [ (m,n,x) | p <- condNodes, m <- nodes graph, Set.size (smnInit ! (m,p)) /= 0, (n,x) <- prevCondsWithSucc p ]) smnInit
  where snmWorkList :: Set (Node, Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p,x), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' = if (not $ m ∊ toNextCond x) then (Set.insert (p,x) smp) else smp
                    influenced = if (Set.size smp == 0 && Set.size smp' > 0)
                                   then Set.fromList [ (m,n,x') | (n,x') <- prevCondsWithSucc p ]
                                   else Set.empty

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- condNodes, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, not $ m ∊ reachable x]) | p <- condNodes, m <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        toNextCond = toNextCondNode graph
        prevCondsWithSucc = prevCondsWithSuccNode graph
        trncl = trc graph


{- the same, with less memory consumption -}
-- here, for given node node m, S[m,p] is represented by S[m',p] for that condition or join node m'
-- which preceeds  m in the graph (or: m itself, if there is no such node)
nticdF3'dualWorkListSymbolicGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'dualWorkListSymbolicGraphP = cdepGraphP nticdF3'dualWorkListSymbolicGraph

nticdF3'dualWorkListSymbolicGraph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3'dualWorkListSymbolicGraph = cdepGraph nticdF3'dualWorkListSymbolic

nticdF3'dualWorkListSymbolic :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3'dualWorkListSymbolic = ntXcd snmF3'dualWorkListSymbolicLfp

snmF3'dualWorkListSymbolicLfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3'dualWorkListSymbolicLfp graph = snmWorkList (Set.fromList [ (m,n,x) | p <- condNodes, m <- representants, Set.size (smnInit ! (m,p)) /= 0, (n,x) <- prevCondsWithSucc p ]) smnInit
  where snmWorkList :: Set (Node, Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = expandSymbolic s
          | otherwise         = snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p,x), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' = if (not $ m ∊ toNextCond x) then (Set.insert (p,x) smp) else smp
                    influenced = if (Set.size smp == 0 && Set.size smp' > 0)
                                   then Set.fromList [ (m,n,x') | (n,x') <- prevCondsWithSucc p ]
                                   else Set.empty

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- condNodes, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, not $ m ∊ reachable x]) | p <- condNodes, m <- representants]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        prevCondsWithSucc = prevCondsWithSuccNode graph
        representantOf = prevRepresentantNodes graph
        representants = [ m | m <- nodes graph, (length (pre graph m) /= 1) ∨ (let [n] = pre graph m in n ∊ condNodes)]
        trncl = trc graph
        expandSymbolic s = Map.fromList [ ((m,p), s ! (r, p)) | p <- condNodes, m <- nodes graph, Just r <- [representantOf m]]
                         ⊔ Map.fromList [ ((m,p), Set.empty)  | p <- condNodes, m <- nodes graph, Nothing == representantOf m]

{- A Worklist-Implementation of nticd, based on f3 -}
nticdF3WorkListGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3WorkListGraphP = cdepGraphP nticdF3WorkListGraph

nticdF3WorkListGraph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3WorkListGraph = cdepGraph nticdF3WorkList

nticdF3WorkList :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3WorkList = ntXcd snmF3WorkListGfp

snmF3WorkListGfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3WorkListGfp graph = snmWorkList (Set.fromList [ (m,p) | p <- condNodes, m <- reachable p]) smnInit
  where snmWorkList :: Set (Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = assert (smp' ⊆  smp) $
                                snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' = lin  ⊔ cond
                    lin  = Set.fromList  [ (p,x) | x <- (suc graph p), m ∊ toNextCond x]
                    cond = Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x],
                                                     (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                           ]
                    influenced = if  (Set.size smp /=  (Set.size $ Set.fromList $ suc graph p))
                                   ∨ (Set.size smp == Set.size smp')
                                   then Set.empty
                                   else Set.fromList [ (m,n) | n <- prevConds p ]

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, m ∊ reachable x]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        prevConds = prevCondNodes graph
        trncl = trc graph

{- the same, with less memory consumption -}
-- here, for given node node m, S[m,p] is represented by S[m',p] for that condition or join node m'
-- which preceeds  m in the graph (or: m itself, if there is no such node)
nticdF3WorkListSymbolicGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3WorkListSymbolicGraphP = cdepGraphP nticdF3WorkListSymbolicGraph

nticdF3WorkListSymbolicGraph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3WorkListSymbolicGraph = cdepGraph nticdF3WorkListSymbolic

nticdF3WorkListSymbolic :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3WorkListSymbolic = ntXcd snmF3WorkListSymbolicGfp

snmF3WorkListSymbolicGfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3WorkListSymbolicGfp graph = snmWorkList (Set.fromList [ (m,p) | p <- condNodes, m <- representants  ]) smnInit
  where snmWorkList :: Set (Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = expandSymbolic s
          | otherwise         = snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' =   Set.fromList  [ (p,x) | x <- (suc graph p), m ∊ toNextCond x]
                           ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x],
                                                     (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                           ]
                    influenced = if (Set.size smp == Set.size smp')
                                   then Set.empty
                                   else Set.fromList [ (m,n) | n <- prevConds p ]
--                                 else Set.fromList [ (m,n) | n <- condNodes, x <- (suc graph n), Just p == nextCond x ]

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- condNodes, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, m ∊ reachable x]) | p <- condNodes, m <- representants]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        prevConds = prevCondNodes graph
        representantOf = prevRepresentantNodes graph
        representants = [ m | m <- nodes graph, (length (pre graph m) /= 1) ∨ (let [n] = pre graph m in n ∊ condNodes)]
        trncl = trc graph
        expandSymbolic s = Map.fromList [ ((m,p), s ! (r, p)) | p <- condNodes, m <- nodes graph, Just r <- [representantOf m]]
                         ⊔ Map.fromList [ ((m,p), Set.empty)  | p <- condNodes, m <- nodes graph, Nothing == representantOf m]



{- A correct implementation of ntscd, as given in [1], Figure 4,
   using the lfp of functional f4
-}
ntscdF4GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF4GraphP p = cdepGraphP ntscdF4Graph p

ntscdF4Graph :: DynGraph gr => gr a b -> gr a Dependence
ntscdF4Graph = cdepGraph ntscdF4 

ntscdF4 :: DynGraph gr => gr a b -> Map Node (Set Node)
ntscdF4 = ntXcd snmF4

snmF4 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF4 graph = snmLfp graph f4

f4 graph condNodes _ _ _ s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $
                   Map.fromList [ ((x,p), Set.fromList [ (p,x) ]) | p <- condNodes, x <- suc graph p ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- condNodes, p /= n,
                                                             (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]



snmF4WithReachCheckGfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF4WithReachCheckGfp graph = snmGfp graph f4withReachCheck

f4withReachCheck graph condNodes reachable _ _ s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $
                   Map.fromList [ ((x,p), Set.fromList [ (p,x) ]) | p <- condNodes, x <- suc graph p ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ Set.fromList [ (p,x) | (p',x) <- Set.toList $ s ! (n,p),
                                                                       assert (p == p') True,
                                                                       m ∊ reachable x
                                                ]
                                              | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ Set.fromList [ (p,x) | (p',x) <- Set.toList $ s ! (n,p),
                                                                       assert (p == p') True,
                                                                       m ∊ reachable x
                                                ]
                                              | n <- condNodes, p /= n, (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)]
                                  ) | m <- nodes graph, p <- condNodes ]



{- A correct implementation of ntscd, by a tiny modification of [1], Figure 4 -}
ntscdF4WorkListGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF4WorkListGraphP = cdepGraphP ntscdF4WorkListGraph

ntscdF4WorkListGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdF4WorkListGraph = cdepGraph ntscdF4WorkList

ntscdF4WorkList :: DynGraph gr => gr a b -> Map Node (Set Node)
ntscdF4WorkList = ntXcd snmF4WorkListLfp

snmF4WorkListLfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF4WorkListLfp graph = snmWorkList (Set.fromList [ m | n <- condNodes, m <- suc graph n ]) smnInit
  where snmWorkList :: Set (Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ workList') s'
              where (n, workList') = Set.deleteFindMin workList
                    tn = Set.size $ Set.fromList $ suc graph n
                    s'
                     | tn == 1   = let [m] = nub $ suc graph n in     s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) |                                                 p <- condNodes ]
                     | tn  > 1   =                                    s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes ]
                     | otherwise = s 
                    influenced 
                     | tn == 1   = let [m] = nub $ suc graph n in  Set.fromList [ m |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | tn  > 1   =                                 Set.fromList [ m | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | otherwise = Set.empty
        smnInit =  Map.fromList [ ((m,n), Set.empty)              | n <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


{- A faulty implementation of ntscd, as given in [1], Figure 4 -}
ntscdFig4GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdFig4GraphP = cdepGraphP ntscdFig4Graph

ntscdFig4Graph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdFig4Graph = cdepGraph ntscdFig4

ntscdFig4 :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntscdFig4 = ntXcd snmFig4Lfp

snmFig4Lfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmFig4Lfp graph = snmWorkList (Set.fromList [ m | n <- condNodes, m <- suc graph n ]) smnInit
  where snmWorkList :: Set (Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ workList') s'
              where (n, workList') = Set.deleteFindMin workList
                    tn = Set.size $ Set.fromList $ suc graph n
                    s'
                     | tn == 1   = let [m] = nub $ suc graph n in     s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) |                                                 p <- condNodes ]
                     | tn  > 1   =                                    s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes ]
                     | otherwise = s 
                    influenced 
                     | tn == 1   = let [m] = nub $ suc graph n in  Set.fromList [ m |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                     | tn  > 1   =                                 Set.fromList [ m | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                     | otherwise = Set.empty
        smnInit =  Map.fromList [ ((m,n), Set.empty)              | n <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



{- A faulty implementation of nticd, as given in [1], Figure 5, with attempts to fix the worklist updates  -}
nticdFig5GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdFig5GraphP = cdepGraphP nticdFig5Graph

nticdFig5Graph :: DynGraph gr => gr a b ->  gr a Dependence
nticdFig5Graph = cdepGraph nticdFig5

nticdFig5 :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdFig5 = ntXcd snmFig5Lfp

snmFig5Lfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmFig5Lfp graph = snmWorkList (Set.fromList [ m | n <- condNodes, m <- suc graph n ]) smnInit
  where snmWorkList :: Set (Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ influenced2 ⊔ workList') s''
              where (n, workList') = Set.deleteFindMin workList
                    tn = Set.size $ Set.fromList $ suc graph n
                    s'
                     | tn == 1   = let [m] = nub $ suc graph n in     s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) |                                                 p <- condNodes ]
                     | tn  > 1   =                                    s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes ]
                     | otherwise = s
                    influenced
                     | tn == 1   = let [m] = nub $ suc graph n in  Set.fromList [ m |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | tn  > 1   =                                 Set.fromList [ m | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | otherwise = Set.empty

                    s''
                     | n ∊ condNodes ∧ (Set.size $ s' ! (n,n)) > 0  =  s' ⊔  Map.fromList [ ((m,n),                               s' ! (m,n)  ⊔  s' ! (n,n)) | m <- suc graph n, m /= n]
                     | otherwise = s'
                    influenced2
                     | n ∊ condNodes ∧ (Set.size $ s' ! (n,n)) > 0  =  Set.fromList [m | m <- suc graph n, m /= n, s' ! (m,n) /=  s' ! (m,n)  ⊔  s' ! (n,n)]
                                                                          ⊔ Set.fromList [n | m <- suc graph n, m /= n, s' ! (m,n) /=  s' ! (m,n)  ⊔  s' ! (n,n)] -- this is missing in their paper
                     | otherwise = Set.empty

        smnInit =  Map.fromList [ ((m,n), Set.empty)              | n <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



{- A correct implementation of ntscd,
   using the lfp of functional f3.

   This shows that ntscd and nticd are, essentially, the lfp/gfp (respectively) of the *same* functional f3.
-}
ntscdF3GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF3GraphP = cdepGraphP ntscdF3Graph

ntscdF3Graph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdF3Graph = cdepGraph ntscdF3

ntscdF3 :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntscdF3 = ntXcd snmF3Lfp

snmF3Lfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3Lfp graph = snmLfp graph f3


nticdSinkContractionGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdSinkContractionGraphP p = cdepGraphP nticdSinkContractionGraph p 
  where  [endNodeLabel] = newNodes 1 $ tcfg p

nticdSinkContractionGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdSinkContractionGraph = cdepGraph nticdSinkContraction

nticdSinkContraction :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdSinkContraction graph              = Map.fromList [ (n, cdepClassic ! n) | n <- nodes graph, not $ n ∈ sinkNodes ]
                                        ⊔ Map.fromList [ (n, (∐) [ Set.fromList sink | s <- Set.toList $ cdepClassic ! n,
                                                                                        s ∈ sinkNodes,
                                                                                        let sink = the (s ∊) sinks ]
                                                         ) | n <- nodes graph, not $ n ∈ sinkNodes
                                                       ]
                                        ⊔ Map.fromList [ (n, Set.empty) | n <- Set.toList sinkNodes ]
    where [endNode] = newNodes 1 graph
          sinks = controlSinks graph
          cdepClassic = controlDependence (sinkShrinkedGraph graph endNode) endNode
          sinkNodes   = Set.fromList [ x | sink <- sinks, x <- sink]

sinkShrinkedGraph :: DynGraph gr => gr a b  -> Node -> gr () ()
sinkShrinkedGraph graph endNode   = mkGraph (  [ (s,())   | sink <- sinks, let s = head sink]
                                            ++ [ (n,())   | n    <- nodes graph, not $ n ∈ sinkNodes ]
                                            ++ [ (endNode, ()) ]
                                          )
                                          (
                                               [ (n,s,())       | sink <- sinks, let s = head sink, s' <- sink, n <- pre graph s', not $ n ∊ sink]
                                            ++ [ (s,endNode,()) | sink <- sinks, let s = head sink ]
                                            ++ [ (n,m,()) | (n,m) <- edges graph, not $ n ∈ sinkNodes, not $ m ∈ sinkNodes ]
                                          )
    where sinkNodes   = Set.fromList [ x | sink <- sinks, x <- sink]
          sinks = controlSinks graph




nticdIndusGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdIndusGraphP = cdepGraphP nticdIndusGraph

nticdIndusGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdIndusGraph = cdepGraph nticdIndus

nticdIndus :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdIndus graph = go (nodes graph) [] deps
    where
      go []             seen newDeps = newDeps
      go (dependent:ds) seen newDeps = go ds seen newDeps'
        where newDeps' = process dependent newDeps
      process dependent newDeps = run dependent [ d | d <- nodes graph, dependent ∈ (deps ! d)] [] newDeps
        where 
          run dependent []            seen newDeps = newDeps
          run dependent (dependee:ds) seen newDeps
            | dependee ∊ seen                                       = run
                dependent
                ds
                seen
                newDeps
            | shouldRemoveDepBetween dependee dependent sinkNodes = run
                dependent
                (ds ++ [ d | d <- nodes graph, dependee ∈ (deps ! d) ])
                (dependee:seen)
                (Map.update (\dependents -> Just $ Set.delete  dependent  dependents) dependee newDeps)
            | otherwise               = run
                dependent
                ds
                (dependee:seen)
                (Map.update (\dependents -> Just $ Set.insert dependent  dependents) dependee newDeps)
          sinkNodes = nodesOfSinksNotContainingNode dependent
      
      deps = ntscdF4 graph
      csinks = controlSinks graph
      nodesOfSinksNotContainingNode node = [ n | sink <- csinks, not $ node ∊ sink, n <- sink]
      shouldRemoveDepBetween dependee dependent sinkNodes = run [dependee] [dependent]
        where run []     seen = True
              run (n:ns) seen
                | n ∊ seen   = run ns seen
                | n ∊ sinkNodes = False
                | otherwise = run ((suc graph n) ++ ns) (n:seen)



{- The definition of nticd -}
nticdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdDefGraphP = cdepGraphP nticdDefGraph

nticdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdDefGraph  = cdepGraph nticdDef

nticdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph, nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inPath` (nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inPath` (nl,path))
                                         ]
                       )
                     | ni <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inPath = inSinkPathFor graph

inSinkPathFor graph' n (s, path) = inSinkPathFromEntries [s] path
  where 
    inSinkPathFromEntries _       (SinkPath []           controlSink) = n ∊ controlSink
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n ∊ scc = (∀) entries (\entry -> let doms = (dom graph' entry) in
                          (∀) exits (\exit -> let domsexit = doms `get` exit in
                                 (entry /= exit || n == entry) && n ∊ domsexit)
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
            exits = [ n | (n,_) <- borderEdges ]
            get assocs key = fromJust $ List.lookup key assocs



{- The definition of ntscd -}
ntscdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdDefGraphP = cdepGraphP ntscdDefGraph

ntscdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdDefGraph  = cdepGraph ntscdDef

ntscdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntscdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (maximalPaths ! nk) (\path ->       nj `inPath` (nk,path)),
                                                (∃) (maximalPaths ! nl) (\path -> not $ nj `inPath` (nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.

inPathFor graph' doms n (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  (MaximalPath []            endScc endNodes@(end:_))
                    | n ∊ endScc  = (∀) entries (\entry -> let domsEnd = (doms ! entry) `get` end in
                                                                (entry /= end || n == entry) && n ∊ domsEnd
                                         )
                                       ∨ (n ∊ endNodes)
                    | otherwise =  False
                inPathFromEntries entries  (MaximalPath (scc:prefix)  endScc endNodes)
                    | n ∊ scc = (∀) entries (\entry ->
                                      (∀) exits (\exit -> let domsexit = (doms ! entry) `get` exit in
                                             (entry /= exit || n == entry) && n ∊ domsexit)
                                     )
                                     ∨ (n ∊ endNodes)
                    | otherwise    =  inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = fromJust $ List.lookup key assocs




{- The definition of ntacd -}
ntacdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntacdDefGraphP = cdepGraphP ntacdDefGraph

ntacdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntacdDefGraph  = cdepGraph ntacdDef

ntacdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntacdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inSinkPathAfter` (ni,nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inSinkPathAfter` (ni,nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where 
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inSinkPathAfter = inSinkPathAfterFor graph


{- The definition of ntbcd -}
ntbcdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntbcdDefGraphP = cdepGraphP ntbcdDefGraph

ntbcdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntbcdDefGraph  = cdepGraph ntbcdDef

ntbcdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntbcdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inSinkPathAfter'` (ni,nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inSinkPathAfter'` (ni,nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where 
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inSinkPathAfter' = inSinkPathAfterFor' graph


inSinkPathAfterFor :: DynGraph gr => gr a b -> Node -> (Node, Node, SinkPath) -> Bool
inSinkPathAfterFor graph' n (cond, s, path) = inSinkPathFromEntries [s] path
  where 
    inSinkPathFromEntries _       (SinkPath []           controlSink) = n ∊ controlSink ∧ (
                          (  (not $ cond ∊ controlSink) -- ∧
                             -- ((∀) (cyclesInScc  controlSink graph') (\cycle -> n ∈ cycle))
                          )
                        ∨ (  (cond ∊ controlSink) ∧
                             (s == cond ∨ n ∊ (suc withoutCondTrc s))
                          )
                      )
      where withoutCondTrc = trc $ delNode cond graph'
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n ∊ scc = -- traceShow (s, n, cond, entries, scc, controlSink) $ 
                         (True) ∧ (
--                         (not (cond ∈ scc) ∨ (n ∊ (suc (trc $ delNode cond graph') s)  )  ∨ (s == cond) ) ∧ (
                           (∀) entries (\entry -> let doms = (dom graph' entry) in
                            (∀) exits (\exit -> let domsexit = doms `get` exit in
                                   (entry /= exit || n == entry) && n ∊ domsexit)
                           )
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
            exits = [ n | (n,_) <- borderEdges ]
            get assocs key = fromJust $ List.lookup key assocs



inSinkPathAfterFor' :: DynGraph gr => gr a b -> Node -> (Node, Node, SinkPath) -> Bool
inSinkPathAfterFor' graph' n (cond, s, path) = inSinkPathFromEntries [s] path
  where
    get assocs key = fromJust $ List.lookup key assocs
    inSinkPathFromEntries entries (SinkPath []           controlSink) = n ∊ controlSink ∧ (
                          (  (not $ cond ∊ controlSink) ∧ (
                              ((∀) entries (\entry -> let doms = dom graph' entry in
                                (∀) cycles  (\cycle -> let c = head cycle in
                                  (n ∊ cycle) ∨ (n ∊ (doms `get` c))
                                )
                               )
                              )
                             )
                          )
                        ∨ (  (cond ∊ controlSink) ∧ (∀) entries (\entry -> 
                             (entry == cond ∨ n ∊ (suc withoutCondTrc entry))
                          ))
                      )
      where withoutCondTrc = trc $ delNode cond graph'
            cycles = (cyclesInScc  controlSink graph')
--     inSinkPathFromEntries entries (SinkPath []           controlSink) =
--                              (∀) entries (\entry -> 
--                                (∀) (nrPaths (initial entry) entry ) (\path ->  (n ∈ path))
--                              )
-- -- (Set.fromList path == Set.fromList controlSink) →
--       where cycles = (cyclesInScc  controlSink graph')
--             initial entry = Map.fromList [ (m, Set.empty) | m <- controlSink ]
--                           ⊔ Map.fromList [ (x, Set.fromList [(x,entry)]) | x <- controlSink, x ∈ pre graph' entry ]
--             nrPaths :: Map Node (Set (Node,Node)) -> Node -> [[Node]]
--             nrPaths taken n
--              | Set.null allowedEdges      = [[n]]
--              | otherwise                  = -- traceShow taken $
--                                             [ n:p | m <- Set.toList $ Set.map snd $ allowedEdges,
--                                                     p <- nrPaths (Map.adjust (\taken -> Set.insert (n,m) taken ) n taken) m  ]
--                where allowedEdges = (Set.fromList $ [(n,m) | m <- suc graph' n]) ∖ (taken ! n)

            
    -- inSinkPathFromEntries entries (SinkPath []           controlSink) =
    --                          (∀) entries (\entry -> (entry == cond) ∨
    --                            n ∈ (suc (trc $ delEdges ([(cond, x) | x <- suc graph' cond]) graph') entry)
    --                          )
    --   where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries entries  (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) entries (\entry -> let doms = dom graph' entry in
    --                            (∀) cycles  (\cycle -> let c = head cycle in
    --                              (s ∈ cycle) ∨ (n ∈ cycle) ∨ (n ∊ (doms `get` c))
    --                            )
    --                           )
    --                          )
    --                         )
    --   where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries entries  (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) entries (\entry -> let doms = dom graph' entry in
    --                            (∀) cycles  (\cycle -> let c = head cycle in
    --                               (s == cond) ∨ ((cond ∈ cycle) → (n ∈ cycle) ∨ (n ∊ (doms `get` c)))
    --                            )
    --                           )
    --                          )
    --                         )
    --  where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries _       (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) (cyclesInScc  controlSink graph') (\cycle -> (s ∈ cycle) ∨ (n ∈ cycle)))
    --                       )
    -- inSinkPathFromEntries entries       (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) (cyclesInScc  controlSink graph') (\cycle ->
    --                            ((∃) entries (∈ cycle)) → (s ∈ cycle) ∨ (n ∈ cycle)))
    --                       )
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n ∊ scc = -- traceShow (s, n, cond, entries, scc, controlSink) $ 
                         (True) ∧ (
--                         (not (cond ∈ scc) ∨ (n ∊ (suc (trc $ delNode cond graph') s)  )  ∨ (s == cond) ) ∧ (
                           (∀) entries (\entry -> let doms = (dom graph' entry) in
                            (∀) exits (\exit -> let domsexit = doms `get` exit in
                                   (entry /= exit || n == entry) && n ∊ domsexit)
                           )
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
            exits = [ n | (n,_) <- borderEdges ]




{- The definition of ntnrcd -}
ntnrcdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntnrcdDefGraphP = cdepGraphP ntnrcdDefGraph

ntnrcdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntnrcdDefGraph  = cdepGraph ntnrcdDef

ntnrcdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntnrcdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph, nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (nrPaths ! (ni,nk)) (\path ->       nj `inPath` path),
                                                (∃) (nrPaths ! (ni,nl)) (\path -> not $ nj `inPath` path)
                                         ]
                       )
                     | ni <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        nrPaths = nrPathsFor graph
        inPath n (NrPath { path }) = n ∊ path

data NrPath = NrPath { path :: [Node] } deriving Show

nrPathsFor :: DynGraph gr => gr a b -> Map (Node,Node) [NrPath]
nrPathsFor graph = Map.fromList [ ((n,m), fmap (\p -> NrPath { path = p }) $ nrPathsFor (n,m)) | n <- nodes graph, m <- suc graph n ]
    where
      nrPathsFor :: (Node,Node) -> [[Node]]
      nrPathsFor (n,m) = nrPaths (forbidden (n,m)) (initial (n,m)) m
      initial (n,m)   = Map.fromList [(n, Set.empty) | n <- nodes graph]
--                  ⊔ Map.fromList [(n, Set.fromList $ [ (n,m) ]) ]
      forbidden (n,m) = Set.fromList $ [ (n,m) ] 
--      forbidden (n,m) = Map.fromList [(x, Set.fromList $ [ (x,n) ]) |  x <- pre graph n ]
--      nrPathsF taken ns = concat $ fmap (nrPaths taken) ns
      nrPaths :: Set (Node, Node) -> Map Node (Set (Node,Node)) -> Node -> [[Node]]
      nrPaths forbidden taken n
--       | Set.null allowedEdges  ∧  (not $ Set.null $ (Set.fromList  [(n,m) | m <- suc graph n]) ⊓ forbidden)  = []
       | Set.null allowedEdges  ∧  (not $ Set.null $ (Set.fromList  [(n,m) | m <- suc graph n]) ⊓ (forbidden ∖ (taken ! n)))  = []
       | Set.null allowedEdges                                                                                                = [[n]]
       | otherwise                  = -- traceShow taken $
                                      [ n:p | m <- Set.toList $ Set.map snd $ allowedEdges,
                                              p <- nrPaths forbidden (Map.adjust (\taken -> Set.insert (n,m) taken ) n taken) m  ]
        where allowedEdges = (Set.fromList $ [(n,m) | m <- suc graph n]) ∖ (taken ! n)




mdomOf ::  DynGraph gr => gr a b -> Map Node (Set Node)
mdomOf graph = -- trace ("Sccs: " ++ (show $ length sccs) ++ "\t\tSize: " ++ (show $ length $ nodes graph)) $
               Map.fromList [ (y, Set.fromList [ x | x <- nodes graph, x `mdom` y]) | y <- nodes graph]
  where mdom x y =  (∀) (maximalPaths ! y) (\path ->       x `inPath` (y,path))
        maximalPaths = maximalPathsForNodes graph (nodes graph)
        inPath = inPathFor graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ]
        sccs = scc graph
        sccOf m =  the (m ∊) $ sccs

sinkdomOf ::  DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOf graph = Map.fromList [ (y, Set.fromList [ x | x <- nodes graph, x `sinkdom` y]) | y <- nodes graph]
  where sinkdom x y =  (∀) (sinkPaths ! y) (\path ->       x `inPath` (y,path))
        sinkPaths = sinkPathsFor graph
        inPath = inSinkPathFor graph



type DomFunctional = Map Node (Set Node) ->  Map Node (Set Node)
type DomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> DomFunctional

domOfLfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
domOfLfp graph f = (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

domOfGfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
domOfGfp graph f = (𝝂) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
             ⊔ Map.fromList [ (y, Set.fromList $ reachable y) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph


joiniSinkDomAround g n imdom imdomrev = fmap (\s -> if Set.null s then Set.fromList [m] else s) $
        Map.fromList [ (m, Set.empty) | m <- nodes g, m /= n]
     ⊔  fwd ⊔ bwd
  where forward n seen
            | Set.null n's = (n, Map.empty,                                     seen     )
            | otherwise    = (m, Map.fromList [ (n', Set.fromList [n]) ] ⊔ fwd, seenfinal)
          where seen' = seen ∪ n's
                n's = (imdom ! n) ∖ seen
                [n'] = Set.toList n's
                (m,fwd,seenfinal) = forward n' seen' 
        (m,fwd,seen) = forward n (Set.fromList [n])
        bwd = backward m ((Set.fromList [m]) ⊔ seen)
        backward n seen = Map.fromList [ (n', Set.fromList [n] ) | n' <- Set.toList n's ] ⊔ (∐) [backward n' seen' | n' <- Set.toList n's]
          where seen' = seen ∪ n's
                n's = (imdomrevInv ! n) ∖ seen
        imdomrevInv = Map.fromList [ (n, Set.empty) | n <- Map.keys imdomrev ]
                    ⊔ invert'' imdomrev
        -- imdomrevInv = (∐) [ Map.fromList [ (m, Set.fromList [n]) ]  | n <- nodes g, let preds = pre g n, (Set.size $ Set.fromList preds) == 1, m <- preds ]
        --                   ⊔  Map.fromList [ (m, Set.empty) | m <- nodes g]
        -- imdomrevInv = Map.fromList [ (m, Set.empty) | m <- nodes g]


-- joiniSinkDomAround g n imdom imdomrev = fmap (\s -> if Set.null s then Set.fromList [n] else s) $
--         Map.fromList [ (m, Set.empty) | m <- nodes g, m /= n]
--      ⊔  backward n (Set.fromList [n])
--   where backward n seen = Map.fromList [ (n', Set.fromList [n] ) | n' <- Set.toList n's ] ⊔ (∐) [backward n' seen' | n' <- Set.toList n's]
--           where seen' = seen ∪ n's
--                 n's = (imdomrevInv ! n ∪ imdom ! n) ∖ seen
--         imdomrevInv = Map.fromList [ (n, Set.empty) | n <- Map.keys imdomrev ]
--                     ⊔ invert'' imdomrev
--         -- imdomrevInv = (∐) [ Map.fromList [ (m, Set.fromList [n]) ]  | n <- nodes g, let preds = pre g n, (Set.size $ Set.fromList preds) == 1, m <- preds ]
--         --                   ⊔  Map.fromList [ (m, Set.empty) | m <- nodes g]
--         -- imdomrevInv = Map.fromList [ (m, Set.empty) | m <- nodes g]


fSinkDom graph _ _ nextCond toNextCond = f 
  where f sinkdomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Set.fromList $ toNextCond y)               | y <- nodes graph]
                    ⊔ Map.fromList [ (y,  (∏) [ sinkdomOf ! x | x <- suc graph n ]) | y <- nodes graph, Just n <- [nextCond y]]
sinkdomOfGfp graph = domOfGfp graph fSinkDom
mdomOfLfp graph = domOfLfp graph fSinkDom



fSinkDomNaive graph _ _ nextCond toNextCond = f 
  where f sinkdomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y,  (∏) [ sinkdomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]
sinkdomNaiveGfp graph = domOfGfp graph fSinkDomNaive
mdomNaiveLfp graph = domOfLfp graph fSinkDomNaive


traceIfFalse x b =
  if b then b else traceShow x $ b

roflDomDef graph = Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                                                        -- (∀) (nodes graph) (\n ->
                                                        --                             y ∈                                       doms ! n               ! m
                                                        --                           ∨ m ∈ (reachableFrom (                      doms ! n) (Set.fromList [y]) Set.empty)
                                                        -- )
                                                        (∀) (nodes graph) (\n ->
                                                                                    y ∈ (reachableFrom (                      doms ! n) (Set.fromList [m]))
                                                                                  ∨ m ∈ (reachableFrom (                      doms ! n) (Set.fromList [y]))
                                                        )
                                                        -- (∃) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)),
                                                        -- (∀) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)   ∨  (n == m)   ∨   y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty))
                                                        -- (∃) (nodes graph) (\n -> m ∈ doms ! n ! y),
                                                        -- (∀) (nodes graph) (\n -> m ∈ doms ! n ! y   ∨   y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ doms ! n ! y )
                                                        -- (∃) (nodes graph) (\n -> n /= m   ∧   m ∈ doms ! n ! y ),
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ (reachableFrom (doms ! n) (Set.fromList [y]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨     (not $ y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty)))
                                      ]
                                  ) | y <- nodes graph ]
   where doms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]
         pdoms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]

lolDomDef graph0 = Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,

                                                        -- (∀) (nodes graph) (\n ->
                                                        --                             n ∈ (reachableFrom (                      doms ! y) (Set.fromList [m]) Set.empty)
                                                        --                           ∨ m ∈                                       doms ! y               ! n
                                                        -- )
                                                        (∀) (nodes graph) (\n ->
                                                                                    n ∈ (reachableFrom (                      doms ! y) (Set.fromList [m]))
                                                                                  ∨ m ∈ (reachableFrom (                      doms ! y) (Set.fromList [n]))
                                                        )
                                                     -- (∀) (nodes graph) (\n ->
                                                     --                                (                                m ∈ (reachableFrom (                      pdoms ! n) (Set.fromList [y]) Set.empty))
                                                     --                              ∨ ( (∃) (suc graph y) (\x -> not $ n ∈ (reachableFrom (                      pdoms ! y) (Set.fromList [x]) Set.empty)))
                                                     --                                 ∧                  (      not $ n ∈ (reachableFrom (                      pdoms ! m) (Set.fromList [y]) Set.empty))
                                                     --                              ∨ ( y == n)
                                                     -- )
                                                        -- (∀) (nodes graph) (\n ->
                                                        --                             n ∈ (reachableFrom (                      pdoms ! m) (Set.fromList [y]) Set.empty)
                                                        --                             -- y ∈ (reachableFrom (fmap (Set.delete n) $ doms ! n) (Set.fromList [m]) Set.empty)
                                                        --                           ∨ m ∈ (reachableFrom (                      pdoms ! n) (Set.fromList [y]) Set.empty)
                                                        --                           -- ∨ m ∈ (reachableFrom (fmap (Set.delete n) $ doms ! n) (Set.fromList [y]) Set.empty)
                                                        -- )
                                                        -- (∃) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)),
                                                        -- (∀) (nodes graph) (\n -> traceIfFalse (y,m,n, doms ! n) $ (n /= m   ∧   m ∈ doms ! n ! y)   ∨   ( n == y )  ∨    m ∈ (reachableFrom (doms ! n) (Set.fromList [y]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ doms ! n ! y )
                                                        -- (∃) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)),
                                                        -- (∀) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)   ∨  (n == m)   ∨   y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty))
                                                        -- (∃) (nodes graph) (\n -> n /= m   ∧   m ∈ doms ! n ! y ),
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ (reachableFrom (doms ! n) (Set.fromList [y]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨     (not $ y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty)))
                                      ]
                                  ) | y <- nodes graph ]
   where  graph = grev graph0
          pdoms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]
          doms  = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph0 n)
                               )
                             | n <- nodes graph ]


omegaLulDomDef graph = Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                                                             -- (∃) (nodes graph) (\m' -> m ∈ doms ! y ! m')
                                                              (∀) (suc graph y) (\x -> 
                                                                                    m ∈ (reachableFrom (                      pdoms ! y) (Set.fromList [x]))
                                                              )
                                      ]
                                  ) | y <- nodes graph ]
   where  pdoms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graphRev n)
                               )
                             | n <- nodes graph ]
            where graphRev = grev graph
          doms  = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]


fRoflDomNaive graph _ _ nextCond toNextCond = f 
  where f rofldomOf =
                      Map.fromList [ (y, Set.fromList [y])                           | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                                                            before m  (Set.fromList $ pre graph y) (Set.fromList $ pre graph y ++ [y])
                                                      ]
                                     )
                                   | y <- nodes graph, pre graph y/= []]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                    --                                         (∀) (pre graph y) (\x ->   (x == y)
                    --                                                                  ∨ (m ∈ rofldomOf ! x   ∧  (m == x   ∨   (not $ x `elem` pre graph m)))
                    --                                                           )
                    --                                   ]
                    --                  )
                    --                | y <- nodes graph, pre graph y/= []]
                    -- ⊔ Map.fromList [ (x,  (∏) [ rofldomOf ! p | p <- pre graph x])   | x <- nodes graph, pre graph x/= []]
                     ⊔ Map.fromList [ (x, Set.fromList [p] ) | x <- nodes graph, [p] <- [nub $ pre graph x]]
                    -- ⊔ Map.fromList [ (x,  (∏) [ rofldomOf ! p | p <- pre graph x, p ∈ rofldomOf ! x ]) | x <- nodes graph, [ p | p <- pre graph x, p ∈ rofldomOf ! x ] /= []]
        before m xs seen = traceShow  (m, xs, seen, bef xs seen) $ bef xs seen
          where bef xs seen
                    | Set.null xs = True
                    | m ∈ xs      = False
                    | otherwise = bef new (seen ∪ new) 
                  where new = Set.fromList [ x' | x <- Set.toList xs, x' <- suc graph x,  not  $ x' ∈ seen]

rofldomNaiveGfp graph = domOfGfp graph fRoflDomNaive
rofldomNaiveLfp graph = domOfLfp graph fRoflDomNaive



rofldomOfTwoFinger7 :: forall gr a b. (DynGraph gr, Eq b) => gr a b -> Map Node (Set Node)
rofldomOfTwoFinger7 graph0 = Map.mapWithKey (\n ms -> Set.delete n ms) $
                          fmap toSet $ twoFinger 0 worklist0 rofldom0
  where graph = removeDuplicateEdges $ delEdges [ e | e@(n,m) <- edges graph0, n == m] $ graph0
        rofldom0   =           Map.fromList [ (x, Just z   ) | x <- nodes graph, [z] <- [pre graph x], z /= x]
                   `Map.union` Map.fromList [ (x, Nothing  ) | x <- nodes graph]
        worklist0   = condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (pre graph x) > 1 ]
        prevConds   = prevCondNodes graph
        nextCond    = nextCondNode graph

        twoFinger :: Integer -> Set Node ->  Map Node (Maybe Node) -> Map Node (Maybe Node)
        twoFinger i worklist rofldom
            |   Set.null worklist = -- traceShow ("x", "mz", "zs", "influenced", worklist, rofldom) $
                                    -- traceShow (Set.size worklist0, i) $ 
                                    rofldom
            | otherwise           = -- traceShow (x, mz, zs, influenced, worklist, rofldom) $
--                                    traceShow (x, influenced, influenced', rofldom) $
                                    if (not $ new) then twoFinger (i+1)                worklist'                                   rofldom
                                    else                twoFinger (i+1) (influenced' ⊔ worklist')  (Map.insert x zs                rofldom)
          where (x, worklist')  = Set.deleteFindMin worklist
                mz = foldM1 (lca rofldom) [ y | y <- pre graph x]
                -- mz = foldM1 lca (pre graph x)
                zs = case mz of
                      Just z  -> if z/= x then
                                   find z (Set.fromList [z])
                                 else
                                   Nothing
                      Nothing ->  Nothing
                  where find z seen
                          | (∀) (pre graph x) (\y -> not $ y `elem` pre graph z) = Just z
                          | otherwise = let z' = rofldom ! z in case z' of
                              Nothing -> Nothing
                              Just z' -> if z' ∈ seen then Nothing else find z' (Set.insert z' seen)
                          
                new     = assert (isNothing $ rofldom ! x) $
                          (not $ isNothing zs)
                influenced' = Set.fromList [ n | (n,Nothing) <- Map.assocs rofldom, n /= x]


fLolDomNaive graph _ _ nextCond toNextCond = f 
  where f loldomOf =
                         Map.fromList [ (x, Set.fromList [ m | m <- nodes graph, (∃) (pre graph x) (\p -> p /= m   ∧   m ∈ loldomOf ! p)] ) | x <- nodes graph ]
                    -- ⊔ Map.fromList [ (x,  (∏) [ loldomOf ! p | p <- pre graph x])   | x <- nodes graph, pre graph x/= []]
                    -- ⊔ Map.fromList [ (x, Set.fromList [p] ) | x <- nodes graph, [p] <- [nub $ pre graph x]]
                    -- ⊔ Map.fromList [ (x,  (∏) [ loldomOf ! p | p <- pre graph x, p ∈ loldomOf ! x ]) | x <- nodes graph, [ p | p <- pre graph x, p ∈ loldomOf ! x ] /= []]
loldomNaiveGfp graph = domOfGfp graph fLolDomNaive
loldomNaiveLfp graph = domOfLfp graph fLolDomNaive



fSinkDomDual graph _ reachable nextCond toNextCond = f 
  where f sinkdomOfCompl = Map.fromList [ (y, (
                             Set.fromList [ x | x <- nodes graph, x /= y]
                           ⊓ Set.fromList [ x | x <- nodes graph, not $ x ∈ ny]
                           ⊓ ((∐) [ sinkdomOfCompl ! x | Just n <- [nextCond y], x <- suc graph n ])
                           -- ⊓ ( case nextCond y of Just n  -> (∐) [  (sinkdomOfCompl! x) | x <- suc graph n ]
                           --                        Nothing -> allNodes)
                         ) ⊔ Set.fromList  [ x | x <- nodes graph, not $ x ∊ reachable y ]
                        ) | y <- nodes graph, let ny = Set.fromList $ toNextCond y]
        allNodes = Set.fromList $ nodes graph
sinkdomOfLfp graph = fmap (\s -> allNodes ∖ s) $ domOfLfp graph fSinkDomDual
  where allNodes = Set.fromList $ nodes graph

sinkdomOfisinkdomProperty :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOfisinkdomProperty graph =
          Map.fromList [ (y,
                 Set.fromList [ y ]
               ⊔ (∐) [ sinkdom ! z | z <- suc isinkdom y]
            )
          | y <- nodes graph]
  where sinkdom = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()
        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs

isinkdomOfGfp2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfGfp2 graph = -- fmap (\s -> Set.fromList [ Set.findMin s | not $ Set.null s]) $  (𝝂) init f
                               (𝝂) init f
  where base  =       Map.fromList [ (x, Set.empty )          | x <- nodes graph, (Set.size $ succs x) == 0]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1]
        init  =       base 
                    ⊔ Map.fromList [ (x, Set.fromList [ y | y <- reachable x, y ∊ joinNodes ] )
                                                              | x <- condNodes ]
        f :: Map Node (Set Node) -> Map Node (Set Node)
        f isinkdom = -- traceShow isinkdom $
                     base 
                   ⊔ Map.fromList [ (x, Set.fromList [ z | z <- Set.toList $ isinkdom ! x,
                                                           (∀) (suc graph x) (\y -> z ∊ (suc isinkdomTrc y))
                                                     ]
                                    )
                                  | x <- condNodes]
          where isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: gr () ())
        condNodes = [ x | x <- nodes graph, (Set.size $ succs x) >= 1  ]
        joinNodes = [ x | x <- nodes graph, (Set.size $ preds x) >= 1  ]
        succs x     = Set.delete x $ Set.fromList $ suc graph x
        preds x     = Set.delete x $ Set.fromList $ pre graph x
        reachable x = suc trncl x
        trncl = trc graph




isinkdomOfSinkContraction :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfSinkContraction graph = fmap (Set.delete endNode) $ 
                                  Map.fromList [ (x, idomClassic ! x)  | x <- nodes graph, not $ x ∈ sinkNodes ]
                                ⊔ Map.fromList [ (x, Set.fromList [y]) | (s:sink) <- sinks, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
                                ⊔ Map.fromList [ (x, Set.empty)        | x <- nodes graph]
    where [endNode] = newNodes 1 graph
          sinks = controlSinks graph
          idomClassic = fmap (\x -> Set.fromList [x]) $ Map.fromList $ iDom (grev $ sinkShrinkedGraph graph endNode) endNode
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]




type Successor = (Set Node, Maybe Node)

sinkdomOfJoinUpperBound :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOfJoinUpperBound  graph =
                      (fmap fromJust $ joinUpperBound graph)
                    ⊔ Map.fromList [ (x, Set.empty)           | x <- nodes graph]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1, not $ x ∈ sinkNodes]
                    ⊔ Map.fromList [ (x, Set.fromList [y])    | (s:sink) <- controlSinks graph, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
    where succs  x    = Set.delete x $ Set.fromList $ suc graph x
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- controlSinks graph, x <- sink]

joinUpperBound :: forall gr a b. DynGraph gr => gr a b -> Map Node (Maybe (Set Node))
joinUpperBound graph = Map.delete dummyNode $ jub condNodes init
    where jub :: Set Node -> Map Node (Maybe (Set Node)) -> Map Node (Maybe (Set Node))
          jub worklist jubs 
              | Set.null worklist = jubs
              | otherwise         = if (ubX == ubX') then
                                      jub               worklist'                     jubs
                                    else
                                      jub (influenced ⊔ worklist') (Map.insert x ubX' jubs)
            where (x, worklist')  = Set.deleteFindMin worklist
                  successorsX = successors ! x
                  ubX         = jubs ! x
                  ubX'        = case foldr1 join successorsX of
                    (ns, Nothing) -> Just ns
                    _             -> Nothing

                  influenced = Set.fromList $ prevConds x

                  join :: Successor -> Successor -> Successor
                  join (ns, Nothing) (ms, Nothing) = (         ns ⊓ ms        , Nothing)
                  join (ns, Just n)  (ms, Nothing) = case jubs ! n of
                    Just ns' -> ((ns ⊔ ns') ⊓  ms, Nothing)
                    Nothing  -> (              ms, Nothing)
                  join (ns, Nothing) (ms, Just m)  = case jubs ! m of
                    Just ms' -> (       ns  ⊓ (ms ⊔ ms'), Nothing)
                    Nothing  -> (       ns              , Nothing)
                  join (ns, Just n)  (ms, Just m)  = case jubs ! m of
                    Just ms' -> case jubs ! n of
                                 Just ns' -> ( (ns ⊔ ns') ⊓ (ms ⊔ ms'), Nothing)
                                 Nothing  -> (              (ms ⊔ ms'), Nothing)
                    Nothing  -> case jubs ! n of
                                 Just ns' -> ( (ns ⊔ ns')             , Nothing)
                                 Nothing  -> (        (ns ⊔ ms),        Just dummyNode)
          [dummyNode] = newNodes 1 graph
          init = Map.fromList $ [ (x, if not $ List.null deadends then
                                        Just $ (∏) [ ns | (ns, Nothing) <- deadends] 
                                      else
                                        Nothing
                                  )
                                | x <- Set.toList $ condNodes,
                                  not $ x ∈ sinkNodes,
                                  let successorsX  = successors ! x,
                                  let deadends =  [ s | s@(_,Nothing) <- successorsX ]
                                ]
                                ++
                                [ (x, Just $ Set.fromList $ the (x ∊) sinks ) | x <- Set.toList $ condNodes,
                                                                                     x ∈ sinkNodes
                                ]
                                ++
                                [ (dummyNode, Nothing) ]
                                   
          successors :: Map Node [Successor] 
          successors = Map.fromList [ (x, [ (Set.fromList $ toNextCond x',
                                             nextCond x'
                                            ) | x' <- Set.toList $ succs x ] 
                                      ) | x <- Set.toList $ condNodes]

          
          succs  x    = Set.delete x $ Set.fromList $ suc graph x
          preds  x    = Set.delete x $ Set.fromList $ pre graph x
          condNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ succs x) > 1 ]
          joinNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ preds x) > 1 ]
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]
          sinks       =  controlSinks graph
          nextCond    = nextRealCondNode graph
          prevConds   = prevRealCondNodes graph
          toNextCond  = toNextRealCondNode graph



onedomOf dom z = Set.fromList $ [ x | y <- Set.toList (dom ! z),
                                      x <- Set.toList (dom ! y),
                                      x /= y
                 ]



domsOf graph dom = Map.fromList [ (z, Set.fromList [ x | x <- Set.toList $ onedom z,
                                                        (∀) (onedom z) (\x' -> x' ∈ dom ! x)
                                      ]
                                  )
                                | z <- nodes graph
                   ]
  where onedom = onedomOf dom

sinkdomsOf graph = domsOf graph sinkdom
  where sinkdom = sinkdomOf graph


mdomsOf graph = domsOf graph mdom
  where mdom = mdomOf graph


sinkDF graph =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈ sinkdom ! p,
                                            not $  x ∈ onedom    y ])
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph
        onedom = onedomOf sinkdom

dfFor graph dom =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈ dom ! p,
                                            not $  x ∈ onedom    y ])
                   | x <- nodes graph ]
  where onedom = onedomOf dom


sinkDFGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFGraphP = cdepGraphP sinkDFGraph

sinkDFGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFGraph = cdepGraph sinkDFcd

sinkDFcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFcd = xDFcd sinkDF


sinkDFLocalDef graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ onedom y  ])
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph
        onedom = onedomOf sinkdom




sinkDFLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFLocal graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            (∀) (suc isinkdom y) (\z -> not $ x ∊ (isinkdomSccOf z))
                                      ]
                     )
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()
        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs

sinkDFLocalViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFLocalViaSinkdoms graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ sinkdoms ! y
                                      ]
                     )
                   | x <- nodes graph ]
  where sinkdoms = sinkdomsOf graph



sinkDFUpDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUpDef graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                            (∀) (suc isinkdom z) (\c ->  (∀) (isinkdomSccOf c)  (\x -> (not $ x ∈ sinkdom ! y)  ∨  x == y))
                                      ]
                     )
                   | z <- nodes graph, (∃) (suc isinkdom z) (\x -> True)]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs

sinkDFUpDefViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUpDefViaSinkdoms graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                            (∀) (sinkdoms ! z) (\x -> not $ x ∈ onedom y)
                                      ]
                     )
                   | z <- nodes graph,  (∃) (sinkdoms ! z) (\x -> True)]
  where sinkdom  = sinkdomOf graph
        sinkdoms = sinkdomsOf graph
        sinkdf   = sinkDF graph
        onedom = onedomOf sinkdom

sinkDFUpGivenXViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
sinkDFUpGivenXViaSinkdoms graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                not $ x ∈ sinkdoms ! y
                                      ]
                     )
                   | z <- nodes graph,  x <- Set.toList $ sinkdoms ! z]
  where sinkdom  = sinkdomOf graph
        sinkdoms = sinkdomsOf graph
        sinkdf   = sinkDF graph

sinkDFUpGivenX :: forall gr a b. DynGraph gr => gr a b -> Map (Node,Node) (Set Node)
sinkDFUpGivenX graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                (∀) (suc isinkdom y) (\c ->  not $ x ∊ (isinkdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, c <- suc isinkdom z,  x <- isinkdomSccOf c]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs


sinkDFUp :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUp graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                assert (
                                                (∀) (suc isinkdom y)                                (/=x)
                                                ↔
                                                (∀) (suc isinkdom y) (\c ->  not $ x ∊ (isinkdomSccOf c))
                                                ) True,
                                                
                                                (∀) (suc isinkdom y) (\c ->  not $ x ∊ (isinkdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, assert ((length $ suc isinkdom z) <= 1) True,  [x] <- [suc isinkdom z]]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs




sinkDFFromUpLocalDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocalDef graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- pre isinkdom x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocalDef graph
        dfup = sinkDFUpDef graph
        sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()

sinkDFFromUpLocalDefViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocalDefViaSinkdoms graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- sinkdomsInv ! x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocalDef graph
        dfup = sinkDFUpDefViaSinkdoms graph
        sinkdoms  = sinkdomsOf graph
        sinkdomsInv = invert' (fmap Set.toList sinkdoms) `Map.union` (Map.fromList [ (x, []) | x <- nodes graph ]) 



mdomOfimdomProperty :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mdomOfimdomProperty graph =
          Map.fromList [ (y,
                 Set.fromList [ y ]
               ⊔ (∐) [ mdom ! z | z <- suc imdom y]
            )
          | y <- nodes graph]
  where mdom = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs



sinkDFFromUpLocalDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFFromUpLocalDefGraphP = cdepGraphP sinkDFFromUpLocalDefGraph

sinkDFFromUpLocalDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFFromUpLocalDefGraph = cdepGraph sinkDFFromUpLocalDefcd

sinkDFFromUpLocalDefcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFFromUpLocalDefcd = xDFcd sinkDFFromUpLocalDef



sinkDFFromUpLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocal graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z | z <- pre isinkdom x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocal graph
        dfup = sinkDFUp graph
        sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()


sinkDFFromUpLocalGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFFromUpLocalGraphP = cdepGraphP sinkDFFromUpLocalGraph

sinkDFFromUpLocalGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFFromUpLocalGraph = cdepGraph sinkDFFromUpLocalcd

sinkDFFromUpLocalcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFFromUpLocalcd = xDFcd sinkDFFromUpLocal


sinkDFF2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFF2 graph = idomToDF graph isinkdom
  where sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()


sinkDFF2GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFF2GraphP = cdepGraphP sinkDFF2Graph

sinkDFF2Graph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFF2Graph = cdepGraph sinkDFF2cd

sinkDFF2cd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFF2cd = xDFcd sinkDFF2

xDFcd :: DynGraph gr => (gr a b -> Map Node (Set Node)) -> gr a b ->  Map Node (Set Node)
xDFcd xDF graph                  = Map.fromList [ (n, Set.empty)       | n <- nodes graph]
                                 ⊔ Map.fromList [ (n, Set.delete n ns) | (n,ns) <- Map.assocs $
                                                                            (fmap Set.fromList $ invert' $ fmap Set.toList df )
                                                ]
  
  where df = xDF graph


isinkdomOf    graph = immediateOf $ sinkdomOf    graph
isinkdomOfGfp graph = immediateOf $ sinkdomOfGfp graph

imdomOf    graph = immediateOf $ mdomOf    graph
imdomOfLfp graph = immediateOf $ mdomOfLfp graph






mDF graph =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈   mdom ! p,
                                            not $  x ∈ onedom   y ])
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph
        onedom = onedomOf mdom


mDFGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFGraphP = cdepGraphP sinkDFGraph

mDFGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFGraph = cdepGraph mDFcd

mDFcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFcd = xDFcd mDF


mDFLocalDef graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ onedom y  ])
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph
        onedom = onedomOf mdom




mDFLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFLocal graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            (∀) (suc imdom y) (\z -> not $ x ∊ (imdomSccOf z))
                                      ]
                     )
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs


mDFLocalViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFLocalViaMdoms graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ mdoms ! y
                                      ]
                     )
                   | x <- nodes graph ]
  where mdoms = mdomsOf graph


mDFUpDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUpDef graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                            (∀) (suc imdom z) (\c ->  (∀) (imdomSccOf c) (\x -> (not $ x ∈ mdom ! y)  ∨  x == y))
                                      ]
                     )
                   | z <- nodes graph,  (∃) (suc imdom z) (\x -> True)]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs

mDFUpDefViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUpDefViaMdoms graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                            (∀) (mdoms ! z) (\x -> not $ x ∈ onedom y)
                                      ]
                     )
                   | z <- nodes graph,  (∃) (mdoms ! z) (\x -> True)]
  where mdom  = mdomOf graph
        mdoms = mdomsOf graph
        mdf   = mDF graph
        onedom = onedomOf mdom
        
mDFUpGivenXViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
mDFUpGivenXViaMdoms graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                not $ x ∈ mdoms ! y
                                      ]
                     )
                   | z <- nodes graph,  x <- Set.toList $ mdoms ! z]
  where mdom  = mdomOf graph
        mdoms = mdomsOf graph
        mdf   = mDF graph

mDFUpGivenX :: forall gr a b. DynGraph gr => gr a b -> Map (Node,Node) (Set Node)
mDFUpGivenX graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                (∀) (suc imdom y) (\c ->  not $ x ∊ (imdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, c <- suc imdom z, x <- imdomSccOf c]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs


mDFUp :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUp graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                (∀) (suc imdom y) (\c -> not $ x ∊  (imdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, assert ((length $ suc imdom z) <= 1) True,  [x] <- [suc imdom z]]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs


mDFFromUpLocalDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocalDef graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- pre imdom x  ] ) | x <- nodes graph]
  where dflocal = mDFLocalDef graph
        dfup = mDFUpDef graph
        mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()

mDFFromUpLocalDefViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocalDefViaMdoms graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- mdomsInv ! x  ] ) | x <- nodes graph]
  where dflocal = mDFLocalDef graph
        dfup = mDFUpDefViaMdoms graph
        mdoms  = mdomsOf graph
        mdomsInv = invert' (fmap Set.toList mdoms) `Map.union` (Map.fromList [ (x, []) | x <- nodes graph ])


mDFFromUpLocalDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFFromUpLocalDefGraphP = cdepGraphP mDFFromUpLocalDefGraph

mDFFromUpLocalDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFFromUpLocalDefGraph = cdepGraph mDFFromUpLocalDefcd

mDFFromUpLocalDefcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFFromUpLocalDefcd = xDFcd mDFFromUpLocalDef




mDFFromUpLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocal graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z | z <- pre imdom x  ] ) | x <- nodes graph]
  where dflocal = mDFLocal graph
        dfup = mDFUp graph
        mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()


mDFFromUpLocalGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFFromUpLocalGraphP = cdepGraphP mDFFromUpLocalGraph

mDFFromUpLocalGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFFromUpLocalGraph = cdepGraph mDFFromUpLocalcd

mDFFromUpLocalcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFFromUpLocalcd = xDFcd mDFFromUpLocal



mDFF2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFF2 graph = idomToDF graph imdom
  where mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()

mDFF2GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFF2GraphP = cdepGraphP mDFF2Graph

mDFF2Graph :: DynGraph gr => gr a b ->  gr a Dependence
mDFF2Graph = cdepGraph mDFF2cd

mDFF2cd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFF2cd = xDFcd mDFF2



imdomOfTwoFinger6 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
imdomOfTwoFinger6 graph = Map.mapWithKey (\n ms -> Set.delete n ms) $
                          fmap toSet $ 
                          twoFinger 0 worklist0 imdom0 imdom0Rev
  where imdom0   =             Map.fromList [ (x, Just z )       | x <- nodes graph, [z] <- [suc graph x], z /= x]
                   `Map.union` Map.fromList [ (x, Nothing)       | x <- nodes graph]
        imdom0Rev = invert''' imdom0
        worklist0   = condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (suc graph x) > 1 ]
        nextCond    = nextCondNode graph
        prevConds   = prevCondNodes graph
        prevCondsImmediate = prevCondImmediateNodes graph

        solution = mdomOfLfp graph
        dom = solution
        doms = domsOf graph dom
        invariant worklist imdom = -- if (True) then True else
                                   -- (if (not inv) then (traceShow (worklist, imdom, imdomWorklist)) else id) $
                                   inv
          where inv =   (∀) (nodes graph) (\n -> (∀) (nodes graph) (\m ->
                                (m ∊ (suc imdomWorklistTrc  n)) ↔ (m ∈ solution ! n)
                        ))
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> (m ∈ solution ! n) ∧ (∀) (solution ! n) (\m' -> m' == n  ∨  (m' ∈ solution ! m))
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> m ∈ doms ! n
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          (isNothing ms  ∧  (∃) (solution ! n) (\m -> m /= n)) → (
                            n ∈ worklistLfp
                          )
                        )
                imdomTrc = trc $ (fromSuccMap (fmap toSet imdom) :: gr () ())
                worklistLfp = (㎲⊒) Set.empty f
                  where f wl = worklist
                             ⊔ Set.fromList [ n | n <- Set.toList condNodes,
                                                  w <- Set.toList wl,
                                                  (∃) (suc graph n) (\y -> reachableFromSeen imdom y w Set.empty),
                                                  (∃) (nodes graph) (\m -> m ∈ doms ! w)
                                            ]
                imdomWorklist = fmap toSet imdom
                              ⊔ Map.fromList [ (w, doms ! w) | w <- Set.toList $ worklistLfp ]
                imdomWorklistTrc = trc $ (fromSuccMap  imdomWorklist :: gr () ())

        twoFinger :: Integer -> Set Node ->  Map Node (Maybe Node) ->  Map Node (Set Node) -> Map Node (Maybe Node)
        twoFinger i worklist imdom imdomRev
            | Set.null worklist = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                  -- traceShow (Set.size worklist0, i) $ 
                                  assert (invariant worklist imdom) $
                                  imdom
            | otherwise         = -- traceShow (x, mz, zs, influenced, influencedSlow, worklist, imdom) $
                                  assert (influenced == influencedSlow) $ 
                                  assert (invariant worklist imdom) $
                                  assert (changed → (zs /= Nothing)) $
                                  assert (changed → ( case imdom ! x of { Nothing -> True ; Just _  -> not $ x ∈ reachableFromM imdom (Set.fromList [ z ]) Set.empty })) $
                                  assert (changed → ( case imdom ! x of { Nothing -> True ; Just z0 -> (z0 ∈ reachableFromM imdom (Set.fromList [z ]) Set.empty)
                                                                                                      ∧ ( z ∈ reachableFromM imdom (Set.fromList [z0]) Set.empty) } )) $
                                  if (not $ changed) then twoFinger (i+1)               worklist'                                   imdom                                          imdomRev
                                                     else twoFinger (i+1) (influenced ⊔ worklist')  (Map.insert x zs                imdom) (Map.insertWith (∪) z (Set.singleton x) imdomRev)
          where (x, worklist')  = Set.deleteFindMin worklist
                mz = foldM1 (lca imdom) (suc graph x)
                Just z = zs
                zs = case mz of
                      Just z  -> if z/= x then
                                   Just z
                                 else
                                   Nothing
                      Nothing -> Nothing
                changed = zs /= (imdom ! x)
                influenced = let preds = reachableFrom imdomRev (Set.fromList [x])
                             in Set.fromList $ [ n | n <- foldMap prevCondsImmediate preds,  n /= x]
                influencedSlow = Set.fromList [ n | n <- Set.toList condNodes, n /= x, (∃) (suc graph n) (\y -> reachableFromSeen imdom y x Set.empty) ]


imdomOfTwoFinger7 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
imdomOfTwoFinger7 graph = Map.mapWithKey (\n ms -> Set.delete n ms) $
                          fmap toSet $ twoFinger 0 workqueue0 Nothing imdom0
  where imdom0   =             Map.fromList [ (x, Just z   ) | x <- nodes graph, [z] <- [suc graph x], z /= x]
                   `Map.union` Map.fromList [ (x, Nothing  ) | x <- nodes graph]
        workqueue0   = Dequeue.fromList $ Set.toList $ condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (suc graph x) > 1 ]
        prevConds   = prevCondNodes graph
        prevCondsImmediate = prevCondImmediateNodes graph
        nextCond    = nextCondNode graph

        solution = mdomOfLfp graph
        dom = solution
        onedom = onedomOf solution
        invariant workqueue imdom = -- if (True) then True else
                                   -- (if (not inv) then (traceShow (worklist, imdom, imdomWorklist)) else id) $
                                   inv
          where worklist = Set.fromList $ Foldable.toList $ workqueue
                inv =   (∀) (nodes graph) (\n -> (∀) (solution ! n) (\m ->
                                (m ∊ (suc imdomWorklistTrc  n))
                        ))
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> (m ∈ solution ! n) ∧ (∀) (solution ! n) (\m' -> m' == n  ∨  (m' ∈ solution ! m))
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> (m ∈ onedom n) ∧ (∀) (onedom n) (\m' -> m' ∈ solution ! m)
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          (isNothing ms  ∧  (∃) (solution ! n) (\m -> m /= n)) → (
                            n ∈ worklistLfp
                          )
                        )
                imdomTrc = trc $ (fromSuccMap (fmap toSet imdom) :: gr () ())
                worklistLfp = (㎲⊒) Set.empty f
                  where f wl = worklist
                             ⊔ Set.fromList [ n | n <- Set.toList condNodes,
                                                  w <- Set.toList wl,
                                                  p <- nodes graph,
                                                  (w ∈  onedom p ∧ (∀) (onedom p) (\w' -> w' ∈ solution ! w)) ∨ w == p,
                                                  (∃) (suc graph n) (\y -> Just p == nextCond y)
                                            ]
                imdomWorklist = fmap toSet imdom
                              ⊔ Map.fromList [ (w, Set.fromList [ m | m <- Set.toList $ onedom w,
                                                                      (∀) (onedom w) (\m' -> m' ∈ solution ! m)
                                                                ]
                                               )
                                             | w <- Set.toList $ worklistLfp ]
                imdomWorklistTrc = trc $ (fromSuccMap  imdomWorklist :: gr () ())

        twoFinger :: Integer -> SimpleDequeue Node -> Maybe Node -> Map Node (Maybe Node) -> Map Node (Maybe Node)
        twoFinger i worklist oldest imdom 
            |  (Dequeue.null worklist)
             ∨ (Just x == oldest) = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                    -- traceShow (Set.size worklist0, i) $ 
                                    assert (invariant worklist imdom) $
                                    imdom
            | otherwise           = -- traceShow (x, mz, zs, worklist, imdom) $
                                    assert (invariant worklist imdom) $
                                    if (not $ new) then twoFinger (i+1) (pushBack worklist' x) oldest'                    imdom
                                    else                twoFinger (i+1) (         worklist'  ) Nothing  (Map.insert x zs  imdom)
          where Just (x, worklist')  = popFront worklist
                mz = foldM1 (lca imdom) (suc graph x)
                zs = case mz of
                      Just z  -> if z/= x then
                                   Just z
                                 else
                                   Nothing
                      Nothing ->  Nothing
                new     = assert (isNothing $ imdom ! x) $
                          (not $ isNothing zs)
                oldest' = case oldest of
                  Nothing -> Just x
                  _       -> oldest



isinkdomOfTwoFinger8Down :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8Down graph sinkNodes sinks nonSinkCondNodes = twoFingerDown
  where sinkNodesToCanonical = Map.fromList [ (s, s1) | sink <- sinks, let (s1:_) = sink, s <- sink ]
        prevCondsImmediate = prevCondImmediateNodes graph
        twoFingerDown worklist imdom
            | Map.null worklist   = imdom
            | otherwise           = assert (influenced == influencedSlow) $ 
                                    assert ((imdom ! x == Nothing) → (zs == Nothing)) $
                                    if (not $ changed) then twoFingerDown                          worklist'                                   imdom
                                    else                    twoFingerDown  (influenced `Map.union` worklist')  (Map.insert x zs                imdom)
          where ((x, succs), worklist')  = Map.deleteFindMin worklist
                mz = require (succs == suc graph x) $
                     foldM1 (lca imdom) succs
                zs = case mz of
                       Nothing -> Nothing
                       Just z  -> assert (z /= x) $
                                  case Map.lookup z sinkNodesToCanonical of
                                    Just s1 -> Just s1
                                    Nothing -> Just z
                changed = imdom ! x /= zs
                influenced = let imdomRev = invert''' $ imdom
                                 preds = reachableFrom imdomRev (Set.fromList [x])
                             in Map.fromList $ [ (n, succ) | n <- foldMap prevCondsImmediate preds, Just succ <- [Map.lookup n nonSinkCondNodes]]
                influencedSlow = Map.fromList [ (n, succ) | (n, succ) <- Map.assocs nonSinkCondNodes, (∃) succ (\y -> reachableFromSeen imdom y x Set.empty) ]


isinkdomOfTwoFinger8DownFixedTraversalForOrder :: forall gr a b. (DynGraph gr) =>
     (gr a b -> Set Node -> [[Node]] -> Map Node [Node] -> Map Node (Maybe Node) -> [(Node, [Node])])
  -> gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownFixedTraversalForOrder order graph sinkNodes sinks toConsider imdom0 =
      id
    $ require (Map.fromList workLeft == toConsider)
    $ result
  where result = twoFingerDown workLeft [] imdom0 False

        sinkNodesToCanonical = Map.fromList [ (s, s1) | sink <- sinks, let (s1:_) = sink, s <- sink ]
        workLeft  = order graph sinkNodes sinks toConsider imdom0
        
        twoFingerDown []                       _         imdom False   = imdom
        twoFingerDown []                       workRight imdom True    = twoFingerDown workLeft'  []                          imdom    False
          where workLeft'  = reverse workRight
        twoFingerDown (w@(x, succs):workLeft') workRight imdom changed = twoFingerDown workLeft'  workRight' (Map.insert x zs imdom)  (changed ∨ changed')
          where workRight' = if done then workRight else w:workRight
                mz = require (succs == suc graph x) $
                     foldM1 (lca imdom) succs
                changed' = imdom ! x /= zs
                (zs, done) = case mz of
                       Nothing -> (Nothing, True)
                       Just z  -> assert (z /= x) $
                                  case Map.lookup z sinkNodesToCanonical of
                                    Just s1 -> (Just s1, False)
                                    Nothing -> (Just z, False)


isinkdomOfTwoFinger8DownSingleNodeSinks :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownSingleNodeSinks graph nxs condNodes imdom0 =
      id
    $ require ((∀) nxs (\nx -> imdom0 ! nx == Nothing))
    $ require ((∀) nxs (\nx -> not $ Map.member nx condNodes))
    --   traceShow (workset, worklist, imdom0)
    -- $ traceShow result
    $ result
  where result = twoFingerDown workLeft [] imdom0 False

        workLeft = Map.assocs condNodes

        twoFingerDown []                       _         imdom False   = imdom
        twoFingerDown []                       workRight imdom True    = twoFingerDown workLeft'  []                          imdom    False
          where workLeft'  = reverse workRight
        twoFingerDown (w@(x, succs):workLeft') workRight imdom changed = twoFingerDown workLeft'  workRight' (Map.insert x mz imdom)  (changed ∨ changed')
          where changed' =  mz /= (imdom ! x)
                workRight' = if mz == Nothing then workRight else w:workRight
                  where Just z = mz
                mz = require (succs == suc graph x) $
                     foldM1 lca succs
                lca = lcaSingleNodeSinks imdom nxs



isinkdomOfTwoFinger8DownTreeTraversal :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownTreeTraversal = isinkdomOfTwoFinger8DownFixedTraversalForOrder order
  where order graph sinkNodes sinks toConsider imdom0 = worklist
          where worklist = [ (n, succs) | (n, succs, _) <- sortBy (comparing sucOrder) [ (n, succs, minimum [ treeOrderOf x | x <- succs] ) | (n, succs) <- Map.assocs toConsider ]]
                sucOrder (n, succs, succOrder) = succOrder 
                treeOrderOf n = treeOrder ! n
                  where treeOrder :: Map Node Integer
                        treeOrder = Map.fromList $ zip (Set.toList sinkNodes ++ [ n | n <- treeDfs (fmap maybeToList imdom0) roots]) [0..]
                          where roots = [ n | (n, Just m) <- Map.assocs imdom0, not $ n ∈ sinkNodes, m ∈ sinkNodes]


isinkdomOfTwoFinger8DownFixedTraversal :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownFixedTraversal = isinkdomOfTwoFinger8DownFixedTraversalForOrder order
  where order graph sinkNodes sinks toConsider imdom0 = Map.assocs toConsider



isinkdomOfTwoFinger8ForSinks :: forall gr a b. (DynGraph gr) => [[Node]] -> Set Node -> Map Node [Node] -> gr a b -> Map Node (Maybe Node)
isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph =
                          require ((Set.fromList sinks) == (Set.fromList $ controlSinks graph))
                        $ require (sinkNodes == (∐) [ Set.fromList sink | sink <- sinks])
                        $ require (nonSinkCondNodes == Map.fromList [ (n, succs) | n <- nodes graph, not $ n ∈ sinkNodes, let succs = suc graph n, length succs > 1 ])
                        $ Map.mapWithKey (\n m -> if m == Just n then Nothing else m)
                        $ imdom''
  where imdom0   =              Map.fromList [ (s1, Just s2)  | (s:sink) <- sinks, sink /= [], (s1,s2) <- zip (s:sink) (sink ++ [s]) ]
                   `Map.union` (Map.fromList [ (x, case suc graph x of { [z] -> assert (z /= x) $ Just z               ; _ -> Nothing  }) | x <- nodes graph, not $ x ∈ sinkNodes ])
                   `Map.union` (Map.fromList [ (x, case suc graph x of { [z] -> if (z /= x) then  Just z else Nothing  ; _ -> Nothing  }) | [x] <- sinks ])
        worklist0 :: SimpleDequeue (Node, [Node])
        worklist0   = Dequeue.fromList $ Map.assocs $ nonSinkCondNodes
--        processed0  = (㎲⊒) sinkNodes (\processed -> processed ⊔ (Set.fromList [ x | x <- nodes graph, [z] <- [suc graph x], z ∈ processed]))
        processed0  = Set.fold f Set.empty sinkNodes
          where f s processed
                    | s ∈ processed = processed
                    | otherwise     = processed'From graph nonSinkCondNodes (Set.fromList [s]) (processed ∪ Set.fromList [s])

--      imdom'  = isinkdomOftwoFinger8UpDfs              graph           sinks                                          imdom0
        imdom'  = isinkdomOftwoFinger8Up                 graph                   nonSinkCondNodes  worklist0 processed0 (invert''' imdom0) imdom0 
        imdom'' = isinkdomOfTwoFinger8DownFixedTraversal graph sinkNodes sinks                    (Map.filterWithKey (\x _ -> imdom' ! x /= Nothing) nonSinkCondNodes) imdom'
--      imdom'' = isinkdomOfTwoFinger8Down               graph sinkNodes sinks   nonSinkCondNodes (Map.filterWithKey (\x _ -> imdom' ! x /= Nothing) nonSinkCondNodes) imdom'


processed'From  :: Graph gr => gr a b -> Map Node c -> Set Node -> Set Node -> Set Node
{-# INLINE processed'From #-}
processed'From graph nonSinkCondNodes = processed'F
  where processed'F xs processed
            | Set.null xs   = processed
            | otherwise     = processed'F (foldr Set.insert xs' new) (foldr Set.insert processed new)
                where (x, xs') = Set.deleteFindMin xs
                      new      = [ x'| x' <- pre graph x, not $ Map.member x' nonSinkCondNodes, not $ x' ∈ processed]


isinkdomOftwoFinger8Up ::  forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> SimpleDequeue (Node, [Node]) -> Set Node ->  Map Node (Set Node) -> Map Node (Maybe Node) -> Map Node (Maybe Node)
isinkdomOftwoFinger8Up graph nonSinkCondNodes  worklist processed imdomRev imdom =
      require (Map.filter (not . Set.null) imdomRev == invert''' imdom)
    $ twoFinger worklist processed imdom imdomRev
  where solution = sinkdomOfGfp graph
        twoFinger worklist processed imdom imdomRev
            | Dequeue.null worklist   = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                    -- traceShow (Set.size worklist0, i) $
                                    assert (  (Set.fromList $ edges $ trc $ (fromSuccMap $ fmap toSet imdom :: gr ()()))
                                            ⊇ (Set.fromList $ edges $ trc $ (fromSuccMap $ solution :: gr () ()))) $
                                    imdom
            | otherwise           = -- traceShow (x, worklist', mz, processed', new, imdom) $
                                    assert (imdom ! x == Nothing) $
                                    assert (not $ x ∈ processed) $
                                    if   (not $ new) then twoFinger (pushBack worklist' w)   processed                      imdom                                           imdomRev
                                    else                  twoFinger (         worklist'  )   processed' (Map.insert x mz    imdom) (Map.insertWith (∪) z (Set.fromList [x]) imdomRev)
          where Just (w@(x, succs0), worklist')  = popFront worklist
                processed' = processed ∪ (reachableFrom imdomRev (Set.fromList [x]))
                z = case mz of
                  Nothing -> undefined
                  Just z  -> z
                mz
                  | List.null succs   = Nothing
                  -- | otherwise         = Just $ head $ succs
                  | otherwise  = case foldM1 (lca imdom) succs of
                      Nothing -> Just $ head $ succs
                      Just z  -> Just z
                  where succs    = require (succs0 == (suc graph x)) $
                                   [ y | y <- succs0, y ∈ processed ]
                new     = not $ isNothing mz


isinkdomOftwoFinger8UpDfs ::  forall gr a b. (DynGraph gr) => gr a b -> [[Node]] -> Map Node (Maybe Node) -> Map Node (Maybe Node)
isinkdomOftwoFinger8UpDfs graph sinks idom =
    assert (  (Set.fromList $ edges $ trc $ (fromSuccMap $ fmap toSet idom' :: gr ()()))
           ⊇ (Set.fromList $ edges $ trc $ (fromSuccMap $ solution :: gr () ()))) $
    idom'
  where solution = sinkdomOfGfp graph

        idom' = go [forest] idom

        forest = rdff [ s | (s:_) <- sinks ] graph

        go :: [[Tree Node]] -> Map Node (Maybe Node) -> Map Node (Maybe Node)
        go []                       idom = idom
        go ([]               :ts'') idom = go         ts''  idom
        go (((Node n ts):ts'):ts'') idom = go (ts:ts':ts'') idom'
          where idom' = foldr f idom [ Tree.rootLabel t | t <- ts ]
                f m = Map.insertWith g m (Just n)
                g n  Nothing  = n
                g _        n' = n'



isinkdomOfTwoFinger8 :: forall gr a b. (DynGraph gr) => gr a b -> Map Node (Set Node)
isinkdomOfTwoFinger8 graph = fmap toSet $ isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph
  where sinkNodes   = Set.fromList [ x | sink <- sinks, x <- sink]
        sinks = controlSinks graph
        nonSinkCondNodes = Map.fromList [ (x, succs) | x <- nodes graph, not $ x ∈ sinkNodes, let succs = suc graph x, length succs > 1 ]










{- 
isinkdomOfTwoFinger9DownFixedTraversal :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Integer
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger9DownFixedTraversal graph i imdom0 =
      id
    $ result
  where solution = sinkdomOfGfp graph
        result = twoFingerDown i worklist imdom0 False
        worklist = [(n, succs) | n <- nodes graph, let succs = suc graph n]
        
        twoFingerDown i []                     imdom False   = imdom
        twoFingerDown i []                     imdom True    = twoFingerDown  i    worklist                   imdom    False
        twoFingerDown i ((x, succs):worklist') imdom changed = if (not $ expanded ⊒ solution) then traceShow (x, zs, imdom) $ error "rofl" else
                                                               twoFingerDown (i+1) worklist' (Map.insert x zs imdom)  (changed ∨ changed')
          where expanded = toSuccMap $ trc $ (fromSuccMap $ fmap toSet $ Map.insert x zs $ imdom :: gr () ())
                mz = require (succs == suc graph x) $
                     case succs of
                       [] -> Nothing
                       _  -> foldM1 (lca imdom) succs
                changed' = imdom ! x /= zs
                zs = case mz of
                       Nothing -> Nothing
                       Just z  -> assert (z /= x) $
                                  -- if (x ∈ reachableFrom (fmap toSet (Map.insert x (Just z) imdom)) (Set.fromList [z]) (Set.empty)) then imdom ! x else Just z
                                  Just z

        lca imdom n m = let result = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m]) in result
          where 
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  caseN
                  where caseN = case imdom ! n of
                                  Nothing ->                 lcaDownLin ms ns m
                                  Just n' -> if n' ∈ ns then lcaDownLin ms ns m  else lcaDown' (m, ms) (n', Set.insert n' ns)
                lcaDownLin ms ns m = assert (not $ m ∈ ns) $ lcaDown'' m ms
                  where lcaDown'' m ms = case imdom ! m of
                                        Nothing -> Nothing
                                        Just m' -> if m' ∈ ns then Just m' else
                                                   if m' ∈ ms then Nothing else lcaDown'' m' (Set.insert m' ms)


isinkdomOfTwoFinger9 :: forall gr a b. (DynGraph gr) => gr a b -> Map Node (Set Node)
isinkdomOfTwoFinger9 graph
    | List.null $ nodes graph = Map.empty
    | otherwise =         Map.mapWithKey (\n ms -> Set.delete n ms)
                        $ fmap toSet
                        -- $ traceShow (zip starts ends)
                        -- $ traceShow imdomLin'
                        $ isinkdomOfTwoFinger9DownFixedTraversal graph 0 imdom0
  where
        -- imdomLin  =  Map.fromList [ (m, Just m')  | m <- nodes graph, [m'] <- [suc graph m]]
        -- imdomLin' = case starts of
        --              []  -> imdomLin
        --              [s] -> imdomLin
        --              _   -> imdomLin `Map.union` Map.fromList [ (end, Just start)  | (end, start) <- zip ends starts0]
        -- starts = [ m  | m <- Map.keys imdomLin, not $ (∃) (Map.elems imdomLin) (\(Just m') -> m == m') ]
        -- ends   = [ go m | m <- starts ]
        --   where go m = case Map.lookup m imdomLin of
        --                          Nothing        -> m
        --                          Just (Just m') -> go m'
        -- (_:_:starts0) = starts 

        imdom0   =  Map.fromList [ (m, Just m')  | (m,m') <- zip (n:ns) (ns ++ [n]) ]
          where (n:ns) = nodes graph
-}





withPossibleIntermediateNodesFromiXdom :: forall gr a b x. (Ord x, DynGraph gr) => gr a b -> Map Node (Set (Node, x)) -> Map Node (Set (Node, (x, Set Node)))
withPossibleIntermediateNodesFromiXdom graph ixdom = Map.fromList [ (n, Set.fromList [(m,(x,pi))])  | (n, ms) <- Map.assocs ixdom, [(m,x)] <- [Set.toList $ ms], let pi = pis ! n ]
                                                   ⊔ Map.fromList [ (n, Set.fromList []          )  | (n, ms) <- Map.assocs ixdom, []      <- [Set.toList $ ms]                   ]
  where pis = possibleIntermediateNodesFromiXdom graph $  fmap (Set.map fst) $ ixdom
  
possibleIntermediateNodesFromiXdom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node)
possibleIntermediateNodesFromiXdom graph ixdom = (㎲⊒) init f
  where init     = Map.fromList [ (n, Set.empty)                       | n <- Map.keys ixdom ]
        f pis    = pis
                 ⊔ Map.fromList [ (p, Set.delete z $
                                      (∐) [ Set.fromList [ y ]  ⊔  pis ! y | x <- suc graph p,
                                                                              let path = revPathFromTo ixdom x z,
                                                                              y <- path
                                      ]
                                  )
                                | p <- condNodes,
                                  [z] <- [Set.toList $ ixdom ! p]
                   ]
        condNodes   = [ x | x <- nodes graph, length (suc graph x) > 1 ]

        revPathFromTo ixdom x z = revPathFromToA x []
          where revPathFromToA x ps 
                   | x == z    = ps
                   | otherwise = revPathFromToA next (x:ps)
                 where [next] = Set.toList $ ixdom ! x



reachableFromSeen :: Map Node (Maybe Node) -> Node -> Node -> Set Node -> Bool
reachableFromSeen imdom n m seen
 | n == m   = True
 | n ∈ seen = False
 | otherwise = case imdom ! n of
     Just n' -> reachableFromSeen imdom n' m (Set.insert n seen)
     Nothing -> False



-- TODO: limit this to starts of linear section
predsSeenFor :: Map Node [Node] -> [Node] -> [Node] -> [Node]
predsSeenFor imdomRev = predsSeenF where
      predsSeenF :: [Node] -> [Node] -> [Node]
      predsSeenF seen front = concat $ fmap (predsSeen seen) front
      predsSeen  :: [Node] -> Node -> [Node]
      predsSeen seen x = case Map.lookup x imdomRev of 
        Nothing  -> seen
        Just ys  -> let new = (filter (not . (∊ seen)) ys) in case new of
                      [] -> seen
                      _  -> predsSeenF (new ++ seen) new



idomToDF :: forall gr a b. DynGraph gr => gr a b -> gr () () -> Map Node (Set Node)
idomToDF graph idomG = 
      (㎲⊒) (Map.fromList [(x, Set.empty) | x <- nodes graph]) f2
  where f2 df = df ⊔ 
           Map.fromList [ (x, (∐) [ Set.fromList [ y ] | y <- pre graph x,
                                                         (∀) (suc idomG y) (\c -> not $ x ∊ (idomSccOf ! c))
                                   ]
                          )
                        | x <- nodes graph]
         ⊔ Map.fromList [ (x, (∐) [ Set.fromList [ y ] | z <- pre idomG x,
                                                          y <- Set.toList $ df ! z,
                                                         (∀) (suc idomG y) (\c -> not $ x ∊ (idomSccOf ! c))
                                   ])
                        | x <- nodes graph]
        idomSccs = scc idomG
        idomSccOf = Map.fromList [ (c, cycle) | cycle <- idomSccs, c <- cycle ]

idomToDFFastForRoots :: forall gr a b. Graph gr => [[Node]] -> gr a b -> Map Node (Maybe Node) -> Map Node (Set Node)
idomToDFFastForRoots roots graph idom = foldr f2 Map.empty sorting
  where f2 cycle df = Map.fromSet (\x -> combined) cycle `Map.union` df
          where combined = (local ∪ up) ∖ invalid
                local = Set.fromList [ y                | x <- Set.toList cycle, 
                                                          y <- pre graph x
                                   ]
                up    = Set.unions [ us                 | z <- Set.toList invalid,
                                                          Just us <- [Map.lookup z df]
                                   ]
                invalid =  Set.unions [ is | x <- Set.toList cycle, Just is <- [Map.lookup x idom'] ]

        rs = fmap Set.fromList $ roots
        idom' :: Map Node (Set Node)
        idom' = invert''' idom

        sorting :: [Set Node]
        sorting = dfsTree idom' rs

idomToDFFast graph idom = idomToDFFastForRoots (roots idom) graph (fmap fromSet idom)

dfViaCEdges :: Graph gr => gr a b -> Map Node (Maybe Node) -> Node -> Set Node
dfViaCEdges graph idom = \x -> Set.fromList [ y | z <- Set.toList $ reachableFrom idom' (Set.fromList [x]),
                                                  y <- cEdges ! z, {- y <- pre graph z, not $ z ∈ idomsOf y -}
                                                  (not $ x ∈ reachableFromM idom (idomsOf y) Set.empty)
                         ]
  where idom' = invert''' idom
        idomsOf y = case idom ! y of
          Nothing -> Set.empty
          Just y' -> cycleOf y'
        (cycleOfM,_) =  findCyclesM $ idom
        cycleOf x = Map.findWithDefault (Set.singleton x) x cycleOfM
        cEdges = Map.fromList [(z, [ y | y <- pre graph z, not $ z ∈ idomsOf y ]) | z <- nodes graph]


idfViaCEdgesFastForCycles :: Graph gr => (Map Node (Set Node), [Set Node]) -> gr a b -> Map Node (Maybe Node) -> Set Node -> Set Node
idfViaCEdgesFastForCycles (cycleOfM, cycles) graph idom = \xs0 -> if Set.null xs0 then
                                       Set.empty
                                     else
                                       let queue0 = Prio.Max.fromList [ (levelOf ! x, x) | x <- Set.toList xs0 ]
                                           ((lvlX,x), queue) = Prio.Max.deleteFindMax queue0
                                       in go Set.empty x lvlX (Set.toList $ cycleOf x) queue xs0
  where 
        go processed x lvlX zs queue idf
          | List.null zs  ∧ Prio.Max.null queue = idf
          | List.null zs                  =  go (Set.insert x processed) x' lvlX'  (Set.toList $ cycleOf x')   queue' idf
          | z ∈ processed                 =  go               processed  x  lvlX   zs'                         queue  idf
          | otherwise     = 
                            let isDf (y,_,mlvlY') = case mlvlY' of
                                  Nothing    -> True
                                  Just lvlY' -> lvlX > lvlY'
                                ys = assert ((∀) (Map.findWithDefault [] z cEdges) (\p@(y,_,_) -> isDf p ==  (not $ x ∈ reachableFromM idom (idomsOf y) Set.empty ))) $
                                     List.filter (\p@(y,_,_) -> (not $ y ∈ idf) ∧ isDf p) (Map.findWithDefault [] z cEdges)
                            in case Map.lookup z idom'' of
                                Nothing   -> go               processed  x lvlX  zs'                    (queue `with` ys) (foldr (Set.insert . fst) idf ys)
                                Just zNew -> go               processed  x lvlX (Set.fold (:) zs' zNew) (queue `with` ys) (foldr (Set.insert . fst) idf ys)
          where ((lvlX', x'), queue') = Prio.Max.deleteFindMax queue
                (z:zs') = zs
                with queue ys = foldr (\(y,lvlY,_) queue -> Prio.Max.insert lvlY y queue) queue ys
                fst (a,_,_) = a

        idom'  = invert''' idom
        idom'' = Map.mapWithKey (\z z's -> z's ∖ (cycleOf z)) idom'
        idomsOf y = case idom ! y of
          Nothing -> Set.empty
          Just y' -> cycleOf y'
        cycleOf x = Map.findWithDefault (Set.singleton x) x cycleOfM
        roots = foldr (\(n,m) roots -> if m == Nothing then Set.fromList [n] : roots else roots) cycles (Map.assocs idom)
        levelOf = Map.fromList [ (n,l) | nl <- treeLevel idom' roots, (n,l) <- nl]
        cEdges :: Map Node [(Node, Integer, Maybe Integer)]
        cEdges = foldr f Map.empty (edges graph)
          where f (y,z) cEdges = case idom ! y of
                           Nothing ->                                      Map.insertWith (++) z [(y,levelOf ! y, Nothing            )] cEdges
                           Just y' -> if z ∈ (cycleOf y') then cEdges else Map.insertWith (++) z [(y,levelOf ! y, Just $ levelOf ! y')] cEdges


idfViaCEdgesFast :: Graph gr => gr a b -> Map Node (Maybe Node) -> Set Node -> Set Node
idfViaCEdgesFast graph idom = idfViaCEdgesFastForCycles cycles graph idom
  where cycles = findCyclesM idom


nticdSliceViaCEdgesFast graph = \ms -> idf ms
  where sinks            = controlSinks graph
        sinkS            = fmap Set.fromList sinks
        sinkNodes        = (∐) [ sink | sink <- sinkS]
        nonSinkCondNodes = Map.fromList [ (n, succs) | n <- nodes graph, not $ n ∈ sinkNodes, let succs = suc graph n, length succs > 1 ]

        idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph

        cycles = (foldr Map.union Map.empty [ Map.fromSet (\n -> sink) sink | sink <- sinkS], sinkS)

        idf = idfViaCEdgesFastForCycles cycles graph idom

nticdSliceNumberedViaCEdgesFast graph = \ms -> idf ms
  where sinks            = controlSinks graph
        sinkS            = fmap Set.fromList sinks
        
        idom = Map.fromList $ iPDomForSinks sinks graph

        cycles = (foldr Map.union Map.empty [ Map.fromSet (\n -> sink) sink | sink <- sinkS], sinkS)

        idf = idfViaCEdgesFastForCycles cycles graph idom


nticdSliceViaCEdgesFastFor :: DynGraph gr => [[Node]] -> gr a b -> Map Node (Maybe Node) ->  Set Node -> Set Node
nticdSliceViaCEdgesFastFor roots graph idom =  \ms -> idf ms
  where sinkS = [ Set.fromList root | root@(_:_:_) <- roots ]
        cycles = (foldr Map.union Map.empty [ Map.fromSet (\n -> sink) sink | sink <- sinkS], sinkS)
        idf = idfViaCEdgesFastForCycles cycles graph idom


idomToDFFastLazy :: forall gr a b. Graph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node) -> Map Node (Set Node) -> Node -> (Set Node, Map Node (Set Node))
idomToDFFastLazy graph cycleOf idom' = \df x -> case Map.lookup x df of
    Just dfs -> (dfs, df)
    Nothing  -> let cycle = Map.findWithDefault (Set.singleton x) x cycleOf
                    combined = (local ∪ up) ∖ invalid
                    local = Set.fromList [ y            | x <- Set.toList cycle, 
                                                          y <- pre graph x
                                   ]
                    (up, df') =  Set.fold f (Set.empty, df) (invalid ∖ cycle)
                      where f z (up, df) = let (us,df') = idomToDFFastLazy graph cycleOf idom' df z in (up ∪ us, df')
                    
                    invalid =  Set.unions [ is | x <- Set.toList cycle, Just is <- [Map.lookup x idom'] ]
                in (combined, Map.fromSet (\x -> combined) cycle `Map.union` df')



mDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFTwoFinger graph = idomToDFFast graph $ imdomOfTwoFinger7 graph

imdomTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
imdomTwoFingerGraphP = cdepGraphP imdomTwoFingerGraph

imdomTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
imdomTwoFingerGraph = cdepGraph imdomTwoFingercd

imdomTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
imdomTwoFingercd = xDFcd mDFTwoFinger


isinkDFTwoFingerForSinks :: forall gr a b. DynGraph gr => [[Node]] -> gr a b ->  Map Node (Set Node)
isinkDFTwoFingerForSinks sinks graph =
    require (Set.fromList sinks == Set.fromList (controlSinks graph)) $
    idomToDFFastForRoots roots graph idom
  where 
        sinkNodes        = (∐) [ Set.fromList sink | sink <- sinks]
        nonSinkCondNodes = Map.fromList [ (n, succs) | n <- nodes graph, not $ n ∈ sinkNodes, let succs = suc graph n, length succs > 1 ]

        idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph
        roots = go (Map.assocs idom) [ sink | sink@(_:_:_) <- sinks ]
          where go []     roots = roots
                go ((n, m):as) roots = case m of 
                  Nothing -> go as ([n]:roots)
                  _       -> go as      roots

isinkDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkDFTwoFinger graph = isinkDFTwoFingerForSinks sinks graph
  where sinks = controlSinks graph


isinkdomTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
isinkdomTwoFingerGraphP = cdepGraphP isinkdomTwoFingerGraph

isinkdomTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
isinkdomTwoFingerGraph = cdepGraph isinkdomTwoFingercd

isinkdomTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
isinkdomTwoFingercd = xDFcd isinkDFTwoFinger



timDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timDFTwoFinger graph = idomToDFFast graph $ fmap (Set.map fst) $ timdomOfTwoFinger graph

itimdomTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
itimdomTwoFingerGraphP = cdepGraphP itimdomTwoFingerGraph

itimdomTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
itimdomTwoFingerGraph = cdepGraph itimdomTwoFingercd

itimdomTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
itimdomTwoFingercd = xDFcd timDFTwoFinger




type SmmnFunctional = Map (Node,Node,Node) (Set (T Node)) -> Map (Node,Node,Node) (Set (T Node))
type SmmnFunctionalGen gr a b = gr a b -> [Node] -> (Map Node (Set Node)) -> (Node -> Maybe Node) -> (Node -> [Node]) -> SmmnFunctional


fMust :: DynGraph gr => SmmnFunctionalGen gr a b
fMust graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     m1 ∈ (reachable ! x)
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]


fMustNoReachCheck :: DynGraph gr => SmmnFunctionalGen gr a b
fMustNoReachCheck graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX
                                                                     -- m1 ∊ (reachable x)
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]




fMustBefore :: DynGraph gr => SmmnFunctionalGen gr a b
fMustBefore graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                            m1 ∈ (reachable ! x),
                                                                      not $ m2 ∈ (reachable ! x)
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     m1 ∈ (reachable ! x),
                                                                     s ! (m1,m2,n) ⊇ Set.fromList [ (n, y) | y <- suc graph n, m2 ∈ (reachable ! y) ]
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]



fMay :: DynGraph gr => SmmnFunctionalGen gr a b
fMay graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     let toNxtCondX = toNextCond x,
                                                                     m1 ∈ (reachable ! x),
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) > 0
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]


fMay' :: DynGraph gr => SmmnFunctionalGen gr a b
fMay' graph condNodes reachable nextCond toNextCond s =
              (∐) [ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) ])]
                                | p <- condNodes,
                                  x <- suc graph p,
                                  let toNxtCondX = toNextCond x,
                                  m1 <- toNxtCondX,
                                  m2 <- nodes graph,
                                  not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                  ]
           ⊔      Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) > 0
                                             ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes
                  ]



type MustFunctional = Map Node (Set (Node, Node)) -> Map Node (Set (Node, Node))
type MustFunctionalGen gr a b = gr a b -> MustFunctional

mustOfLfp :: DynGraph gr => gr a b -> Map Node (Set (Node, Node))
mustOfLfp graph = (㎲⊒) init (fMustNaive graph)
  where init = Map.fromList [ (n, Set.empty) | n <- nodes graph]


mustOfGfp :: DynGraph gr => gr a b -> Map Node (Set (Node, Node))
mustOfGfp graph = (𝝂) init (fMustNaive graph)
  where init = Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- reachable n graph, m2 <- nodes graph]) | n <- nodes graph ]


fMustNaive :: DynGraph gr => MustFunctionalGen gr a b
fMustNaive graph  must =
                      Map.fromList [ (n, Set.fromList [(n,m2) | m2 <- nodes graph, m2 /= n ])                                             | n <- nodes graph]
                    ⊔ Map.fromList [ (n, Set.fromList [(m1,m2) | (m1,m2) <- Set.toList $ (∏) [ must ! x | x <- suc graph n ], m2 /= n])   | n <- nodes graph, suc graph n /= []]



combinedBackwardSliceSlow :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map (Node, Node) (Set Node) -> Set Node -> Set Node
combinedBackwardSliceSlow graph cd od = \ms -> (㎲⊒) ms f
  where f slice = slice
                ⊔ Set.fromList [ n | m <- Set.toList slice, n <- Set.toList $ cd ! m ]
                ⊔ Set.fromList [ n | m1 <- Set.toList slice, m2 <- Set.toList slice, m1 /= m2, n <- Set.toList $ Map.findWithDefault Set.empty (m1,m2) od ]

combinedBackwardSlice :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map (Node, Node) (Set Node) -> Set Node -> Set Node
combinedBackwardSlice graph cd od = \ms ->
     let result = slice Set.empty ms 
         slice s workset
             | Set.null workset = s
             | otherwise        = slice s' workset'
           where (m, workset0) = Set.deleteFindMin workset
                 s'  = Set.insert m s
                 new = (fromOD ∪ fromCD) ∖ s'
                 workset' = workset0 ∪ new

                 fromCD = Map.findWithDefault Set.empty m cd
                 fromOD
                   | Map.null od  = Set.empty
                   | otherwise    = (∐) [ (Map.findWithDefault Set.empty (m,m') od ) ∪ (Map.findWithDefault Set.empty (m', m) od) | m' <- Set.toList s ]
     in result


nticdSliceLazy :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node) -> Set Node -> Set Node
nticdSliceLazy graph cycleOf idom' = \ms ->
     let result = slice Map.empty Set.empty ms 
         slice df s workset 
             | Set.null workset = s
             | otherwise        = slice df' s' workset'
           where (m, workset0) = Set.deleteFindMin workset
                 s'  = Set.insert m s
                 new = fromNTICD ∖ s'
                 workset' = workset0 ∪ new

                 (fromNTICD, df') = idomToDFFastLazy graph cycleOf idom' df m
      in result

isinkDFNumberedForSinks :: forall gr a b. DynGraph gr => [[Node]] -> gr a b ->  Map Node (Set Node)
isinkDFNumberedForSinks sinks graph =
    require (Set.fromList sinks == Set.fromList (controlSinks graph)) $
    idomToDFFastForRoots roots graph idom
  where idom = Map.fromList $ iPDomForSinks sinks graph
        roots = go (Map.assocs idom) [ sink | sink@(_:_:_) <- sinks ]
          where go []     roots = roots
                go ((n, m):as) roots = case m of 
                  Nothing -> go as ([n]:roots)
                  _       -> go as      roots

isinkDFNumbered :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkDFNumbered graph = isinkDFNumberedForSinks sinks graph
  where sinks = controlSinks graph


nticdSliceNumbered :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdSliceNumbered graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFNumbered graph
        w     = Map.empty



ntscdMyDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = myDod graph

ntscdMyDodFastPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodFastPDomSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = myDodFastPDom graph


ntscdDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = dod graph



nticdSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFTwoFinger graph
        w     = Map.empty

nticdSliceFor :: DynGraph gr => [[Node]] -> gr a b -> Map Node (Maybe Node) ->  Set Node -> Set Node
nticdSliceFor roots graph idom = {- traceShow (Map.fold (\ns sum -> sum + Set.size ns) 0 nticd') $ -} combinedBackwardSlice graph nticd' w
  where nticd' = idomToDFFastForRoots roots graph idom
        w      = Map.empty


ntscdSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdSlice graph =  combinedBackwardSlice graph ntscd w
  where ntscd = mDFTwoFinger graph
        w     = Map.empty


nticdTimingSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdTimingSlice graph =  combinedBackwardSlice graph (nticd' ⊔ timing') w
  where nticd'  = isinkDFTwoFinger graph
        timing' = invert'' $ timingDependenceViaTwoFinger graph
        w     = Map.empty


ntscdTimingSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdTimingSlice graph =  combinedBackwardSlice graph (ntscd' ⊔ timing') w
  where ntscd'  = invert'' $ ntscdF3 graph
        timing' = invert'' $ timingDependenceViaTwoFinger graph
        w     = Map.empty



tscdSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSlice graph =  combinedBackwardSlice graph tscd' w
  where tscd' = invert'' $ tscdOfLfp graph
        w     = Map.empty


tscdSliceFast :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSliceFast graph msS = combinedBackwardSlice graph tscd' w msS
  where ms = Set.toList msS
        toMs   = rdfs ms graph
        graph' = foldr (flip delSuccessorEdges) graph ms
        tscd' =  timDFTwoFinger graph'
        w     = Map.empty


tscdSliceForTrivialSinks :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSliceForTrivialSinks graph =  combinedBackwardSlice graph tscd' w
  where tscd' = -- require ((∀) sinks (\sink -> length sink == 1)) $
                timDFTwoFinger graph
        w     = Map.empty
        sinks = controlSinks graph


nticdMyWodSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = invert'' $ nticdF3 graph
        w     = myWod graph

nticdMyWodFastSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodFastSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFTwoFinger graph
        w     = myWodFast graph

nticdMyWodPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodPDomSimpleHeuristic graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFTwoFinger graph
        w     = myWodFastPDomSimpleHeuristic graph

nticdMyWodPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodPDom graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFTwoFinger graph
        w     = myWodFastPDom graph


wccSliceViaWodTEILPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaWodTEILPDom graph = \ms -> let fromMs = (Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m graph ]) in combinedBackwardSlice graph empty w ms ∩ fromMs
  where empty = Map.empty
        w     = wodTEIL'PDom graph


wccSliceViaNticdMyWodPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaNticdMyWodPDomSimpleHeuristic g ms = s ∩ fromMs
  where gRev = grev g
        g'   = subgraph (Set.toList toMs) g
        s    = nticdMyWodPDomSimpleHeuristic g' ms
        toMs   = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m gRev ]
        fromMs = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m g    ]


wodTEILSliceViaNticd :: (Show (gr a b),  DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSliceViaNticd g =  \ms ->
    let toMs  = rdfs (Set.toList ms) g
        toMsS = Set.fromList toMs
        g'    = Set.fold (flip delSuccessorEdges) (subgraph toMs g) ms
        msSinks = [ sink | sink <- sinks, (∃) ms (\m -> m `elem` sink) ]
        idom'0 = id
               $ Map.union (Map.fromSet    (\m     -> Nothing) $ ms)
               $ Map.union (Map.mapWithKey (\x _   -> Nothing) $ Map.filterWithKey isEntry $ condNodes')
               $ Map.union (Map.mapWithKey (\x [z] ->                     assert (z /= x) $ Just z                   ) noLongerCondNodes)
               $ Map.union (Map.fromList  [ (x, case suc g' x of { [z] -> assert (z /= x) $ Just z  ; _ -> Nothing  }) | msSink <- msSinks, x <- msSink ])
               $ fmap intoMs
               $ restrict idom toMsS
          where isEntry x _ = case idom ! x of
                  Nothing -> False
                  Just z -> z ∈ sinkNodes
                intoMs n@(Nothing) = n
                intoMs n@(Just x)
                  | x ∈ toMsS = n
                  | otherwise = Nothing
        idom'0Rev   = invert''' idom'0
        processed'0 = reachableFrom idom'0Rev ms
        todo'0      = without nonSinkCondNodes' processed'0
        worklist'0  = Dequeue.fromList $ Map.assocs todo'0
        idom'1 = Map.union (fmap (\x -> Nothing) todo'0)
               $ idom'0
        idom'1Rev = invert''' idom'1
        idom'2 = isinkdomOftwoFinger8Up                  g'                                                               nonSinkCondNodes'   worklist'0  processed'0 idom'1Rev idom'1
        idom'  = isinkdomOfTwoFinger8DownSingleNodeSinks g' sinkNodes' (Map.filterWithKey (\x _ -> idom'2 ! x /= Nothing) nonSinkCondNodes')                                    idom'2
        sinks' = [ [m] | m <- Set.toList ms]
        sinkNodes' = ms
        (condNodes', noLongerCondNodes) =
              Map.partition isCond
            $ fmap (List.filter (∈ toMsS))
            $ restrict condNodes (toMsS ∖ ms)
          where isCond []  = False
                isCond [_] = False
                isCond _   = True
        nonSinkCondNodes' = condNodes'

        sinkS' = fmap Set.fromList sinks'
        cycleOf' =  Map.fromList [ (s, sink) | sink <- sinkS', s <- Set.toList $ sink ]
        
        idom'Direct = Map.fromList $ iPDomForSinks sinks' g'
    in -- (if idom' == idom'Direct then id else traceShow (ms, g, "*****", idom, idom'0, idom'1, idom'2, idom', fmap fromSet $ isinkdomOfTwoFinger8 g')) $ 
       assert (idom' == idom'Direct) $
       -- nticdSliceLazy g' cycleOf' (invert''' idom'Direct) ms
       idfViaCEdgesFastForCycles (cycleOf', sinkS') g' idom'Direct ms
  where
        sinks            = controlSinks g
        sinkNodes        = (∐) [ Set.fromList sink | sink <- sinks]
        condNodes        = Map.fromList [ (n, succs) | n <- nodes g, let succs = suc g n, length succs > 1 ]
        nonSinkCondNodes = without condNodes sinkNodes
        idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes g



myWodFastSlice :: ( DynGraph gr) => gr a b ->  Set Node  -> Set Node
myWodFastSlice graph =  combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = myWodFast graph


myWodFastPDomSimpleHeuristicSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
myWodFastPDomSimpleHeuristicSlice graph =  combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = myWodFastPDomSimpleHeuristic graph


wodMyEntryWodMyCDSlice :: forall gr a b. ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodMyEntryWodMyCDSlice graph = (if cdEdges == cdFromDomEdges then
                                   -- traceShow (length $ nodes graph, Set.size cdFromDomEdges, Set.size cdEdges, foldl (+) 0 (fmap Set.size cdFromDom), foldl (+) 0 (fmap Set.size cd))
                                  id
                                else
                                   -- traceShow (length $ nodes graph, Set.size cdFromDomEdges, Set.size cdEdges, foldl (+) 0 (fmap Set.size cdFromDom), foldl (+) 0 (fmap Set.size cd), graph)
                                  id
                               ) $
                               combinedBackwardSlice graph (invert'' $ nticdF3 graph ⊔ cd) w
  where cdFromDom    = myCDFromMyDom graph
        cd           = myCD graph
        w     = myEntryWodFast graph
        cdEdges        = Set.fromList $ edges $ trc $ (fromSuccMap cd        :: gr () ())
        cdFromDomEdges = Set.fromList $ edges $ trc $ (fromSuccMap cdFromDom :: gr () ())


wodTEILSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSlice graph = combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = wodTEIL' graph

wodTEILPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILPDomSlice graph = combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = wodTEIL'PDom graph


wodTEIL :: (DynGraph gr) => gr a b -> Map Node (Set (Node,Node))
wodTEIL graph = xodTEIL smmnMustBefore smmnMay graph
  where smmnMustBefore = smmnFMustWodBefore graph
        smmnMay  = smmnFMayWod graph


mmay :: (Graph gr) => gr a b -> Node -> Node -> Node -> Bool
mmay graph m2 m1 x =   (not $ m2 `elem` reachable x graph)
                     ∧ (      m1 `elem` reachable x graph)

mmayOf :: (DynGraph gr) => gr a b -> Node -> Map Node (Set Node)
mmayOf graph = \m2 ->
           let reachM2 = Set.fromList $ reachable m2 g' 
           in Map.fromSet (\x -> Set.empty) reachM2  `Map.union` reach
  where g' = grev graph
        reach = Map.fromList [(x, Set.fromList $ reachable x graph) | x <- nodes graph ]


mmayOf' :: (DynGraph gr) => gr a b -> Node -> Map Node (Set Node)
mmayOf' graph = \m1 ->   Map.fromList [ (x, Set.fromList [ m2 | m2 <- nodes graph, not $ m2 ∈ reach ! x ]) | x <- reachable m1 g' ]
                       ⊔ Map.fromList [ (x, Set.empty) | x <- nodes graph ]
  where g' = grev graph
        reach = Map.fromList [(x, Set.fromList $ reachable x graph) | x <- nodes graph ]

noJoins :: Graph gr => gr a b -> Map Node (Set Node) -> Bool
noJoins g m = (∀) (nodes g) (\x -> (∀) (nodes g) (\z -> (∀) (nodes g) (\v -> (∀) (nodes g) (\s ->
                if (z /= v) ∧ (x ∈ doms ! v) ∧ (x ∈ doms ! z) ∧ (v ∈ m ! s) ∧ (z ∈ m ! s) then (v ∈ doms ! z) ∨ (z ∈ doms ! v) else True
              ))))
  where doms = domsOf g m

stepsCL g dom = (∀) (nodes g) (\x -> (∀) (nodes g) (\y -> (∀) (nodes g) (\x' ->
             if (x' /= y) ∧ (y `elem` pre g x) ∧ (x' ∈ dom ! y) then (x'  ∈ dom ! x) else True
           )))

wodTEIL'PDom :: (DynGraph gr) => gr a b -> Map (Node, Node) (Set Node)
wodTEIL'PDom graph  =
     assert (unreachable == unreachableLeftDef ⊔ unreachableRightDef) $
     unreachable ⊔ nticd
  where nticd       = convert [ (n, m1, m2)  | m2 <- nodes graph,
                                               let gM2    = delSuccessorEdges graph m2,
                                               let gToM2  = subgraph (reachable m2 (grev gM2)) gM2,
                                               let nticd' = isinkDFNumberedForSinks [[m2]] gToM2,
                                               (m1, ns) <- Map.assocs nticd', n <- Set.toList ns, n /= m1
                      ]

        unreachable = convert [ (n, m1, m2) | n <- Set.toList condNodes,
                                              m2 <- Set.toList $ reach ! n, m2 /= n,
                                              m1 <- Set.toList $ (Set.unions [ reach ! x | x <- suc graph n, not $ m2 ∈ reach ! x ]) , m1 /= n, m1 /= m2
                      ]
          where reach = Map.fromList [(x, Set.fromList $ reachable x graph) | x <- nodes graph ]
                graph' = grev graph
                condNodes = Set.fromList [ n | n <- nodes graph, length (suc graph n) > 1 ]


        unreachableLeftDef = Map.fromList [ ((m1, m2), Set.fromList [ n | n <- nodes graph,  n /= m1, n /= m2,
                                                              assert ( (not $ m1 ∈ m2may ! n) ↔ (not $ m1 ∈ m2onedom n)) True,
                                                                       (not $ m1 ∈ m2may ! n),
                                                                       (∃) (suc graph n) (\x ->       m1 ∈ m2may ! x)
                                                ]
                                     ) | m2 <- nodes graph,
                                         let m2may = mmay m2,
                                         let m2onedom = onedomOf m2may,
                                         m1 <- nodes graph, m1 /= m2
                    ]
          where mmay = mmayOf graph

        unreachableRightDef = Map.fromList [ ((m2, m1), ns) | ((m1,m2),ns) <- Map.assocs unreachableLeftDef]


        convert :: [(Node, Node, Node)] ->  Map (Node,Node) (Set Node)
        convert triples = runST $ do
            let keys = [ (m1,m2) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2]

            assocs <- forM keys (\(m1,m2) -> do
              ns <- newSTRef Set.empty
              return ((m1,m2),ns)
             )

            let m = assert (List.sort keys == keys)
                  $ Map.fromDistinctAscList assocs

            forM_ triples (\(n,m1,m2) -> do
               let nsRef  = m ! (m1,m2)
               let nsRef' = m ! (m2,m1)
               modifySTRef nsRef  (Set.insert n)
               modifySTRef nsRef' (Set.insert n)
             )

            m' <- forM m readSTRef

            return m'


wodTEIL' :: (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
wodTEIL' graph = Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
               ⊔ (fmap Set.fromList $ invert' $ fmap Set.toList wTEIL )
  where wTEIL = wodTEIL graph




mustBeforeMaximalDef :: (DynGraph gr) => gr a b -> Map Node (Set (Node, Node))
mustBeforeMaximalDef graph =
                Map.fromList [ (n, Set.empty) | n <- nodes graph]
              ⊔ Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- nodes graph,
                                                            m2 <- nodes graph,
                                                            n /= m1, n /= m2, m1 /= m2,
                                                            (∀) paths (\path -> (m1,m2) `inPathBefore` (n,path))
                                                ]
                               ) | n <- nodes graph, let paths = maximalPaths ! n ]
  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        inPathBefore = inPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.

smmnFMustWod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustWod graph = smmnGfp graph fMust

smmnFMustWodBefore :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustWodBefore graph = smmnGfp graph fMustBefore


smmnFMayWod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMayWod graph = smmnLfp graph fMay'


smmnFMustDod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustDod graph = smmnLfp graph fMust

smmnFMustNoReachCheckDod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustNoReachCheckDod graph = smmnLfp graph fMustNoReachCheck


smmnFMayDod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMayDod graph = smmnLfp graph fMay'




smmnGfp :: (DynGraph gr ) => gr a b -> SmmnFunctionalGen gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnGfp graph f = -- traceShow graph $ 
                  (𝝂) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m1,m2,p), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m1,m2,p), Set.fromList [ (p,x) | x <- suc graph p]) | m1 <- nodes graph, m2 <- nodes graph, m2 /= m1, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable = Map.fromList [(x, Set.fromList $ Data.Graph.Inductive.Query.DFS.reachable x graph) | x <- nodes graph] 
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

smmnLfp :: (DynGraph gr) => gr a b -> SmmnFunctionalGen gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnLfp graph f = -- traceShow graph $ 
                  (㎲⊒) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m1,m2,p), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable = Map.fromList [(x, Set.fromList $ Data.Graph.Inductive.Query.DFS.reachable x graph) | x <- nodes graph] 
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

{- a combinator to generate order dependencies in the style of [2]

  [2] Slicing for modern program structures: a theory for eliminating irrelevant loops
      TorbenAmtoft
      https://doi.org/10.1016/j.ipl.2007.10.002
-}
xodTEIL:: DynGraph gr => (Map (Node, Node, Node ) (Set (T Node))) ->
                         (Map (Node, Node, Node ) (Set (T Node))) ->
                         gr a b ->
                         Map Node (Set (Node,Node))
xodTEIL smmnMustBefore smmnMay graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- nodes graph,
                                                  m2 <- nodes graph,
                                                  Set.size (smmnMay ! (m1,m2,n)) > 0, n /= m2,
                                                  Set.size (smmnMay ! (m2,m1,n)) > 0, n /= m1,
                                                  let s12n = smmnMustBefore ! (m1,m2,n),
                                                  let s21n = smmnMustBefore ! (m2,m1,n),
                                                  Set.size s12n + Set.size s21n > 0
                                      ]
                     ) | n <- condNodes
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


{- a combinator to generate order dependencies in the style of [1] -}
xod smmnMust s graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  Set.size (s ! (m1,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  Set.size (s ! (m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  let s12n = smmnMust ! (m1,m2,n),
                                                  let s21n = smmnMust ! (m2,m1,n),
                                                  Set.size s12n > 0,
                                                  Set.size s21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


myXod smmnMust s graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  Set.size (s ! (m1,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  Set.size (s ! (m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  let s12n = smmnMust ! (m1,m2,n),
                                                  Set.size s12n > 0,
                                                  Set.size s12n < (Set.size $ Set.fromList $ suc graph n)
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


myEntryWodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myEntryWodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- isinkdomCycles,
                                       let entries = entriesFor cycle,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       assert (length cycle > 1) True,
                                       let color = colorLfpFor graph m1 m2,
                                       let ns = Set.fromList [ n | n <- entries,
                                                                   n /= m1 ∧ n /= m2,
                                                           assert (m1 ∊ (suc isinkdomTrc n)) True,
                                                           assert (m2 ∊ (suc isinkdomTrc n)) True,
                                                                   myDependence color n
                                                ]
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]
        condsIn cycle    = [ n | n <- cycle, length (suc graph n) > 1]
        myDependence = myDependenceFor graph

symmetric m = (∐) [ Map.fromList [((m1,m2), ns), ((m2,m1),ns) ] |  ((m1,m2),ns) <- Map.assocs m ]

mySinkWodFast  :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
mySinkWodFast graph = (∐) [ Map.fromList [ ((m1, m2), Set.fromList [ n ] ) ] |
                                                                           cycle <- isinkdomCycles, length cycle > 1, n <- cycle, n `elem` condNodes,
                                                                           xl <- suc graph n,
                                                                           xr <- suc graph n,
                                                                           m1 <- Set.toList $ dom ! xl,
                                                                           m1 /= n,
                                                                           m2 <- cycle,
                                                                           m2 /= n,
                                                                           m2 /= m1,
                                                                           not $ m2 ∈ dom ! xr
                                                                           -- not $ m2 `elem` (suc cdG n)
                      ]
  where condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n, x /= n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        dom = myDom graph
        cd  = myCD graph
        cdG = fromSuccMap cd :: gr () ()
        cdGTrc = trc cdG

-- fMyDom graph _ _ nextCond toNextCond = f 
--   where f sinkdomOf =
--                       Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
--                     ⊔ Map.fromList [ (y, Set.fromList $ toNextCond y)               | y <- nodes graph]
--                     ⊔ Map.fromList [ (y,  (∏) [ sinkdomOf ! x | x <- suc graph n ]) | y <- nodes graph, Just n <- [nextCond y]]
-- myDomOfGfp graph = domOfGfp graph fMyDom

fAllDomNaive graph all = f 
  where f alldomOf =
                      Map.fromList [ (y, Map.fromList [ (y, all) ]             )  | y <- nodes graph]
                    ⊔ Map.fromList [ (y, fmap (Set.delete y) $ (∏) [ alldomOf ! x | x <- suc graph y ])  | y <- nodes graph, suc graph y /= []]

allDomNaiveGfp graph = (𝝂) init (fAllDomNaive graph all)
  where init = Map.fromList [ (y, Map.empty                                  ) | y <- nodes graph]
             ⊔ Map.fromList [ (y, Map.fromList [ (m, all) | m <- reachable y]) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph
        all = Set.fromList $ nodes graph

myDomNaiveGFP graph =
                      Map.fromList [ (y, Set.fromList [ m | m <- nodes graph, (∀) (suc graph y) (\x -> Map.member m (allDom ! x)  ∧  y ∈ allDom ! x ! m ) ]) | y <- nodes graph ]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- toNextCond y])                                                                              | y <- nodes graph, not $ y `elem` condNodes]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,                          Map.member m (allDom ! y)  ∧  y ∈ allDom ! x ! m   ]) | y <- nodes graph,
                    --                                                                                                                                      not $ y `elem` condNodes,
                    --                                                                                                                                           [x] <- [suc graph y]
                    --   ]

  where allDom = allDomNaiveGfp graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        -- nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph


fMyDomNaive' graph = f 
  where f mydomOf = -- traceShow mydomOf $
                      Map.fromList [ (y, Set.fromList [y])                                               | y <- nodes graph]
                    -- ⊔ Map.fromList [ (y, mydomOf ! m ) | y <- nodes graph, [m] <- [nub $ suc graph y] ]
                    -- ⊔ Map.fromList [ (y, mydomOf ! m ) | y <- nodes graph, [m] <- [nub $ pre graph y] ]
                    ⊔ Map.fromList [ (y, Set.fromList [ m |  m <- nodes graph,
                                                             let inner = [ x | x <- suc graph y,       y ∈ allMay ! x ! m ],
                                                             let outer = [ x | x <- suc graph y, not $ y ∈ allMay ! x ! m ],
                                                             (∀) (suc graph y) (\x ->
                                                                  m ∈ mydomOf ! x
                                                               -- ∧ y ∈ allMay ! x ! m
                                                               -- ∧  (m `elem` (suc graph y)) → ((∀) (suc graph y) (\x' -> (not $ x' `elem` (suc graph m))))
                                                               -- -- ∧  (m `elem` (pre graph y)) → ((length $ nub $ pre graph y) == 1)
                                                             )
                                                          -- ∧  (∀) inner (\i ->
                                                          --      (∀) outer (\o -> not $ y ∈ allMay ! i ! o)
                                                          --    )
                                                          ∧  (∀) inner (\i ->
                                                               (∀) outer (\o -> not $ y ∈ allMay ! i ! o)
                                                             )
                                                      ])  | y <- nodes graph, suc graph y /= []]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m |  m <- nodes graph, (∀) (suc graph y) (\x -> m ∈ mydomOf ! x   ∧   (∀) (pre graph x) (\y' -> m ∈ mydomOf ! y') ) ])  | y <- nodes graph, suc graph y /= []]
        allMay = allMayNaiveLfp graph

myDomNaive'Gfp graph = (𝝂) init (fMyDomNaive' graph)
  where init = Map.fromList [ (y, all)       | y <- nodes graph]
        all =  Set.fromList $ nodes graph



fMayNaive graph _ _ nextCond toNextCond = f 
  where f maydomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y, (∐) [ maydomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]
mayNaiveGfp graph = domOfGfp graph fMayNaive


fAllMayNaive graph all = f 
  where f alldomOf =
                      Map.fromList [ (y, Map.fromList [ (y, all) ]             )  | y <- nodes graph]
                    ⊔ Map.fromList [ (y, fmap (Set.delete y) $ (∐) [ alldomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]

allMayNaiveLfp graph =  -- (𝝂) init (fAllMayNaive graph all)
                       (㎲⊒) empty (fAllMayNaive graph all)
  where empty = Map.fromList [ (y, Map.fromList [ (m, Set.empty) | m <- nodes graph ]) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph
        all = Set.fromList $ nodes graph


myMayNaiveLfp graph =
                      Map.fromList [ (y, Set.fromList [ m | m <- nodes graph, (∀) (suc graph y) (\x -> Map.member m (allMay ! x)  ∧  y ∈ allMay ! x ! m ) ]) | y <- nodes graph ]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- toNextCond y])                                                                              | y <- nodes graph, not $ y `elem` condNodes]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,                          Map.member m (allDom ! y)  ∧  y ∈ allDom ! x ! m   ]) | y <- nodes graph,
                    --                                                                                                                                      not $ y `elem` condNodes,
                    --                                                                                                                                           [x] <- [suc graph y]
                    --   ]

  where allMay = allMayNaiveLfp graph

fMayNotNaive graph _ _ nextCond toNextCond = f 
  where f maynotdomOf = Map.fromList [ (y, Set.delete y $ all)                                        | y <- nodes graph, suc graph y == []]
                      ⊔ Map.fromList [ (y, Set.delete y $ (∏) [ maynotdomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]
        all = Set.fromList $ nodes graph

notOfGfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
notOfGfp graph f = (𝝂) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
             ⊔ Map.fromList [ (y, all ∖ (Set.fromList $ reachable y)) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph
        all = Set.fromList $ nodes graph

        
mayNotNaiveGfp graph = notOfGfp graph fMayNotNaive






-- fMyDomNaive graph my = f 
--   where f mydomOf =
--                       Map.fromList [ (y, Map.fromList [ (y, my) ]             )  | y <- nodes graph]
--                     ⊔ Map.fromList [ (y, fmap (Set.delete y) $ (∏) [ mydomOf ! x | x <- suc graph y ])  | y <- nodes graph, suc graph y /= []]

-- myDomNaiveGfp graph = (𝝂) init (fMyDomNaive graph my)
--   where init = Map.fromList [ (y, Map.empty                                  ) | y <- nodes graph]
--              ⊔ Map.fromList [ (y, Map.fromList [ (m, my) | m <- reachable y]) | y <- nodes graph]
--         condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
--         reachable x = suc trncl x
--         trncl = trc graph
--         my = Set.fromList $ nodes graph


myDom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
myDom graph =
              toSuccMap $
              (trc :: gr () () -> gr () ()) $
              fromSuccMap $
              Map.fromList [ (n, Set.empty)        | n <- nodes graph ]
            ⊔ Map.fromList [ (n, Set.fromList [m]) | n <- nodes graph, not $ n `elem` condNodes, [m] <- [suc graph n] ]
            ⊔ (∐) [ Map.fromList [ (n, Set.fromList [ m ] ) ]
            | n <- condNodes,
            -- | cycle <- isinkdomCycles,
            --   length cycle > 1,
            --   n <- cycle,
            --   n `elem` condNodes,
              -- let gn   = delPredecessorEdges graph n,
              -- let domn = (fmap Set.singleton$ Map.fromList $ iDom gn n) `Map.union` Map.fromList [ (m, Set.empty) | m <- nodes graph],
              -- Just m <- [foldM1 (lca domn) (suc graph n)]
              let gn  = delSuccessorEdges graph n,
              let isinkdomN  = fmap fromSet $ isinkdomOfSinkContraction gn,
              Just m <- [foldM1 (lca isinkdomN) (suc graph n)]
 ]
  where condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]


cdFromDom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node)
cdFromDom graph dom = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
                    ⊔ Map.fromList [ (n, Set.fromList [ m |                xl <- suc graph n,
                                                                           xr <- suc graph n,
                                                                           m <- Set.toList $ dom ! xl,
                                                                           m /= n,
                                                                           not $ m ∈ dom ! xr
                                         ]
                                      )
                                    | n <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


someprop g =  smmnmay' == smmnmay
  where trcg = trc g
        smmnmay  = Set.fromList [ ((m1,m2,n),(nn,x)) | ((m1,m2,n),nx) <- Map.assocs $ smmnFMustWod g, m1 /= m2, m1 /= n, m2 /= n, (nn,x) <- Set.toList nx, m2 `elem` suc trcg m1 ]
        smmnmay' = Set.fromList [ ((m1,m2,n),(n,x))  | n <- nodes g, (length $ suc g n) > 1,
                                                       let gn  =        delSuccessorEdges   g n,
                                                       let gn' = grev $ delPredecessorEdges g n,
                                                          
                                                       let pdom = sinkdomOfGfp gn,
                                                       let pmay = mayNaiveGfp  gn,

                                                       let dom  = sinkdomOfGfp gn',
                                                       let may  = mayNaiveGfp  gn',
                                                       m1 <- nodes g,  x <- suc g n, m2 <- suc trcg m1, m1 /= m2, n /= m1, n /= m2,
                                                       ((m1 ∈ pdom ! x) ∧ (not $ m1 ∈ pmay ! m2))
                                                 ∨     ((m1 ∈ dom ! m2) ∧ (not $ m2 ∈ pmay ! x))
                                                 ∨     ((m1 ∈ pdom ! m2) ∧ (m1 ∈ dom ! m2))
                   ]

        -- pr = exampleSimpleNoUniqueEndNodeWithChoice2
        -- g0 = tcfg pr
        -- g = insEdge (10,1,NoOp)  $ insEdge (6,9,NoOp) g0
myWodFromMay :: forall gr a b. (DynGraph gr) =>  gr a b -> Map (Node, Node) (Set Node)
myWodFromMay graph =  --      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
                      myEntryWodFast graph
                   ⊔ (∐) [ Map.fromList [ ((m1,m2), Set.fromList [n]) ] | (n, m1, m2) <- mywod ]
  where mywod =  [ (n, m1, m2) | cycle <- isinkdomCycles,
                                 length cycle > 1,
                                 let condsInCycle     = condsIn cycle,
                                 let cycleGraph = subgraph cycle graph,
                                 n <- condsInCycle,
                                 let gn   = delSuccessorEdges cycleGraph n,
                                 let pdom = sinkdomOfGfp gn,
                                 let pmay = mayNaiveGfp gn,
                                 let zs = (∏) [ pdom ! x | x <- suc cycleGraph n ],
                                 let ys = (∏) [ pmay ! x | x <- suc cycleGraph n ],
                                 -- traceShow (n, cycleGraph, pdom, pmay, zs, ys) True,
                                 x <- suc cycleGraph n,
                                 m1 <- Set.toList $ pdom ! x,
                                 m1 `elem` cycle,
                                 m1 /= n,
                                 m2 <- cycle,
                                 m2 /= m1, m2 /= n,
                                 (not $ m2 ∈ pmay ! x)  ∨  ((not $ m1 ∈ zs)  ∧  (m2 ∈ ys))
                 ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]
        condsIn cycle    = [ n | n <- cycle, length (suc graph n) > 1]

cdFromMyWod graph =  (∐) [ Map.fromList [ (n, Set.fromList [m] ) ]  | ((m1,m2),ns) <- Map.assocs $ myWodFast graph, n <- Set.toList ns, m <- [m1,m2] ]

myCDFromMyDom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
myCDFromMyDom graph = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
                    ⊔ Map.fromList [ (n, Set.fromList [ m |                xl <- suc graph n,
                                                                           xr <- suc graph n,
                                                                           m <- Set.toList $ dom ! xl,
                                                                           m /= n,
                                                                           not $ m ∈ dom ! xr
                                         ]
                                      )
                                    |  cycle <- isinkdomCycles, length cycle > 1, n <- cycle, n `elem` condNodes ]
  where dom       = myDom graph
        condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG


myCD :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
myCD graph = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
           ⊔ Map.fromList [ (n, myCDForNode graph n) | cycle <- isinkdomCycles, length cycle > 1, n <- cycle, n `elem` condNodes ]
  where condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]

myCDForNode :: forall gr a b. DynGraph gr => gr a b -> Node -> (Set Node)
myCDForNode graph n = Set.fromList [ m |       -- m <- Set.toList $ reachableFrom isinkdom (Set.fromList [n]) Set.empty,
                                                  let gn  = delSuccessorEdges graph n,
                                                  let isinkdomN  = isinkdomOfSinkContraction gn,
                                                  -- let (z,relevant) = foldr1 (lcaR (fmap fromSet isinkdomN)) [(x, Set.empty) | x <- suc graph n],
                                                  -- m <- Set.toList relevant, m /= z
                                                  m <- nodes graph,
                                                  (∃) (suc graph n) (\x ->       m ∈ reachableFrom isinkdomN (Set.fromList [x])),
                                                  (∃) (suc graph n) (\x -> not $ m ∈ reachableFrom isinkdomN (Set.fromList [x]))
                                   ]
  where lcaR = lcaRMyCDForNode

myWod graph = myXod sMust s3 graph
  where sMust = smmnFMustWod graph
        s3    = snmF3 graph

myWodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myWodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- isinkdomCycles,
                                       let conds   = condsIn    cycle,
                                       let entries = entriesFor cycle,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       let color = colorLfpFor graph m1 m2,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entries  ++ cycle,
                                                                   n /= m1 ∧ n /= m2,
                                                           assert (m1 ∊ (suc isinkdomTrc n)) True,
                                                           assert (m2 ∊ (suc isinkdomTrc n)) True,
                                                                   myDependence color n
                                                                  -- let s12n = sMust ! (m1,m2,n),
                                                                  -- Set.size s12n > 0,
                                                                  -- Set.size s12n < (Set.size $ Set.fromList $ suc graph n)
                                                ]
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]
        condsIn cycle    = [ n | n <- cycle, length (suc graph n) > 1]
        myDependence = myDependenceFor graph



rotatePDomAroundNeighbours :: forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> Map Node (Maybe Node) -> (Node, Node) -> Map Node (Maybe Node)
rotatePDomAroundNeighbours  graph condNodes pdom e@(n,m) =
      id
    $ require (n /= m)
    $ require (hasEdge graph e)
    $ require (pdom  ! n == Nothing)
    $ assert  (nodes graphm == (nodes $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (edges graphm == (edges $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (pdom' ! m == Nothing)
    $ pdom'
  where graphm = delSuccessorEdges graph m
        preM = Set.fromList $ pre graph m
        pdom'0   = id
                 $ Map.union (Map.fromSet (const $ Just m) $ Set.delete m preM)
                 $ ipdomM''
        ipdomM'' = Map.insert m Nothing
                 $ pdom
        pdom' = id
              -- $ traceShow pdom'0 
              -- $ traceShow [ (n, sol, pd) | (n,sol) <- Map.assocs $ toSuccMap $ (immediateOf solution :: gr () ()),
              --                              let pd = pdom'0 ! n, pd /= sol]
              $ assert ((∀) (nodes graph) (\x ->
                                   if isReachableFromTreeM ipdomM'' n x then
                                             reachableFromTree  (fmap toSet pdom'0) x
                                          ⊇  reachableFromTree             solution x
                                   else 
                                             reachableFromTree  (fmap toSet pdom'0) x
                                         ==  reachableFromTree             solution x
                                       )
                       )
              $ if ((∀) preM (\p -> p == n)) then
                    id
                  $ pdom'0
                else
                    id 
                  $ isinkdomOfTwoFinger8DownSingleNodeSinks graphm (Set.fromList [m]) relevantCondNodesM pdom'0
          where 
                condNodesM = Map.delete m condNodes
                relevantCondNodesM = assert (fromFind == slow) $
                                     fromFind
                  where slow     = Map.filterWithKey (\x _ -> isReachableFromTreeM ipdomM'' n x    ∧   (not $ x ∈ preM)) condNodesM
                        fromFind = findAll (Set.toList $ (Map.keysSet condNodesM) ∖ preM) Map.empty
                          where findAll     [] relevant = relevant
                                findAll (x:xs) relevant = find [x] xs relevant
                                find []         [] relevant = relevant
                                find path@(x:_) xs relevant
                                    | x == n                 = find path'     xs' relevant'
                                    | Map.member x relevant  = find path'     xs' relevant'
                                    | otherwise = case ipdomM'' ! x of
                                                    Nothing -> find path'     xs' relevant
                                                    Just x' -> find (x':path) xs  relevant
                                  where (path', xs') = case xs of
                                                         []     -> ([], [])
                                                         (y:ys) -> ([y], ys)
                                        relevant' = foldr (uncurry Map.insert) relevant [ (y,succs) | y <- path, not $ y ∈ preM, Just succs <- [Map.lookup y condNodesM] ]


                solution = fromIdom m $ iDom (grev graphm) m



rotatePDomAroundArbitrary :: forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> Map Node (Maybe Node) -> (Node, Node) -> Map Node (Maybe Node)
rotatePDomAroundArbitrary  graph condNodes ipdom (n, m) = 
      id
    $ require (n /= m)
    $ require (ipdom  ! n == Nothing)
    $ assert  (nodes graphm == (nodes $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (edges graphm == (edges $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (ipdom' ! m == Nothing)
    $ ipdom'

  where ipdomM''  = Map.insert m Nothing ipdom
        succs     = [ x | x <- suc graph n, isReachableFromTreeM ipdomM'' m x]
        graphm = delSuccessorEdges graph m
        condNodesM = Map.delete m condNodes

        ipdom' = assert ((∀) (nodes graph) (\x ->
                                   if isReachableFromTreeM ipdomM'' n x then
                                             reachableFromTree  (fmap toSet ipdomM''') x
                                          ⊇  reachableFromTree                solution x
                                   else 
                                             reachableFromTree  (fmap toSet ipdomM''') x
                                         ==  reachableFromTree                solution x
                                       )
                       )
               $ assert (relevantCondNodesM == Map.filterWithKey (\x _ -> isReachableFromTreeM ipdomM'' n x) condNodesM)
               $ isinkdomOfTwoFinger8DownSingleNodeSinks graphm (Set.fromList [m]) relevantCondNodesM ipdomM'''

        (relevantCondNodesM, ipdomM''') = 
                if List.null succs then
                  let (processed0, relevantCondNodesM) = findProcessedAndRelevant (nodes graphm) (Set.singleton m) Map.empty
                      ipdomM''' = isinkdomOftwoFinger8Up graphm condNodesM worklist0 processed0 imdom0Rev imdom0
                        where nIsCond    = Map.member n condNodes
                              [nx]       = suc graphm n
                              imdom0     = (if nIsCond then id else Map.insert n (Just nx)) $
                                           (fmap (const Nothing) relevantCondNodesM) `Map.union` ipdomM''
                              imdom0Rev  = invert''' imdom0
                              worklist0  = Dequeue.fromList $ Map.assocs relevantCondNodesM
                  in (relevantCondNodesM, ipdomM''')
                else
                   let relevantCondNodesM = findRelevant (Map.keys condNodesM) Map.empty
                       ipdomM''' = assert (z /= Nothing) $ Map.insert n z ipdomM''
                         where z = foldM1 (lca ipdomM'') succs
                  in (relevantCondNodesM, ipdomM''')


        findProcessedAndRelevant (x:xs) processed relevant = find [x] xs processed relevant
                  where find []         [] processed relevant =  (processed, relevant)
                        find path@(x:_) xs processed relevant
                            | Map.member x   relevant  = find path'     xs' processed  relevant'
                            |            x ∈ processed = find path'     xs' processed' relevant
                            | otherwise = case ipdomM'' ! x of
                                            Nothing ->   find path'     xs' processed  relevant'
                                            Just x' ->   find (x':path) xs  processed  relevant
                          where (path', xs') = case xs of
                                                []     -> ([], [])
                                                (y:ys) -> ([y], ys)
                                processed' = foldr          Set.insert  processed                    path
                                relevant'  = foldr (uncurry Map.insert) relevant  [ (y,succs) | y <- path, Just succs <- [Map.lookup y condNodesM] ]

        findRelevant     [] relevant =             relevant
        findRelevant (x:xs) relevant = find [x] xs relevant
                  where find []         [] relevant = relevant
                        find path@(x:_) xs relevant
                            | x == n                 = find path'     xs' relevant'
                            | Map.member x relevant  = find path'     xs' relevant'
                            | otherwise = case ipdomM'' ! x of
                                            Nothing -> find path'     xs' relevant
                                            Just x' -> find (x':path) xs  relevant
                          where (path', xs') = case xs of
                                                []     -> ([], [])
                                                (y:ys) -> ([y], ys)
                                relevant' = foldr (uncurry Map.insert) relevant [ (y,succs) | y <- path, Just succs <- [Map.lookup y condNodesM] ]

        solution = fromIdom m $ iDom (grev graphm) m


rotatePDomAround :: forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> Map Node (Maybe Node) -> (Node, Node) -> Map Node (Maybe Node)
rotatePDomAround graph condNodes pdom nm
  | hasEdge graph nm = rotatePDomAroundNeighbours  graph condNodes pdom nm
  | otherwise        = rotatePDomAroundArbitrary   graph condNodes pdom nm



myWodFastPDomForIterationStrategy :: forall gr a b. (DynGraph gr) => (gr a b -> [Node] -> [[Node]]) -> gr a b -> Map (Node,Node) (Set Node)
myWodFastPDomForIterationStrategy strategy graph =
        convert $
        [ (n,m1,m2)  |                                        cycle <- isinkdomCycles,
                                                              length cycle > 1,
                                                              let cycleS = Set.fromList cycle,
                                                              let entries = entriesFor cycle,
                                                              let nodesTowardsCycle = dfs (head cycle : entries) graph,
                                                              let condsTowardCycle = condsIn nodesTowardsCycle,
                                                              let condsInCycle = restrict condsTowardCycle cycleS,
                                                              let cycleGraph = subgraph nodesTowardsCycle graph,
                                                              let paths = strategy graph cycle,
                                                      require ( (∐) [ Set.fromList path | path <- paths] == Set.fromList cycle ) True,
                                                              let (m20:others) = concat paths,
                                                              let pairs = zip (m20:others) others,
                                                              let pdom0 = fromIdomM m20 $ iDom (grev cycleGraph) m20,
                                                              let pdoms = zip (m20:others) (scanl (rotatePDomAround cycleGraph condsTowardCycle) pdom0 pairs),
                                                              n <- [ n | (n,_) <- Map.assocs condsInCycle] ++ entries,
                                                              (m2, pdom) <- pdoms,
                                                              let pdom' = fromIdomM m2  $ iDom (grev cycleGraph) m2,
                                                       assert (pdom == pdom') True,
                                                              n /= m2,
                                                              let (z,relevant) = lcaRKnownM pdom n (suc graph n),
                                                       assert (Just z == foldM1 (lca pdom) (suc graph n)) True,
                                                       assert (Set.fromList relevant == Set.fromList [ m1 | x <- suc graph n, m1 <- Set.toList $ (reachableFrom (fmap toSet pdom)  (Set.fromList [x])), isReachableBeforeFromTreeM pdom m1 z x ] ) True,
                                                              m1 <- relevant, m1 /= z,
                                                              m1 /= n,
                                                              m1 ∈ cycleS,
                                                       assert (m1 ∊ (suc isinkdomTrc n)) True,
                                                       assert (m2 ∊ (suc isinkdomTrc n)) True
      ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        convert :: [(Node, Node, Node)] ->  Map (Node,Node) (Set Node)
        convert triples = runST $ do
            let keys = [ (m1,m2) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2]

            assocs <- forM keys (\(m1,m2) -> do
              ns <- newSTRef Set.empty
              return ((m1,m2),ns)
             )

            let m = assert (List.sort keys == keys)
                  $ Map.fromDistinctAscList assocs

            forM_ triples (\(n,m1,m2) -> do
               let nsRef = m ! (m1,m2)
               modifySTRef nsRef (Set.insert n)
             )

            m' <- forM m readSTRef

            return m'

        isinkdom = isinkdomOfTwoFinger8 graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]
        condsIn ns    = Map.fromList [ (n, succs) | n <- ns, let succs = suc graph n, length succs > 1]


-- towardsCycle graph cycleS n = dfs [n] graph


myWodFastPDom :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myWodFastPDom graph = myWodFastPDomForIterationStrategy none graph
  where none graph cycle = [ [n] | n <- cycle ]


myWodFastPDomSimpleHeuristic :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myWodFastPDomSimpleHeuristic graph = myWodFastPDomForIterationStrategy simple graph
  where simple :: gr a b -> [Node] -> [[Node]]
        simple graph cycle = from (joinNodes ++ nonJoinNodes) Set.empty []
          where (joinNodes, nonJoinNodes) = partition (\n -> length (pre graph n) > 1) cycle
                joinNodesSet = Set.fromList joinNodes
                from []        seen result = result
                from (n:nodes) seen result = from [ n | n <- nodes, not $ n ∈ seen' ] seen' (app newPath result)
                  where newPath = forward n seenN
                          where seenN   = (Set.insert n seen)
                        seen' = seen ∪ newSeen
                          where newSeen = Set.fromList newPath
                        app []      oldPaths = oldPaths
                        app newPath oldPaths = app' oldPaths
                          where newPathLast  = last newPath
                                app' [] = [newPath]
                                app' (oldPath@(oldPathFirst:oldPathRest) : oldPaths ) 
                                  | hasEdge graph (newPathLast, oldPathFirst) = (newPath ++ oldPath) : oldPaths
                                  | otherwise                                 = oldPath : app' oldPaths
                forward n seen 
                    | List.null succs        = [n]
                    | List.null nonJoinSuccs = let n' = head    joinSuccs in n : (forward n' (Set.insert n' seen))
                    | otherwise              = let n' = head nonJoinSuccs in n : (forward n' (Set.insert n' seen))
                  where succs = [ m | m <- suc graph n, not $ m ∈ seen]
                        (joinSuccs, nonJoinSuccs) = partition (∈ joinNodesSet) succs

dod graph = xod sMust s3 graph
  where sMust = smmnFMustDod graph
        s3    = snmF3Lfp graph

myDod graph = myXod sMust s3 graph
  where sMust = smmnFMustDod graph
        s3    = snmF3Lfp graph


myDodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myDodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- imdomCycles,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       let color = colorLfpFor graph m1 m2,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entriesFor cycle,
                                                           assert (n /= m1 ∧ n /= m2) True,
                                                           assert (m1 ∊ (suc imdomTrc n)) True,
                                                           assert (m2 ∊ (suc imdomTrc n)) True,
                                                                  myDependence color n
                                                ]
                   ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        imdom = imdomOfTwoFinger7 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∊ cycle]
        myDependence = myDependenceFor graph

myDodFastPDom :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myDodFastPDom graph =
        convert $
        [ (n,m1,m2)  |                                        cycle <- imdomCycles, length cycle > 1,
                                                              let cycleS = Set.fromList cycle,
                                                              let entries = entriesFor cycleS, not $ entries == [],
                                                              let nodesTowardsCycle = dfs entries graph,
                                                              let cycleGraph = subgraph nodesTowardsCycle graph,
                                                              m2 <- cycle,
                                                              let graph' = delSuccessorEdges cycleGraph m2,
                                                              let pdom = fmap fromSet $ imdomOfTwoFinger7 graph',
#ifdef PDOMUSESDF
                                                              (m1, ns) <- Map.assocs $ idomToDFFastForRoots [[m2]] graph' pdom,
                                                              m1 ∈ cycleS,
                                                              n <- Set.toList ns,
#else
                                                              n <- entries,
                                                              let (z,relevant) = lcaRKnownM pdom n (suc graph n),
                                                       assert (Just z == foldM1 (lca pdom) (suc graph n)) True,
                                                       assert (Set.fromList relevant == Set.fromList [ m1 | x <- suc graph n, m1 <- Set.toList $ (reachableFrom (fmap toSet pdom)  (Set.fromList [x])), isReachableBeforeFromTreeM pdom m1 z x ] ) True,
                                                              m1 <- relevant, m1 /= z,
                                                              m1 ∈ cycleS,
#endif
                                                       assert (m1 /= n) True,
                                                       assert (m2 /= n) True,
                                                       assert (m2 /= m1) True,
                                                       assert (m1 ∊ (suc imdomTrc n)) True,
                                                       assert (m2 ∊ (suc imdomTrc n)) True
      ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        convert :: [(Node, Node, Node)] ->  Map (Node,Node) (Set Node)
        convert triples = runST $ do
            let keys = Set.toList $ Set.fromList [ (m1,m2) | (_,m1,m2) <- triples]

            assocs <- forM keys (\(m1,m2) -> do
              ns <- newSTRef Set.empty
              return ((m1,m2),ns)
             )

            let m = assert (List.sort keys == keys)
                  $ Map.fromDistinctAscList assocs

            forM_ triples (\(n,m1,m2) -> do
               let nsRef = m ! (m1,m2)
               modifySTRef nsRef (Set.insert n)
             )

            m' <- forM m readSTRef

            return m'

        imdom = imdomOfTwoFinger7 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG

        entriesFor cycle = [ n | n <- condNodes, not $ n ∈ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∈ cycle]




dodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
dodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc imdomTrc n),
                                                  m2 ∊ (suc imdomTrc n),
                                                  -- allImdomReachable (Set.fromList [n]) n (Set.fromList [m1,m2]),
                                                  let s12n = sMust ! (m1,m2,n),
                                                  let s21n = sMust ! (m2,m1,n),
                                                  Set.size s12n > 0,
                                                  Set.size s21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where sMust = smmnFMustNoReachCheckDod graph
        imdom = imdomOfTwoFinger7 graph
        -- allImdomReachable seen n ms
        --   | Set.null ms   = True
        --   | n ∈ ms        = allImdomReachable               seen  n (Set.delete n ms)
        --   | Set.null next = False
        --   | n' ∈ seen     = False
        --   | otherwise     = allImdomReachable (Set.insert n seen) n' ms
        --      where next = imdom ! n
        --            [n'] = Set.toList next
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



{- this algorithm does *not* work, see: Program.Examples.dodSuperFastCounterExample6 -}
dodSuperFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
dodSuperFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc imdomTrc n),
                                                  m2 ∊ (suc imdomTrc n),
                                                  (∃) (suc graph n) (\x -> mustBeforeAny (m1,m2,x)),
                                                  (∃) (suc graph n) (\x -> mustBeforeAny (m2,m1,x))
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where imdom = imdomOfTwoFinger7 graph
        pis   = possibleIntermediateNodesFromiXdom graph imdom
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())
        mustBeforeAny (m1,m2,x) = mustBeforeAnySeen (Set.fromList [x]) x
          where mustBeforeAnySeen seen n
                  | n == m2 = False
                  | n == m1 = True
                  | Set.null next = False
                  | m2 ∈ toNext = False
                  | otherwise = mustBeforeAnySeen (Set.insert n seen) n'
                      where next = imdom ! n
                            toNext   = pis ! n
                            [n']     = Set.toList next
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


data Color = Undefined | White | Black | Uncolored deriving (Show, Ord, Eq, Bounded, Enum)

instance JoinSemiLattice Color where
  Undefined `join` x         = x
  x         `join` Undefined = x

  Uncolored `join` x         = Uncolored
  x         `join` Uncolored = Uncolored

  White     `join` White     = White
  Black     `join` Black     = Black

  x         `join` y         = Uncolored

instance BoundedJoinSemiLattice Color where
  bottom = Undefined


instance PartialOrd.PartialOrd Color where
  c1 `leq` c2 =  c1 ⊔ c2 == c2

dodColoredDag :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDag graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc trcGraph m2),
                                                  m2 ∊ (suc trcGraph m1),
                                                  dependence n m1 m2
                               ]
                      ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                   ]
  where trcGraph = trc graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph


myDependenceFor graph color n = whiteChild ∧ otherChild
          where 
                whiteChild = (∃) (suc graph n) (\x -> color ! x == White)
                otherChild = (∃) (suc graph n) (\x -> assert ( color ! x /= Undefined) 
                                                      color ! x /= White)


dependenceFor graph n m1 m2 = whiteChild ∧ blackChild
          where color = colorFor graph n m1 m2
                whiteChild = (∃) (suc graph n) (\x -> color ! x == White)
                blackChild = (∃) (suc graph n) (\x -> color ! x == Black)

colorFor graph n m1 m2 = color
          where color = fst $ colorFor n (init, Set.fromList [m1,m2])
                  where init =             Map.fromList [ (m1, White), (m2, Black) ]
                               `Map.union` Map.fromList [ (n, Uncolored) | n <- nodes graph]
                colorFor :: Node -> (Map Node Color, Set Node) -> (Map Node Color, Set Node)
                colorFor n (color, visited)
                  | n ∈ visited = (color, visited)
                  | otherwise   = ( Map.insert n ((∐) [ color' ! x | x <- suc graph n ]) color', visited')
                      where (color', visited') = foldr colorFor (color, Set.insert n visited) (suc graph n)



colorFunctionalFor :: forall gr a b. DynGraph gr => gr a b -> Node -> Node -> Map Node Color -> Map Node Color
colorFunctionalFor graph m1 m2 color =
      color
    ⊔ Map.fromList [ (m1, White), (m2, Black) ]
    ⊔ Map.fromList [ (n, (∐) [ color ! x | x <- suc graph n ]) | n <- nodes graph, n /= m1, n /= m2 ]

colorLfpFor graph m1 m2 =  (㎲⊒) (Map.fromList [ (n, Undefined) | n <- nodes graph]) f
  where f = colorFunctionalFor graph m1 m2

dodColoredDagFixed :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDagFixed graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc imdomTrc n),
                                                  m2 ∊ (suc imdomTrc n),
                                                  dependence n m1 m2
                               ]
                      ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                   ]
  where trcGraph = trc graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph
        imdom = imdomOfTwoFinger7 graph
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())


dodColoredDagFixedFast :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDagFixedFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((mm1,mm2), ns) | cycle <- imdomCycles,
                                       (m1,m2) <- unorderedPairsOf cycle,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entriesFor cycle,
                                                           assert (n /= m1 ∧ n /= m2) True,
                                                           assert (m1 ∊ (suc imdomTrc n)) True,
                                                           assert (m2 ∊ (suc imdomTrc n)) True,
                                                                   dependence n m1 m2
                                                ],
                                       (mm1,mm2) <- [(m1,m2),(m2,m1)]
                   ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph
        imdom = imdomOfTwoFinger7 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∊ cycle]

        unorderedPairsOf []     = []
        unorderedPairsOf (x:xs) = [ (x,y) | y <- xs ] ++ unorderedPairsOf xs


wodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
wodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  let sMay12n = sMay ! (m1,m2,n),
                                                  let sMay21n = sMay ! (m2,m1,n),
                                                  ((n /= m2) ∧ (Set.size sMay12n > 0))  ∨  ((n == m1) ∧ (m2 ∊ suc graphTrc n)),
                                                  ((n /= m1) ∧ (Set.size sMay21n > 0))  ∨  ((n == m2) ∧ (m1 ∊ suc graphTrc n)),
                                                  let sMust12n = sMust ! (m1,m2,n),
                                                  let sMust21n = sMust ! (m2,m1,n),
                                                  Set.size sMust12n > 0 ∨ Set.size sMust21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where sMust = smmnFMustNoReachCheckDod graph
        sMay  = smmnFMayWod graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        graphTrc = trc $ graph



wodDef :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
wodDef graph = Map.fromList [ ((m1,m2), Set.fromList [ p | p <- condNodes,
                                                           (∃) (maximalPaths ! p) (\path -> (m1,m2) `mayInPathBefore` (p,path)),
                                                           (∃) (maximalPaths ! p) (\path -> (m2,m1) `mayInPathBefore` (p,path)),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m2,m1) `inPathBefore` (x,path))
                                                           ∨ (∀) (maximalPaths ! x) (\path -> (m1,m2) `inPathBefore` (x,path))
                                                           )
                                        ]
                                )
                            | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPathBefore = inPathForBefore graph doms
        mayInPathBefore = mayInPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're ju

dodDef :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodDef graph = Map.fromList [ ((m1,m2), Set.fromList [ p | p <- condNodes,
                                                           (∀) (maximalPaths ! p) (\path ->   m1 `inPath` (p,path)
                                                                                            ∧ m2 `inPath` (p,path)),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m1,m2) `inPathBefore` (x,path))
                                                           ),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m2,m1) `inPathBefore` (x,path))
                                                           )
                                        ]
                                )
                            | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        inPathBefore = inPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.

inPathForBefore :: DynGraph gr => gr a b -> Map Node [(Node, [Node])] -> (Node,Node) -> (Node, MaximalPath) -> Bool
inPathForBefore graph' doms (m1,m2) (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  thispath@(MaximalPath []            endScc endNodes@(end:_))
                    | m1 ∊ endScc  = -- traceShow (entries, thispath) $ 
                                          (∀) entries (\entry -> let domsEnd = (doms ! entry) `get` end
                                                                     domsm2   = (doms ! entry) `get` m2 in
                                                                 (entry /= end || m1 == entry) && m1 ∊ domsEnd && ((not $ m2 ∊ endScc) ∨ (m1 ∊ domsm2))
                                          )
                                          ∨ ((m1 ∊ endNodes) ∧
                                             (∀) entries (\entry ->  let domsm2   = (doms ! entry) `get` m2 in ((not $ m2 ∊ endScc) ∨ (m1 ∊ domsm2)))
                                          )

                    | otherwise         = -- traceShow (entries, thispath) $
                                          False
                inPathFromEntries entries  thispath@(MaximalPath (scc:prefix)  endScc endNodes)
                    | m1 ∊ scc = -- traceShow (entries, thispath) $
                                      (∀) entries (\entry ->
                                        (∀) exits (\exit -> let domsexit = (doms ! entry) `get` exit 
                                                                domsm2   = (doms ! entry) `get` m2   in
                                             (entry /= exit || m1 == entry) && m1 ∊ domsexit && ((not $ m2 ∊ scc) ∨ (m1 ∊ domsm2))
                                        )
                                      )
                                      ∨
                                      ((m1 ∊ endNodes) ∧
                                       (∀) entries (\entry ->  let domsm2   = (doms ! entry) `get` m2 in ((not $ m2 ∊ scc) ∨ (m1 ∊ domsm2)))
                                      )
                    | otherwise    =  -- traceShow (entries, thispath) $
                                      (not $ m2 ∊ scc) ∧ inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = case  List.lookup key assocs of
                                   Nothing -> error $ "lookup " ++ (show key) ++ "  " ++ (show assocs)
                                   Just v  -> v



mayInPathForBefore :: DynGraph gr => gr a b -> Map Node [(Node, [Node])] -> (Node,Node) -> (Node, MaximalPath) -> Bool
mayInPathForBefore graph' doms (m1,m2) (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  thispath@(MaximalPath []            endScc endNodes@(end:_))
                    | m1 ∊ endScc ∧ m2 ∊ endScc  = -- traceShow (entries, thispath) $
                                      (∃) entries (\entry -> let domsm1 = (doms ! entry) `get` m1 in
                                                             not $ m2 ∊ domsm1
                                      )
                    | m1 ∊ endScc  = -- traceShow (entries, thispath) $
                                          True
                    | otherwise         = -- traceShow (entries, thispath) $
                                          False
                inPathFromEntries entries  thispath@(MaximalPath (scc:prefix)  endScc endNodes)
                    | m1 ∊ scc ∧ m2 ∊ scc = -- traceShow (entries, thispath) $
                                      (∃) entries (\entry -> let domsm1 = (doms ! entry) `get` m1 in
                                                             not $ m2 ∊ domsm1
                                      )
                    | m1 ∊ scc = -- traceShow (entries, thispath) $
                                      True
                    | m2 ∊ scc = -- traceShow (entries, exits, thispath) $
                                      (∃) entries (\entry ->
                                        (∃) exits (\exit -> let domsexit = (doms ! entry) `get` exit in
                                                                not $ m2 ∊ domsexit
                                        )
                                      )
                                    ∧ inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                    | otherwise     = -- traceShow (entries, thispath) $
                                      inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = case  List.lookup key assocs of
                                   Nothing -> error $ "lookup " ++ (show key) ++ "  " ++ (show assocs)
                                   Just v  -> v





{- Utility functions -}
toNextCondNode graph n = toNextCondSeen [n] n
    where toNextCondSeen seen n = case suc graph n of
            []    -> seen
            [ n'] -> if n' ∊ seen then seen else toNextCondSeen (n':seen) n'
            (_:_) -> seen

nextCondNode graph n = nextCondSeen [n] n
    where nextCondSeen seen n = case suc graph n of
            []    -> Nothing
            [ n'] -> if n' ∊ seen then Nothing else nextCondSeen (n':seen) n'
            (_:_) -> Just n


nextLinearSinkNode graph sink n = next n
    where next n = case suc graph n of
            []    -> error $ "did not start from an 'entry' node for sink " ++ (show sink)
            [ n'] -> if n' ∊ sink then n' else next n'
            (_:_) -> error $ "reached a cond node before sink " ++ (show sink)



toNextRealCondNode graph n = toNextCondSeen [n] n
    where toNextCondSeen seen n = case List.delete n $ nub $ suc graph n of
            []    -> seen
            [ n'] -> if n' ∊ seen then seen else toNextCondSeen (n':seen) n'
            (_:_) -> seen

nextRealCondNode graph n = nextCondSeen [n] n
    where nextCondSeen seen n = case List.delete n $ nub $ suc graph n of
            []    -> Nothing
            [ n'] -> if n' ∊ seen then Nothing else nextCondSeen (n':seen) n'
            (_:_) -> Just n



nextJoinNode graph n = nextJoinSeen [n] n
    where nextJoinSeen seen n = case pre graph n of
            (_:_) -> Just n
            _     -> case suc graph n of
              []     -> Nothing
              [ n' ] -> if n' ∊ seen then Nothing else nextJoinSeen (n':seen) n'
              (_:_)  -> Nothing

nextJoinNodes graph n = nextJoinSeen [n] n []
    where nextJoinSeen seen n joins = case suc graph n of
              []     -> joins'
              [ n' ] -> if n' ∊ seen then joins' else nextJoinSeen (n':seen) n' joins'
              (_:_)  -> joins'
            where joins' = case pre graph n of
                     (_:_) -> n:joins
                     _     -> joins



prevRealCondNodes graph start = prevCondsF (List.delete start $ nub $ pre graph start)
    where prevCondsF front = concat $ fmap prevConds front
          prevConds  n
            | n == start = [n]
            | otherwise  = case List.delete n $ nub $ suc graph n of
                [ n'] -> prevCondsF (List.delete n $ nub $ pre graph n)
                (_:_) -> [n]




prevCondImmediateNodes graph n = [ p | p <- pre graph n, case suc graph p of { [_] -> False ; _ -> True } ]


prevCondNodes graph start = prevCondsF (pre graph start)
    where prevCondsF front = concat $ fmap prevConds front
          prevConds  n
            | n == start = [n]
            | otherwise  = case suc graph n of
                [ n'] -> prevCondsF (pre graph n)
                (_:_) -> [n]

prevCondsWithSuccNode graph start = prevCondsF [(p, start) | p <- pre graph start]
    where prevCondsF front = concat $ fmap prevConds front
          prevConds  (n,x)
            | n == start = [(n,x)]
            | otherwise  = case suc graph n of
                [ n'] -> prevCondsF [ (p,n) | p <- pre graph n]
                (_:_) -> [(n,x)]


prevCondsWithSuccNode' graph start = prevCondsF [(p, start) | p <- pre graph start] []
    where prevCondsF []    found = found
          prevCondsF front found = prevCondsF newFront (newFound ++ found)
            where (newFound, notFound) = partition isCond front
                  isCond (n,x)
                    | n == start = True
                    | otherwise = case suc graph n of
                        [ n'] -> False 
                        (_:_) -> True
                  newFront = [ (p,n) | (n,x) <- notFound, p <- pre graph n]


prevRepresentantNodes graph start =
      case pre graph start of
        (_:_:_) -> Just start
        []      -> Just start
        [n]     -> prevRepresentant [start] n start
    where prevRepresentant seen n m -- invariance : n is only predecessor of m, m is no join node
              | n ∊ seen  = Nothing
              | otherwise = case suc graph n of
                  (_:_:_) -> Just m
                  [m']    -> assert (m' == m) $
                             case pre graph n of
                               [n']    -> prevRepresentant (n:seen) n' n
                               _       -> Just n


data SinkPath = SinkPath { prefix :: [[Node]], controlSink :: [Node] } deriving Show

data MaximalPath          = MaximalPath { mPrefix :: [[Node]],  mScc :: [Node], mEndNodes  :: [Node] } deriving Show
data MaximalPathCondensed = MaximalPathCondensed {
  mcPrefix :: [Node],   -- of Nodes in the condensed graph
  mcScc ::  Node,       --    Node  in the condensed graph
  mcEndNodes :: [Node]  -- of Nodes in the original graph
 }

sinkPathsFor :: DynGraph gr => gr a b -> Map Node [SinkPath]
sinkPathsFor graph = Map.fromList [ (n, sinkPaths n) | n <- nodes graph ]
    where
      sccs = scc graph
      sccOf m =  the (m ∊) $ sccs
      sinks = controlSinks graph     -- TODO: dont repeat scc computation
      condensed = condensation graph --       or here
--      trcCondensed = trc condensed
      sinkPaths n = [ SinkPath { prefix = fmap (fromJust . (lab condensed)) revPath, controlSink = sink } | sink <- sinks , revPath <- revPaths (nodeMap ! (sccOf n)) ( nodeMap ! sink) ]
      revPaths :: Node -> Node -> [[Node]]
      revPaths ns sink
       | ns == sink    = [[]]
       | otherwise     = fmap (ns:) [ path | ns' <- suc condensed ns, path <- revPaths ns' sink ]
      nodeMap = Map.fromList [ (ns, n) | (n, ns) <- labNodes condensed ]




maximalPathsFor :: DynGraph gr => gr a b -> Map Node [MaximalPath]
maximalPathsFor graph = maximalPathsForNodes graph [ n | p <- condNodes, n <- suc graph p ++ [p]]
    where
      condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]

maximalPathsForNodes :: DynGraph gr => gr a b -> [Node] -> Map Node [MaximalPath]
maximalPathsForNodes graph relevantNodes = Map.fromList [ (n, maximalPaths n) | n <- relevantNodes]
    where
      sccs = scc graph
      sccOf m =  the (m ∊) $ sccs
      condensed = condensation graph --       or here
      maximalPaths n = [ MaximalPath { mPrefix   = reverse $  fmap (fromJust . (lab condensed)) $ mcPrefix revPath,
                                       mScc      =                 (fromJust . (lab condensed)) (mcScc revPath),
                                       mEndNodes = reverse $ mcEndNodes revPath
                                     }
                       |  revPath <- revPaths [(nodeMap ! (sccOf n))] ]
      revPaths :: [Node] -> [MaximalPathCondensed]
      revPaths (ns:rest)
         | suc condensed ns == []   =    pathsToCycleInNs
                                      ++ pathsToSinkInNs
         | (length nsNodes ) > 1    =    pathsToCycleInNs
                                      ++ pathsToSinkInNs
                                      ++ pathsToSuccessors
         | let [n] = nsNodes in
           n ∊ suc graph n     =    [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = nsNodes } ] -- ==  pathsToCycleInNs
                                      ++ pathsToSuccessors
         | otherwise                =    pathsToSuccessors
       where
         pathsToCycleInNs  = [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = cycle } | cycle <- cyclesInScc nsNodes graph ]
         pathsToSinkInNs   = [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = sink  } | sink  <- [ [n] | n <- nsNodes, length (suc graph n) == 0] ]
         pathsToSuccessors = [ path | ns' <- suc condensed ns, path <- revPaths (ns':ns:rest)]
         nsNodes = fromJust $ lab condensed ns
      nodeMap = Map.fromList [ (ns, n) | (n, ns) <- labNodes condensed ]


-- Speed this up, using http://dx.doi.org/10.1137/0205007 or http://dx.doi.org/10.1137/0205007 ?!?! See http://stackoverflow.com/questions/546655/finding-all-cycles-in-graph
cyclesInScc scc@(n:_) graph = cyclesFromIn scc graph n
cyclesFrom graph n = cyclesFromIn (nodes graph) graph n
cyclesFromIn nodes graph n = cyclesFromPath [n]
    where
      cyclesFromPath path@(n:_) =      [ n':(takeWhile (/=n') path) | n' <- suc graph n, n' ∊ nodes,       n' ∊ path]
                                   ++  [ cycle                      | n' <- suc graph n, n' ∊ nodes, not $ n' ∊ path, cycle <- cyclesFromPath (n':path) ]



-- Examples
      
-- shows necessity of change in the "linear path section" rule
exampleLinear :: Graph gr => gr () ()
exampleLinear = mkGraph [(-27,()),(-23,()),(-10,()),(4,()),(21,()),(25,()),(26,())] [(-27,21,()),(-23,-10,()),(-23,25,()),(21,-27,()),(25,-27,()),(25,-27,()),(25,4,()),(25,21,()),(26,-27,()),(26,-23,()),(26,-10,()),(26,4,()),(26,21,()),(26,25,())]

exampleLinearSimple :: Graph gr => gr () ()
exampleLinearSimple =
    mkGraph [(n,()) | n <- [1..5]]
            [(1,2,()), (1,4,()),
             (4,5,()), (4,3,()),
             (2,3,()), (3,2,())
            ]

exampleLinearSimpleLong :: Graph gr => gr () ()
exampleLinearSimpleLong =
    mkGraph [(n,()) | n <- [1..7]]
            [(1,2,()), (1,4,()),
             (4,5,()), (4,3,()),
             (2,3,()), (3,6,()), (6,7,()), (7,2,())
            ]




data Reachability  = Unreachable | Unknown | FixedSteps Integer | FixedStepsPlusOther Integer Node | UndeterminedSteps deriving (Show, Eq)
instance JoinSemiLattice Reachability where
  Unreachable   `join` x           = x
  x             `join` Unreachable = x

  FixedSteps x `join` FixedSteps y
    | x == y    = FixedSteps x
    | otherwise = UndeterminedSteps

  FixedStepsPlusOther x n  `join` FixedStepsPlusOther y m
    | x == y ∧ n == m  = FixedStepsPlusOther x n 
    | otherwise = UndeterminedSteps

{-
  FixedStepsPlusOther x n  `join` FixedSteps          y   = {- assert (y >= x) $ -} FixedStepsPlusOther x n
  FixedSteps          x    `join` FixedStepsPlusOther y m = {- assert (x >= y) $ -} FixedStepsPlusOther y m
-}

  x         `join` y         = UndeterminedSteps

instance BoundedJoinSemiLattice Reachability where
  bottom = Unreachable

instance Ord Reachability where
  Unreachable   `compare` Unreachable = EQ
  Unreachable   `compare` x           = LT
  x             `compare` Unreachable = GT

  FixedSteps x `compare` FixedSteps y = compare x y
  FixedStepsPlusOther x n  `compare` FixedStepsPlusOther y m = case cnm of
      EQ -> compare x y
      _  -> cnm
    where cnm  = compare n m

  FixedSteps _ `compare` FixedStepsPlusOther _ _ = LT
  FixedStepsPlusOther _ _ `compare` FixedSteps _ = GT
 
  UndeterminedSteps `compare` UndeterminedSteps = EQ
  UndeterminedSteps `compare` x                 = GT
  x                 `compare` UndeterminedSteps = LT
  

plusAt :: Node -> Reachability -> Integer ->  Reachability
plusAt n r y = r `plus` y where
  (FixedSteps x)            `plus` y = FixedSteps (x+y)
  (FixedStepsPlusOther x m) `plus` y = FixedStepsPlusOther (x+y) m
  (Unreachable)             `plus` y = Unreachable
  (UndeterminedSteps)       `plus` y = FixedStepsPlusOther y n


joinPlus ::  Reachability -> Integer ->  Reachability
joinPlus r y = r `plus` y where
  (FixedSteps x)            `plus` y = FixedSteps (x+y)
  (FixedStepsPlusOther x n) `plus` y = FixedStepsPlusOther (x+y) n
  r                         `plus` y = r


type SmnTimingEquationSystem =
       Map (Node,Node) (Map (Node,Node) Reachability)
type SmnTimingEquationSystemGen gr a b =
       gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node])
    -> SmnTimingEquationSystem

solveTimingEquationSystem ::  SmnTimingEquationSystem -> SmnTimingEquationSystem
solveTimingEquationSystem s = if (s == s') then s else solveTimingEquationSystem s'
          where s' =     Map.fromList [ ((m,p), Map.fromList [ ((p,x), r) | ((p',x), rpx) <- Map.assocs smp,
                                                                            assert (p == p') True,
                                                                            let r = case rpx of
                                                                                      FixedStepsPlusOther i q -> let smq = s ! (m,q)
                                                                                                                     rmq = (∐) [ r | r <- Map.elems smq ]
                                                                                                                 in case rmq of
                                                                                                                      FixedSteps j             -> FixedSteps (1+i+j)
                                                                                                                      FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+i+j) q'
                                                                                                                      _            -> rpx
                                                                                      _                       -> rpx
                                                            ]
                                        )
                                      | ((m,p), smp) <- Map.assocs s ]


timingF3EquationSystem :: DynGraph gr => SmnTimingEquationSystemGen gr a b
timingF3EquationSystem graph condNodes reachable nextCond toNextCond =
                   Map.fromList [ ((m,p), Map.fromList  [ ((p,x), FixedSteps i) | x <- suc graph p,
                                                                                  (i,m2) <- (zip [0..] (toNextCondInOrder x)), m2 == m ]
                                  ) | m <- nodes graph, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), reachability) | x <- (suc graph p),
                                                                           m ∊ reachable x,
                                                                           Just n <- [nextCond x],
                                                                           let plus = plusAt n,
                                                                           let toNextCondX = toNextCond x,
                                                                           not $ m ∊ toNextCondX,
                                                                           let stepsToN = List.genericLength toNextCondX - 1,
                                                                           let reachabilityFromN = FixedStepsPlusOther 0 n,
                                                                           let reachability = reachabilityFromN `plus` stepsToN
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]
  where toNextCondInOrder = reverse . toNextCond

timingF3EquationSystem' :: DynGraph gr => SmnTimingEquationSystemGen gr a b
timingF3EquationSystem' graph condNodes _ nextCond toNextCond =
                        Map.fromList [ ((m,p), Map.empty) | m <- nodes graph, p <- condNodes]
                 ⊔ (∐) [ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), FixedSteps i) ]) ]
                         | p <- condNodes, x <- suc graph p,    (i,m) <- (zip [0..] (toNextCondInOrder x))
                       ]
                 ⊔ (∐) [ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), reachability) ]) ]
                         | p <- condNodes, x <- suc graph p,    Just n <- [nextCond x],
                                                                           m <- reachable x graph,
                                                                           let plus = plusAt n,
                                                                           let toNextCondX = toNextCond x,
                                                                           not $ m ∊ toNextCondX,
                                                                           let stepsToN = List.genericLength toNextCondX - 1,
                                                                           let reachabilityFromN = FixedStepsPlusOther 0 n,
                                                                           let reachability = reachabilityFromN `plus` stepsToN
                        ]
  where toNextCondInOrder = reverse . toNextCond


snmTimingEquationSystem :: DynGraph gr => gr a b -> SmnTimingEquationSystemGen gr a b -> SmnTimingEquationSystem
snmTimingEquationSystem graph f = f graph condNodes reachable nextCond toNextCond
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

snmTimingF3 :: DynGraph gr => gr a b -> SmnTimingEquationSystem
snmTimingF3 graph     = snmTimingEquationSystem graph timingF3EquationSystem'

snmTimingSolvedF3 :: DynGraph gr => gr a b -> SmnTimingEquationSystem
snmTimingSolvedF3 graph = snmTimingEquationSystem graph timingSolvedF3EquationSystem
  where timingSolvedF3EquationSystem graph condNodes reachable nextCond toNextCond = solveTimingEquationSystem $ timingF3EquationSystem' graph condNodes reachable nextCond toNextCond

timingF3summary :: DynGraph gr => gr a b -> Map Node (Map Node Reachability)
timingF3summary     = timingXsummary snmTimingF3

timingSolvedF3summary :: DynGraph gr => gr a b -> Map Node (Map Node Reachability)
timingSolvedF3summary = timingXsummary snmTimingSolvedF3

timingXsummary :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Map Node Reachability)
timingXsummary snmTiming graph = 
      Map.fromList [ (n, Map.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Map.fromList [ (m,r `joinPlus` 1 ) | m <- nodes graph,
                                                          m /= n,
                                                          let rmn = s ! (m,n),
                                                          let r = (∐) [ r | r <- Map.elems rmn ]
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


timingF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingF3dependence     = timingXdependence snmTimingF3

timingSolvedF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSolvedF3dependence = timingXdependence snmTimingSolvedF3

timingSolvedF3sparseDependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSolvedF3sparseDependence = timingXsparseDependence snmTimingSolvedF3


timingXdependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
timingXdependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            let rmn = s ! (m,n),
                                            (length [ r | r <- Map.elems rmn, r /= Unreachable ]) > 1,
                                            let r = (∐) [ r | r <- Map.elems rmn ],
                                            r == UndeterminedSteps
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



timingXsparseDependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
timingXsparseDependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            m /= n,
                                            let rmn = s ! (m,n),
                                            (length [ r | r <- Map.elems rmn, r /= Unreachable ]) > 1,
                                            (∃) (Map.elems rmn) (\r ->
                                              (∃) (Map.elems rmn) (\r' ->  r ⊔ r' == UndeterminedSteps ∧ ( 
                                                                             case (r,r') of
                                                                               (FixedStepsPlusOther _ u, FixedStepsPlusOther _ v)  -> (not $ n ∊ [u,v]) ∧ (u /= v)
                                                                               _                                                   -> True
                                                                           )
                                              )
                                            )
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        trncl = trc graph
        nextCond = nextCondNode graph



type TimeDomFunctional = Map Node (Map Node (Set Integer)) ->  Map Node (Map Node (Set Integer))
type TimeDomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> TimeDomFunctional

tdomOfLfp :: DynGraph gr => gr a b -> TimeDomFunctionalGen gr a b -> Map Node (Set (Node, Integer))
tdomOfLfp graph f = fmap (\m -> Set.fromList [ (n, steps) | (n, ss) <- Map.assocs m, steps <- Set.toList ss ]) $
        (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Map.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

fTimeDom :: DynGraph gr => TimeDomFunctionalGen gr a b
fTimeDom graph _ _ nextCond toNextCond = f 
  where f timeDomOf = fmap (fmap (Set.singleton . Set.findMin)) $ 
                      Map.fromList [ (y, Map.fromList [(y, Set.fromList [0]    )]) | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Map.fromList [(n, Set.fromList [steps]) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                                   | y <- nodes graph
                                                                                     
                                   ]
                    ⊔ Map.fromList [ (y,
                                         fmap (Set.map (\s -> s + (steps + 1))) $
                                         Map.filter (not . Set.null) $
                                         (∏) [ timeDomOf ! x | x <- suc graph n ]
                                     )
                                                                                   | y <- nodes graph,
                                                                                     Just n <- [nextCond y],
                                                                                     let steps = (toInteger $ length $ toNextCond y) - 1
                                   ]
timdomOfLfp graph = tdomOfLfp graph fTimeDom

tscdOfLfp :: DynGraph gr => gr a b -> Map Node (Set Node)
tscdOfLfp graph = Map.fromList [ (n, Set.fromList [ m | timdom <- timdoms,  (m, steps) <- Set.toList timdom, (∃) timdoms (\timdom' -> not $ (m, steps) ∈ timdom') ]) |
                    n <- nodes graph,
                    let timdoms = [ timdom ! x | x <- suc graph n]
                  ]
  where timdom = timdomOfLfp graph


type TimeDomFunctionalR = Map Node (Map Node Reachability) ->  Map Node (Map Node Reachability)
type TimeDomFunctionalGenR gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> TimeDomFunctionalR

tdomRLfpF :: DynGraph gr => gr a b -> TimeDomFunctionalGenR gr a b -> Map Node (Map Node Reachability)
tdomRLfpF graph f = {-  fmap (\m -> Set.fromList [ (n, steps) | (n, steps) <- Map.assocs m]) $ -}
        (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Map.fromList [ (x, Unreachable) | x <- nodes graph ]) |  y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

ftdomR :: DynGraph gr => TimeDomFunctionalGenR gr a b
ftdomR graph _ _ nextCond toNextCond = f 
  where f timeDomOf = {- traceShow ((7,timeDomOf ! 7 ! 6), (11,timeDomOf ! 11 ! 6), (13, timeDomOf ! 13 ! 6)) $ -}
                   Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                ⊔  Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                                   | y <- nodes graph
                                   ]
                ⊔  Map.fromList [ (y,    let plus = plusAt n in
                                         fmap (noSelf y) $ 
                                         fmap ( `plus` (steps)) $
                                         (flip without) (Set.fromList $ toNextCond y) $
                                         fmap (noSelf n) $
                                         (∐) [ fmap (flip (plusAt x) 1) $ timeDomOf ! x | x <- suc graph n ]
                                     )
                                                                                   | y <- nodes graph,
                                                                                     Just n <- [nextCond y],
                                                                                     let steps = (toInteger $ length $ toNextCond y) - 1
                                   ]
noSelf n r@(FixedStepsPlusOther _ m)
 | n == m = UndeterminedSteps
 | otherwise = r
noSelf n r = r

tdomROfLfp graph = tdomRLfpF graph ftdomR


tdepR g =
       Map.fromList [ (n, Set.fromList [ m | m <- nodes g, let rs = Set.fromList [ r | x <- suc g n, let r = timdom ! x ! m, r /= Unreachable ], Set.size rs > 1 ])  | n <- condNodes ]
       -- Map.fromList [ (n, Set.fromList [ m | m <- nodes g, let r = timdom ! n ! m,  r == UndeterminedSteps]) | n <- condNodes]
  where timdom = tdomROfLfp g
        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]

tdepRSlice :: (DynGraph gr) => gr a b -> Node -> Set Node
tdepRSlice g = \m -> let nticdSliceM = slicer (Set.fromList [m]) in  Set.fromList [m]  ∪  (㎲⊒) Set.empty (f m nticdSliceM)
  where f m nticdSliceM s = Set.fromList [ n | n <- condNodes, m ∈ tdep ! n ]
              ∪ Set.fromList [ n | n <- condNodes, not $ Set.null $ tdep  ! n  ∩  s  ]
--              ∪ Set.fromList [ n | n <- condNodes, not $ Set.null $ nticd ! n  ∩  s, not $ n ∈ nticdSliceM]
        tdep = tdepR g
        nticd = nticdF3 g
        slicer = nticdSlice g
        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]

type TimeMayDomFunctional = Map Node (Map Node Reachability) ->  Map Node (Map Node Reachability)
type TimeMayDomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> TimeMayDomFunctional

fTimeMayDom :: DynGraph gr => TimeMayDomFunctionalGen gr a b
fTimeMayDom graph _ _ nextCond toNextCond = f 
  where f timeDomOf = -- traceShow timeDomOf $
                      Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                               | y <- nodes graph
                                   ]
                    ⊔ Map.fromList [ (y, let all = (∐) [ Map.keysSet $ timeDomOf ! x | x <- suc graph n ] in
                                         let plus = joinPlus in
                                         fmap (\s -> s `plus` (steps + 1)) $
                                         Map.fromList [ (m, (∐) [  steps  | x <- suc graph n, Just steps <- [Map.lookup m (timeDomOf ! x)]   ]) | m <- Set.toList all, not $ m ∊ toNextCond y ]
                                     )
                                                                                   | y <- nodes graph,
                                                                                     Just n <- [nextCond y],
                                                                                     let steps = (toInteger $ length $ toNextCond y) - 1
                                   ]



type SnTimingEquationSystem =
       Map Node (Map Node Reachability)
type SnTimingEquationSystemGen gr a b =
       gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node])
    -> SnTimingEquationSystem


timeMayDomEquationSystemGen :: DynGraph gr => SnTimingEquationSystemGen gr a b
timeMayDomEquationSystemGen graph condNodes _ nextCond toNextCond =
                      -- Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                      -- ⊔
                         Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                                | p <- condNodes, y <- suc graph p
                         ]

timeMayDomEquationSystem graph = timeMayDomEquationSystemGen graph condNodes reachable nextCond toNextCond
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph



enumerateTimingDependence ::  DynGraph gr => gr a b -> Map Node (Set Node)
enumerateTimingDependence graph =
                     Map.fromList  [ (n, Set.empty) | n <- nodes graph ]
          ⊔   (∐)  [Map.fromList [ (n, Set.fromList [m] )]  | m <- nodes graph, n <- Set.toList $ enumerateTimingForUsing graph prevCondsWithSucc condsOf m ]
  where prevCondsWithSucc = (∐) [ Map.fromList [ (m, Set.fromList [(p,x,steps) ]) ] | p <- condNodes,
                                                                                       x <- suc graph p,
                                                                                       let toNextCondX = toNextCond x,
                                                                                       let m = head toNextCondX,
                                                                                       let steps = (toInteger $ length $ toNextCondX) - 1
                                ]
        condsOf = (∐) [ Map.fromList [ (x, Set.fromList [ p ]) ] | p <- condNodes, x <- suc graph p ]
                ⊔       Map.fromList [ (x, Set.empty         )   | x <- nodes graph ]
        condNodes = [ n | n <- nodes graph, isCond graph n ]
        toNextCond = toNextCondNode graph


enumerateTimingFor ::  DynGraph gr => gr a b -> Node -> Set Node
enumerateTimingFor graph = enumerateTimingForUsing graph prevCondsWithSucc condsOf
  where prevCondsWithSucc = (∐) [ Map.fromList [ (m, Set.fromList [(p,x,steps) ]) ] | p <- condNodes,
                                                                                       x <- suc graph p,
                                                                                       let toNextCondX = toNextCond x,
                                                                                       let m = head toNextCondX,
                                                                                       let steps = (toInteger $ length $ toNextCondX) - 1
                                ]
        condsOf = (∐) [ Map.fromList [ (x, Set.fromList [ p ]) ] | p <- condNodes, x <- suc graph p ]
                ⊔       Map.fromList [ (x, Set.empty         )   | x <- nodes graph ]
        condNodes = [ n | n <- nodes graph, isCond graph n ]
        toNextCond = toNextCondNode graph
enumerateTimingForUsing ::  DynGraph gr => gr a b -> (Map Node (Set (Node,Node,Integer))) -> Map Node (Set Node) -> Node -> Set Node
enumerateTimingForUsing graph prevCondsWithSucc condsOf m =
                             Set.fromList [ p | (p, sp) <- Map.assocs spx,
                                                sp == UndeterminedSteps
                             ]
          where nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                prevConds  = prevCondNodes graph
                -- spx = (∐) [ Map.fromList [ (p, sx) ] | (x,(_,_,sx)) <- Map.assocs $ (Map.union s0 s), p <- Set.toList $ condsOf ! x]
                spx = fmap (\sxs -> (∐) sxs) byCond
                  where byCond :: Map Node [Reachability]
                        byCond = foldr update Map.empty (Map.assocs $ Map.union s0 s)
                        update :: (Node, (Node, Integer, Reachability)) -> Map Node [Reachability] ->  Map Node [Reachability]
                        update (x,(_,_,sx)) m = foldr (Map.alter (cons sx)) m (condsOf ! x)
                          where cons sx  Nothing   = Just [sx]
                                cons sx (Just sxs) = Just (sx:sxs)
                s = solve Map.empty s0 Set.empty
                s0 :: Map Node (Node, Integer, Reachability)
                s0 = Map.fromList [ (x, (undefined, undefined, FixedSteps (toInteger steps))) | (p,x) <- prevCondsWithSuccNode graph m, let Just steps = List.findIndex (==m) (reverse $ toNextCond x)  ]
                solve s latest ps = -- traceShow latest $
                          if (s == s') then s else solve s' new (ps ∪ newPs)
                 where s' = Map.fromList [ (y, (n,steps,r)) | (y,(n,steps,_)) <- Map.assocs $ (Map.union new s),
                                                    let sxm =  (∐) [ sxm | x <- suc graph n, Just (_,_,sxm) <- [lookupEither x s0 s] ],
                                                    let r = case sxm of
                                                              FixedSteps j             -> FixedSteps (1+steps+j)
                                                              FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+steps+j) q'
                                                              UndeterminedSteps        -> FixedStepsPlusOther steps n
                            ]
                       new = Map.fromList $
                             [ (z, (p,steps,undefined))
                                 | p <- Set.toList $ newPs,
                                   Just prevConds <- [ Map.lookup p prevCondsWithSucc ],
                                   (_,z,steps) <- Set.toList $ prevConds,
                                   not $ Map.member z s0,
                                   not $ Map.member z s
                             ]
                       newPs = Set.fromList [ p | y <- Map.keys $ latest, p <- Set.toList $ condsOf ! y, not $ p ∈ ps ]
                lookupEither k m1 m2 = case Map.lookup k m1 of
                  Just v -> Just v
                  Nothing -> Map.lookup k m2

solveSnTimingEquationSystem ::  DynGraph gr => gr a b -> SnTimingEquationSystem -> SnTimingEquationSystem
solveSnTimingEquationSystem graph s = solve s0 0
          where nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                s0 = s
                solve s iterations = -- traceShow (s ! 3) $ traceShow (s ! 4) $ traceShow ("") $
                          if (s == s') then s else solve s' (iterations + 1)
                  where s' = Map.fromList [ (y, Map.union (s0 ! y) r) | (y, sy) <- Map.assocs s,
                                                                        let r = Map.fromList [ (m, case sxm of
                                                                                                     FixedSteps j             -> FixedSteps (1+steps+j)
                                                                                                     FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+steps+j) q'
                                                                                                     UndeterminedSteps        -> FixedStepsPlusOther steps n
                                                                                               )
                                                                                             | Just n <- [nextCond y],
                                                                                               let steps = (toInteger $ length $ toNextCond y) - 1,
                                                                                               let sx =  (∐) [ s ! x | x <- suc graph n ],
                                                                                               (m, sxm) <- Map.assocs sx
                                                                                ]
                            ]


solveSnTimingEquationSystemWorklist ::  forall gr a b. (DynGraph gr) => gr a b -> SnTimingEquationSystem -> SnTimingEquationSystem
solveSnTimingEquationSystemWorklist graph s0 = solve s0 worklist0 (Map.fromList [ (y, 0) | y <- Map.keys s0]) (Map.fromList [ (y, 0) | y <- Map.keys s0])
          where condNodes = [ x | x <- nodes graph, length (suc graph x) > 1 ]
                nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                prevConds   = prevCondNodes graph
                prevCondsWithSucc = prevCondsWithSuccNode graph
                (node2index, index2node) = ( Map.fromList [ (n, i) | (i,n) <- zip [0..] topsorted ],
                                             Map.fromList [ (i, n) | (i,n) <- zip [0..] topsorted ]
                                           )
                  where topsorted = topsort $ (fromSuccMap influencedNodes :: gr () ())
                        -- topsorted = reverse $ topsort graph
                worklist0 = Set.fromList [ node2index ! y | p <- condNodes, x <- suc graph p, (_,y) <- prevCondsWithSucc p]
                influencedNodes = Map.fromList [ (y, Set.fromList [ z | p <- pre graph y, (length $ suc graph p) > 1, (_,z) <- prevCondsWithSucc p ]) | y <- Map.keys s0 ]
                influenced = fmap (Set.map (node2index !)) influencedNodes
                solve :: Map Node (Map Node Reachability) -> Set Node -> Map Node Integer -> Map Node Integer -> Map Node (Map Node Reachability)
                solve s worklist iterations changes
                   | Set.null worklist  = -- traceShow ("SnTimingWorklist: ", iterations, changes, "Graph:\n", if ((length $ nodes graph) < 50 ∧ (Map.fold (+) 0 iterations) > 200) then graph else mkGraph [] [])
                                          s
                   | not changed        =      solve s   worklist'                (Map.update (\i -> Just $ i+1) y iterations)                                  changes
                   | otherwise          =      solve s' (worklist' ⊔ influencedY) (Map.update (\i -> Just $ i+1) y iterations) (Map.update (\i -> Just $ i+1) y changes)
                  where tr = traceShow (y,n, changed, Set.map (index2node !) worklist', Set.map (index2node !) influencedY)
                        (i, worklist') = Set.deleteFindMin worklist
                        y              = index2node ! i
                        toNextCondY = toNextCond y
                        n = head toNextCondY  -- assert (nextCond y == Just n)
                        steps = (toInteger $ length $ toNextCondY) - 1
                        sx =  (∐) [ s ! x | x <- suc graph n ]
                        sy  = (s  ! y)
                        sy' = Map.union (s0 ! y) $
                              Map.fromList [ (m, case sxm of
                                                     FixedSteps j             -> FixedSteps (1+steps+j)
                                                     FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+steps+j) q'
                                                     UndeterminedSteps        -> FixedStepsPlusOther steps n
                                              )
                                            | (m, sxm) <- Map.assocs sx
                              ]
                        changed     = sy /= sy'
                        influencedY = (influenced ! y)
                        s'          = Map.insert y sy' s


solveSnTimingEquationSystemWorklist2 ::  forall gr a b. DynGraph gr => gr a b -> SnTimingEquationSystem -> SnTimingEquationSystem
solveSnTimingEquationSystemWorklist2 graph s0 = -- traceShow (s0, worklist0, finished0, influenced) $
                                                solve s0 worklist0 finished0 0 0
          where condNodes = [ x | x <- nodes graph, length (suc graph x) > 1 ]
                nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                prevConds   = prevCondNodes graph
                influencedNodes = Map.fromList [ (y, Set.fromList [ (z, steps, p) | p <- pre graph y, (length $ suc graph p) > 1,
                                                                                         -- assert ((not $ Map.member p prevCondsWithSucc) → (prevCondsWithSuccNode graph p == [])) True,
                                                                                         -- assert (       Map.member p prevCondsWithSucc  → (   (Set.map (\(p,x,_) -> (p,x)) $ prevCondsWithSucc ! p)
                                                                                         --                                                    == (Set.fromList $  prevCondsWithSuccNode graph p)) ) True,
                                                                                         Just prevConds <- [Map.lookup p prevCondsWithSucc],
                                                                                         (_,z,steps) <- Set.toList $ prevConds
                                                             ]
                                            )
                                          | y <- Map.keys s0 ]
                influenced = fmap (Set.map (\(z,steps,p) -> (node2index ! z, steps, p))) influencedNodes

                prevCondsWithSucc = (∐) [ Map.fromList [ (m, Set.fromList [(p,x,steps) ]) ] | p <- condNodes,
                                                                                       x <- suc graph p,
                                                                                       let toNextCondX = toNextCond x,
                                                                                       let m = head toNextCondX,
                                                                                       let steps = (toInteger $ length $ toNextCondX) - 1
                                ]
                (node2index, index2node) = ( Map.fromList [ (n, i) | (i,n) <- zip [0..] topsorted ],
                                             Map.fromList [ (i, n) | (i,n) <- zip [0..] topsorted ]
                                           )
                  where topsorted = topsort $ (fromSuccMap (fmap (Set.map (\(z,_,_) -> z)) influencedNodes) :: gr () ())
                        --topsorted = reverse $ topsort graph
                worklist0 =  Map.fromList [ ((i,m), infl) | p <- condNodes, y <- suc graph p, infl@(i,steps,n) <- Set.toList $ influenced ! y, m <- toNextCond y, not $ (i,m) ∈ finished0]
                finished0 :: Set (Integer, Node)
                finished0 =  Set.fromList [  (i,m)             | p <- condNodes, y <- suc graph p, let i = node2index ! y,                     m <- toNextCond y]
                solve ::  SnTimingEquationSystem ->  Map (Integer, Node) (Integer, Integer, Node) -> Set (Integer, Node) -> Integer -> Integer ->  SnTimingEquationSystem
                solve s worklist finished iterations changes
                   | Map.null worklist  = s
                   | not changed        =      solve s   worklist'                                   finished (iterations+1)  changes
                   | otherwise          =      solve s' (worklist' `Map.union` influencedM)       newFinished (iterations+1) (changes + 1)
                  where tr = assert (n0 == n) $
                             assert (steps0 == steps) $
                             if (y == 180 ∧ m ∊ [-36, -22, 253]) then (
                             traceShow ((y,m),n, steps, changed, finishedY, sym', [ (x,sxm) | x <- suc graph n, Just sxm <- [Map.lookup m (s ! x)]], 
                                                                           Map.fromList [ ((index2node ! i, m), (steps, n)) | ((i,m), (_,steps,n)) <- Map.assocs worklist'],
                                                                           Map.fromList [ ((index2node ! i, m), (steps, n)) | ((i,m), (_,steps,n)) <- Map.assocs influencedM]
                                       )
                             ) else id 
                          where toNextCondY0 = toNextCond y
                                n0 = head toNextCondY0  -- assert (nextCond y == Just n)
                                steps0 = (toInteger $ length $ toNextCondY0) - 1
                        (((i,m),(_,steps,n)), worklist') = Map.deleteFindMin worklist
                        y = index2node ! i
                        msym  = Map.lookup m (s ! y)
                        sxm = (∐) [ sxm | x <- suc graph n, Just sxm <- [Map.lookup m (s ! x)]]
                        (finishedY, sym') = case sxm of
                                             FixedSteps j             -> (False, FixedSteps (1+steps+j))
                                             FixedStepsPlusOther j q' -> (False, FixedStepsPlusOther (1+steps+j) q')
                                             UndeterminedSteps        -> ((∀) (suc graph n) (\x -> case Map.lookup m (s ! x) of { Just (FixedSteps _) -> True ; _ -> False }),  FixedStepsPlusOther steps n)
                                             Unreachable              -> error (show $ (y,m,n))
                        newFinished
                          | finishedY = Set.insert (i, m) finished
                          | otherwise =                   finished
                        changed    = case msym of
                                       Just sym -> sym /= sym'
                                       Nothing  -> True
                        influencedM = Map.fromList [ ((iz,m), infl) | infl@(iz, steps, n) <- Set.toList $ influenced ! y,  not $ (iz,m) ∈ newFinished ]
                        s'          = Map.update (\sy -> Just $ Map.insert m sym' sy) y s

timingSnSolvedDependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSnSolvedDependence graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (p, Set.fromList [ m | let sx = (∐) [ s ! x  | x <- suc graph p ],
                                            (m, sxm) <- Map.assocs sx,
                                            sxm == UndeterminedSteps
                                      ]
                     ) | p <- condNodes
                  ]
  where s0 =  timeMayDomEquationSystem graph
        s  =  solveSnTimingEquationSystem graph s0
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


timingSnSolvedDependenceWorklist :: (DynGraph gr) => gr a b -> Map Node (Set Node)
timingSnSolvedDependenceWorklist graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (p, Set.fromList [ m | let sx = (∐) [ s ! x  | x <- suc graph p ],
                                            (m, sxm) <- Map.assocs sx,
                                            sxm == UndeterminedSteps
                                      ]
                     ) | p <- condNodes
                  ]
  where s0 =  timeMayDomEquationSystem graph
        s  =  solveSnTimingEquationSystemWorklist graph s0
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]

timingSnSolvedDependenceWorklist2 :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSnSolvedDependenceWorklist2 graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (p, Set.fromList [ m | let sx = (∐) [ s ! x  | x <- suc graph p ],
                                            (m, sxm) <- Map.assocs sx,
                                            sxm == UndeterminedSteps
                                      ]
                     ) | p <- condNodes
                  ]
  where s0 =  timeMayDomEquationSystem graph
        s  =  solveSnTimingEquationSystemWorklist2 graph s0
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]




tmaydomOfLfp :: DynGraph gr => gr a b -> TimeMayDomFunctionalGen gr a b -> Map Node (Set (Node, Integer ))
tmaydomOfLfp graph f = fmap (\m -> Set.fromList [ (n, steps) | (n, ss) <- Map.assocs m, FixedSteps steps <- [ss] ]) $
-- tmaydomOfLfp :: DynGraph gr => gr a b -> TimeMayDomFunctionalGen gr a b -> Map Node (Set (Node, Reachability))
-- tmaydomOfLfp graph f = fmap (\m ->   Set.fromList [ (n, r) | (n, rs) <- Map.assocs m, r <- [rs] ]) $
        (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Map.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

timmaydomOfLfp graph = tmaydomOfLfp graph fTimeMayDom




timdomOfTwoFingerFor :: forall gr a b. DynGraph gr => gr a b -> Map Node [Node] -> Map Node [Node] -> Map Node (Maybe (Node, Integer)) -> Map Node (Set (Node)) -> Map Node (Maybe (Node, Integer))
timdomOfTwoFingerFor graph condNodes worklist0 imdom0  imdom0Rev =
      require (condNodes  == Map.fromList [ (x, succs) | x <- nodes graph, let succs = suc graph x, length succs > 1 ])
    $ require (imdom0Rev  == (invert''' $ fmap noSteps $ imdom0))
    $ twoFinger 0 worklist0 imdom0 imdom0Rev
  where
        noSteps Nothing       = Nothing
        noSteps (Just (z, _)) = Just z
        toMap Nothing  = Map.empty
        toMap (Just (x, sx)) = Map.fromList [(x,sx)]

        prevCondsImmediate = prevCondImmediateNodes graph

        twoFinger :: Integer -> Map Node [Node] ->  Map Node (Maybe (Node, Integer)) -> Map Node (Set Node) -> Map Node (Maybe (Node, Integer))
        twoFinger i worklist imdom imdomRev
            | Map.null worklist = imdom
            | otherwise         =   if (not $ new) then twoFinger (i+1)                         worklist'                                   imdom                                            imdomRev
                                    else                twoFinger (i+1) (influenced `Map.union` worklist')  (Map.insert x zs                imdom)  (Map.insertWith (∪) z (Set.fromList [x]) imdomRev)
          where ((x, succs), worklist')  = Map.deleteFindMin worklist
                mz :: Maybe (Node, Integer, Set Node)
                mz = require (succs == suc graph x) 
                   $ foldM1 lca [ (y, 1, Set.empty) | y <- succs]
                Just (z,_) = zs
                zs = case mz of
                      Just (z,sz,_)  -> if z /= x then
                                          Just (z, sz)
                                        else
                                          Nothing
                      Nothing ->  Nothing
                new     = assert (isNothing $ imdom ! x) $
                          (not $ isNothing zs)
                influenced = assert (imdomRev  == (invert''' $ fmap (liftM fst) imdom)) $
                             let preds = reachableFrom imdomRev (Set.fromList [x])
                             in  restrict condNodes (Set.fromList $ [ n | n <- foldMap prevCondsImmediate preds, n /= x, isNothing $ imdom ! n])
                lca = lcaTimdomOfTwoFinger imdom

timdomOfTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set (Node, Integer))
timdomOfTwoFinger graph = fmap toSet $ timdomOfTwoFingerFor graph condNodes worklist0 imdom0 (invert''' $ fmap (liftM fst) $ imdom0)
  where imdom0   =             Map.fromList [ (x, Just (z,1)) | x <- nodes graph, [z] <- [suc graph x]]
                   `Map.union` Map.fromList [ (x, Nothing   ) | x <- nodes graph]
        condNodes   = Map.fromList [ (x, succs) | x <- nodes graph, let succs = suc graph x, length succs > 1 ]
        worklist0   = condNodes


timingDependenceViaTwoFinger g =
      invert'' $
      Map.fromList [ (m, Set.fromList [ n | (n, Nothing) <- Map.assocs itimdom ])         | m <- nodes g,
                                                                                            let toM  = reachable m gRev,
                                                                                            let toMS = Set.fromList toM,
                                                                                            let (condNodes', noLongerCondNodes) = Map.partition isCond $ fmap (List.filter (∈ toMS)) $ Map.delete m  $ restrict condNodes toMS,
                                                                                            let usingMS = reachableFrom (fmap toSet itimdom) (Set.fromList [m]),
                                                                                            let imdom0' = id
                                                                                                  $ Map.insert m Nothing
                                                                                                  $ Map.union (Map.mapWithKey (\x [z] ->  assert (z /= x) $ Just (z,1)) noLongerCondNodes)
                                                                                                  $ Map.union (Map.mapMaybeWithKey (\x _ -> case itimdom ! x of { Just (z, _) -> if z ∈ usingMS then Just Nothing else Nothing ; _ -> Nothing }) condNodes')
                                                                                                  $ restrict itimdom toMS,
                                                                                            let g' = (flip delSuccessorEdges m) $ subgraph toM $ g,
                                                                                            let worklist0' = Map.filterWithKey (\x _ -> imdom0' ! x == Nothing) condNodes',
                                                                                            let itimdom = timdomOfTwoFingerFor g'  condNodes' worklist0' imdom0' (invert''' $ fmap (liftM fst) $ imdom0')
                   ]
                                               
  where gRev = grev g
        condNodes = Map.fromList [ (x, succs) | x <- nodes g, let succs = suc g x, length succs > 1 ]
        imdom0 =             Map.fromList [ (x, Just (z,1)) | x <- nodes g, [z] <- [suc g x]]
                 `Map.union` Map.fromList [ (x, Nothing   ) | x <- nodes g]
        itimdom = timdomOfTwoFingerFor g condNodes condNodes imdom0 (invert''' $ fmap (liftM fst) $ imdom0)

        toSet Nothing = Set.empty
        toSet (Just (z, steps)) = Set.singleton z
        isCond []  = False
        isCond [_] = False
        isCond _   = True

alternativeTimingXdependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
alternativeTimingXdependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            let rmn = s ! (m,n),
                                            ((_,nl), rl) <- Map.assocs rmn,
                                            ((_,nr), rr) <- Map.assocs rmn,
                                            if (rl == Unreachable)       then error "unsolved snmTiming" else True,
                                            if (rr == Unreachable)       then error "unsolved snmTiming" else True,
                                            if (rl == UndeterminedSteps) then error "unsolved snmTiming" else True,
                                            if (rr == UndeterminedSteps) then error "unsolved snmTiming" else True,
                                            case (rl,rr) of
                                              (FixedSteps i, FixedSteps j)                         -> (i /= j)
                                              (FixedStepsPlusOther i l', FixedStepsPlusOther j r') -> (i /= j) ∨ (l' /= r')
                                              (FixedSteps i, _)                                    -> True 
                                              (_,            FixedSteps j)                         -> True 
                                              (_,            _)                                    -> False
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


alternativeTimingSolvedF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
alternativeTimingSolvedF3dependence = alternativeTimingXdependence snmTimingSolvedF3

pathsBetween :: Graph gr => gr a b -> gr a () -> Node -> Node -> [(Bool, [Node])]
pathsBetween graph trc n m = pathsBetweenUpTo graph trc n m m

pathsBetweenUpTo :: Graph gr => gr a b -> gr a () -> Node -> Node -> Node -> [(Bool, [Node])]
pathsBetweenUpTo graph trc n m q = pathsBetweenSeen (Set.fromList [n]) (Set.fromList []) n m
  where pathsBetweenSeen :: Set Node -> Set Node -> Node -> Node -> [(Bool, [Node])]
        pathsBetweenSeen seen loops n m
            | n == q         = return (False, [q])
            | n == m         = return (False, [m])
            | not $
              m ∊ suc trc n  = []
            | otherwise      = do
                                   x <- [ x |  x <- sucs, not $ x `elem` loops ]
                                   if (x ∈ seen) then do
                                       (_,   path) <- pathsBetweenSeen               seen  (Set.insert x loops) x m
                                       return (True, n:path)
                                   else do
                                       (loop,path) <- pathsBetweenSeen (Set.insert x seen)               loops  x m
                                       return (loop, n:path)
                where sucs = Set.toList $ Set.fromList $ suc graph n


pathsBetweenBFS :: Graph gr => gr a b -> gr a () -> Node -> Node -> [(Bool, [Node])]
pathsBetweenBFS graph trc n m =  pathsBetweenUpToBFS graph trc n m m


pathsBetweenUpToBFS :: Graph gr => gr a b -> gr a () -> Node -> Node -> Node -> [(Bool, [Node])]
pathsBetweenUpToBFS graph trc n m q =  Logic.observeAll $ pathsBetweenSeen (Set.fromList [n]) (Set.fromList []) n m
  where pathsBetweenSeen :: Set Node -> Set Node -> Node -> Node -> Logic.Logic (Bool, [Node])
        pathsBetweenSeen seen loops n m
            | n == q         = return (False, [q])
            | n == m         = return (False, [m])
            | not $
              m ∊ suc trc n  = Logic.mzero
            | otherwise      = foldr Logic.interleave Logic.mzero [
                                   if (x ∈ seen) then do
                                       (_,   path) <- pathsBetweenSeen               seen  (Set.insert x loops) x m
                                       return (True, n:path)
                                   else do
                                       (loop,path) <- pathsBetweenSeen (Set.insert x seen)               loops  x m
                                       return (loop, n:path)
                                | x <- sucs, not $ x ∈ loops
                              ]
                where sucs = Set.toList $ Set.fromList $ suc graph n




