{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
#define PDOMUSESDF
module Data.Graph.Inductive.Query.NTICD where

import Data.Ord (comparing)
import Data.Maybe(fromJust)
import Control.Monad (liftM, foldM, forM, forM_, liftM2)

import System.Random (mkStdGen, randoms)

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
import Data.Graph.Inductive.Query.NTICD.Util (cdepGraphP, cdepGraph, combinedBackwardSlice)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers.Numbered (isinkDFNumberedForSinks)
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)


import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)
import Data.Dequeue.SimpleDequeue (SimpleDequeue)

import Data.Foldable (maximumBy)
import qualified Data.Foldable as Foldable

import IRLSOD
import Program

import Util(minimalPathsUpToLength, the, invert', invert'', invert''', foldM1, reachableFrom, reachableFromM, isReachableFromM, reachableFromSeenM, treeDfs, toSet, fromSet, reachableFromTree, fromIdom, fromIdomM, roots, dfsTree, restrict, isReachableFromTreeM, without, findCyclesM, treeLevel, isReachableBeforeFromTreeM, minimalPath, reachableUpToLength, distancesUpToLength, minimalDistancesForReachable, inCycle, pathsUpToLength)
import Unicode



import Data.Graph.Inductive.Query.LCA
import Data.Graph.Inductive.Query.PostDominance (MaximalPath(..), sinkPathsFor, inSinkPathFor, maximalPathsFor, inPathFor, sinkdomOf, mdomOf, mdomOfLfp, sinkdomOfGfp, domOfGfp, onedomOf, domsOf, sinkdomsOf, mdomsOf, isinkdomOftwoFinger8Up, isinkdomOfTwoFinger8, isinkdomOfTwoFinger8ForSinks, isinkdomOfTwoFinger8DownSingleNodeSinks, imdomOfTwoFinger7)

import Data.Graph.Inductive.Query.PostDominanceFrontiers (idomToDFFastForRoots, mDFTwoFinger, isinkDFTwoFinger)
import Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges (idfViaCEdgesFastForCycles)
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

sinkShrinkedGraphNoNewExitForSinks :: DynGraph gr => gr a b  -> [[Node]] -> gr () ()
sinkShrinkedGraphNoNewExitForSinks graph sinks = mkGraph (  [ (s,())   | sink <- sinks, let s = head sink]
                                            ++ [ (n,())   | n    <- nodes graph, not $ n ∈ sinkNodes ]
                                          )
                                          (
                                               [ (n,s,())       | sink <- sinks, let s = head sink, s' <- sink, n <- pre graph s', not $ n ∊ sink]
                                            ++ [ (n,m,()) | (n,m) <- edges graph, not $ n ∈ sinkNodes, not $ m ∈ sinkNodes ]
                                          )
    where sinkNodes   = Set.fromList [ x | sink <- sinks, x <- sink]

sinkShrinkedGraph :: DynGraph gr => gr a b  -> Node -> gr () ()
sinkShrinkedGraph graph endNode = foldl (flip insEdge) graph' [ (s,endNode,()) | sink <- sinks, let s = head sink ]
    where sinks  = controlSinks graph
          graph' = insNode (endNode, ()) $ sinkShrinkedGraphNoNewExitForSinks graph sinks 



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






isinkdomOfSinkContraction :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfSinkContraction graph = fmap (Set.delete endNode) $ 
                                  Map.fromList [ (x, idomClassic ! x)  | x <- nodes graph, not $ x ∈ sinkNodes ]
                                ⊔ Map.fromList [ (x, Set.fromList [y]) | (s:sink) <- sinks, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
                                ⊔ Map.fromList [ (x, Set.empty)        | x <- nodes graph]
    where [endNode] = newNodes 1 graph
          sinks = controlSinks graph
          idomClassic = fmap (\x -> Set.fromList [x]) $ Map.fromList $ iDom (grev $ sinkShrinkedGraph graph endNode) endNode
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]














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






ntindDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntindDef g = Map.fromList [ (n, onPathBetween (suc g n) (Set.toList $ sinkdoms ! n) ∖ (Set.insert n $ sinkdoms ! n)) | n <- nodes g ]
  where sinkdoms = sinkdomsOf g
        onPathBetween ss ts = fwd
          where g' = foldr (flip delSuccessorEdges) g ts
                fwd = Set.fromList $  dfs ss g'

ntsndDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntsndDef g = Map.fromList [ (n, onPathBetween (suc g n) (Set.toList $ mdoms ! n) ∖ (Set.insert n $ mdoms ! n)) | n <- nodes g ]
  where mdoms = mdomsOf g
        onPathBetween ss ts = fwd
          where g' = foldr (flip delSuccessorEdges) g ts
                fwd = Set.fromList $  dfs ss g'





ntscdMyDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = myDod graph

ntscdMyDodFastPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodFastPDomSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = myDodFastPDom graph

ntscdMyDodSliceViaNtscd :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodSliceViaNtscd graph msS = combinedBackwardSlice graph ntscd' empty msS
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        ntscd' = mDFTwoFinger graph'
        empty = Map.empty


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








nticdMyWodSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = invert'' $ nticdF3 graph
        w     = myWod graph


nticdMyWodSliceViaEscapeNodes :: (DynGraph gr) => gr () () ->  Set Node -> Set Node
nticdMyWodSliceViaEscapeNodes g = \ms -> combinedBackwardSlice g' nticd' empty ms ∖ (Set.fromList (end:escape))
  where (end, escape, g') = withUniqueEndNodeAndEscapeNodes () () () () g
        nticd' = invert'' $ nticdF3 g'
        empty = Map.empty


choiceAtRepresentativesGraphOf :: forall gr a b . (DynGraph gr) => gr a b ->  gr a b
choiceAtRepresentativesGraphOf g = g''
  where g'' :: gr a b
        g'' = mkGraph ((nx, undefined) : (labNodes g))
                ([ e                          | e@(n,m,l) <- labEdges g] ++
                 [ (n,  nx, undefined)        | n <- representants]
                )
 
        representants  = [ head sink | sink <- controlSinks g]
        [nx] = newNodes 1 g


nticdMyWodSliceViaChoiceAtRepresentatives :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSliceViaChoiceAtRepresentatives g = \ms -> combinedBackwardSlice g'' (nticd'') empty ms
  where -- g'  = foldr (flip delSuccessorEdges) g (Map.keys representants)
        g'' = choiceAtRepresentativesGraphOf g
        -- nticd   = invert'' $ nticdF3 g
        -- nticd'  = invert'' $ nticdF3 g'
        nticd'' = invert'' $ nticdF3 g''
        empty = Map.empty



splitRepresentativesGraphOf :: forall gr a b . (DynGraph gr) => gr a b ->  gr a b
splitRepresentativesGraphOf g = g''
  where g'' :: gr a b
        g'' = mkGraph ([ (n', fromJust $ lab g n) | (n,n') <- Map.assocs splitPredOf ] ++ labNodes g)
                ([ e                          | e@(n,m,l) <- labEdges g, not $ m ∊ representants] ++
                 [ (n,  m',  l)               |   (n,m,l) <- labEdges g, Just m' <- [Map.lookup m splitPredOf], n /= m]
                )
 
        representants = [ head sink | sink <- controlSinks g]
        splitPred   = newNodes (length representants) g
        splitPredOf = Map.fromList $ zip representants splitPred

splitRepresentativesGraphNoTrivialOf :: forall gr a b . (DynGraph gr) => gr a b ->  gr a b
splitRepresentativesGraphNoTrivialOf g = g''
  where g'' :: gr a b
        g'' = mkGraph ([ (n', fromJust $ lab g n) | (n,n') <- Map.assocs splitPredOf ] ++ labNodes g)
                ([ e                          | e@(n,m,l) <- labEdges g, not $ m ∊ representants] ++
                 [ (n,  m',  l)               |   (n,m,l) <- labEdges g, Just m' <- [Map.lookup m splitPredOf], n /= m]
                )
 
        representants = [ head sink | sink <- controlSinks g, length sink > 1]
        splitPred   = newNodes (length representants) g
        splitPredOf = Map.fromList $ zip representants splitPred


nticdMyWodSliceViaCutAtRepresentatives :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSliceViaCutAtRepresentatives g = \ms -> combinedBackwardSlice g'' (nticd ⊔ nticd'') empty ms
  where -- g'  = foldr (flip delSuccessorEdges) g (Map.keys representants)
        g'' = splitRepresentativesGraphOf g
        nticd   = invert'' $ nticdF3 g
        -- nticd'  = invert'' $ nticdF3 g'
        nticd'' = invert'' $ nticdF3 g''
        empty = Map.empty

nticdMyWodSliceViaCutAtRepresentativesNoTrivial :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSliceViaCutAtRepresentativesNoTrivial g = \ms -> combinedBackwardSlice g'' (nticd ⊔ nticd'') empty ms
  where -- g'  = foldr (flip delSuccessorEdges) g (Map.keys representants)
        g'' = splitRepresentativesGraphNoTrivialOf g
        nticd   = invert'' $ nticdF3 g
        -- nticd'  = invert'' $ nticdF3 g'
        nticd'' = invert'' $ nticdF3 g''
        empty = Map.empty


ntscdMyDodSliceViaCutAtRepresentatives :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodSliceViaCutAtRepresentatives g = \ms -> combinedBackwardSlice g'' (ntscd ⊔ ntscd'') empty ms
  where g'' = splitRepresentativesGraphOf g
        ntscd   = invert'' $ ntscdF3 g
        ntscd'' = invert'' $ ntscdF3 g''
        empty = Map.empty



nticdMyWodSliceViaNticd :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSliceViaNticd graph msS = combinedBackwardSlice graph nticd' empty msS
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        nticd' = isinkDFTwoFinger graph'
        empty = Map.empty


nticdMyWodSliceViaISinkDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSliceViaISinkDom graph msS =  Set.fromList [ n | n <- rdfs ms graph', {- n <- pre graph' x, -} isinkdom' ! n == Nothing]
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        isinkdom' = isinkdomOfTwoFinger8ForSinks sinks' sinkNodes' nonSinkCondNodes' graph'
          where sinks'     =  controlSinks graph'
                sinkNodes' = (∐) [ Set.fromList sink | sink <- sinks']
                nonSinkCondNodes' = Map.fromList [ (n, succs) | n <- nodes graph', not $ n ∈ sinkNodes', let succs = suc graph' n, length succs > 1 ]


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


wccSliceViaNticd :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaNticd g msS = s
  where ms = Set.toList msS

        g'''   = foldr (flip delSuccessorEdges) g'' ms
          where  toMs   = rdfs ms g
                 g' = subgraph toMs g
                 
                 fromMs =  dfs ms g'
                 g'' = subgraph fromMs g'

        sinks            = fmap (\m -> [m]) ms

        -- sinkS            = fmap Set.fromList sinks
        -- sinkNodes        = msS
        -- nonSinkCondNodes = Map.fromList [ (n, succs) | n <- nodes g''', not $ n ∈ sinkNodes, let succs = suc g''' n, length succs > 1 ]
        -- idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes g'''

        idom = Map.fromList $ iPDomForSinks sinks g'''

        s = Map.keysSet $ Map.filter (== Nothing) idom 




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



symmetric m = (∐) [ Map.fromList [((m1,m2), ns), ((m2,m1),ns) ] |  ((m1,m2),ns) <- Map.assocs m ]


fMayNaive graph _ _ nextCond toNextCond = f 
  where f maydomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y, (∐) [ maydomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]
mayNaiveGfp graph = domOfGfp graph fMayNaive




cdFromMyWod graph =  (∐) [ Map.fromList [ (n, Set.fromList [m] ) ]  | ((m1,m2),ns) <- Map.assocs $ myWodFast graph, n <- Set.toList ns, m <- [m1,m2] ]



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
                                   if isReachableFromTreeM ipdomM'' n x   ∧  (not $ x ∈ preM) then
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
                  in assert (processed0 == Set.fromList [ x | x <- nodes graph, isReachableFromTreeM ipdomM'' m x ]) $
                     (relevantCondNodesM, ipdomM''')
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
        [ (n,m1,m2)  |                                        cycle <- isinkdomCycles, length cycle > 1,
                                                              let cycleS = Set.fromList cycle,
                                                              let entries = entriesFor cycle,
                                                              let nodesTowardsCycle = dfs (head cycle : entries) graph,
                                                              let condsTowardCycle = condsIn nodesTowardsCycle,
                                                              let condsInCycle = restrict condsTowardCycle cycleS,
                                                              let cycleGraph0 = subgraph nodesTowardsCycle graph,
                                                              let nodesFromCycle = rdfs cycle cycleGraph0,
                                                              let cycleGraph = subgraph nodesFromCycle cycleGraph0,
                                                              let paths = strategy graph cycle,
                                                      require ( (∐) [ Set.fromList path | path <- paths] == Set.fromList cycle ) True,
                                                              let (m20:others) = concat paths,
                                                              let pairs = zip (m20:others) others,
                                                              let pdom0 = fromIdomM m20 $ iDom (grev cycleGraph) m20,
                                                              let pdoms = zip (m20:others) (scanl (rotatePDomAround cycleGraph condsTowardCycle) pdom0 pairs),
                                                              (m2, pdom) <- pdoms,
#ifdef PDOMUSESDF
                                                              let graph' = delSuccessorEdges cycleGraph m2,
                                                              (m1, ns) <- Map.assocs $ idomToDFFastForRoots [[m2]] graph' pdom,
                                                              m1 ∈ cycleS,
                                                              n <- Set.toList ns,
                                                              m1 /= n,
#else
                                                              n <- [ n | (n,_) <- Map.assocs condsInCycle] ++ entries,
                                                              let pdom' = fromIdomM m2  $ iDom (grev cycleGraph) m2,
                                                       assert (pdom == pdom') True,
                                                              n /= m2,
                                                              let (z,relevant) = lcaRKnownM pdom n (suc graph n),
                                                       assert (Just z == foldM1 (lca pdom) (suc graph n)) True,
                                                       assert (Set.fromList relevant == Set.fromList [ m1 | x <- suc graph n, m1 <- Set.toList $ (reachableFrom (fmap toSet pdom)  (Set.fromList [x])), isReachableBeforeFromTreeM pdom m1 z x ] ) True,
                                                              m1 <- relevant, m1 /= z,
                                                              m1 /= n,
                                                              m1 ∈ cycleS,
#endif
                                                       assert (m1 /= n) True,
                                                       assert (m2 /= n) True,
                                                       assert (m2 /= m1) True,
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
                                                              let cycleGraph0 = subgraph nodesTowardsCycle graph,
                                                              let nodesFromCycle = rdfs cycle cycleGraph0,
                                                              let cycleGraph = subgraph nodesFromCycle cycleGraph0,
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




