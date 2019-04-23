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

ntscd g = Map.fromList [ (n, Set.fromList [m | nl <- suc g n,  m <- Set.toList $ mdom ! nl, (∃) (suc g n) (\nr -> not $ m ∈ mdom ! nr), m /= n]) | n <- nodes g]
  where mdom = mdomOfLfp g


nticd g = Map.fromList [ (n, Set.fromList [m | nl <- suc g n,  m <- Set.toList $ sinkdom ! nl, (∃) (suc g n) (\nr -> not $ m ∈ sinkdom ! nr), m /= n]) | n <- nodes g]
  where sinkdom = sinkdomOfGfp g


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
nticdMyWodSliceViaISinkDom graph msS =  Set.fromList [ n | n <- rdfs ms graph', isinkdom' ! n == Nothing]
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        isinkdom' = isinkdomOfTwoFinger8ForSinks sinks' sinkNodes' nonSinkCondNodes' graph'
          where sinks'     =  controlSinks graph'
                sinkNodes' = (∐) [ Set.fromList sink | sink <- sinks']
                nonSinkCondNodes' = Map.fromList [ (n, succs) | n <- nodes graph', not $ n ∈ sinkNodes', let succs = suc graph' n, length succs > 1 ]

wodTEILSliceViaISinkDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSliceViaISinkDom g msS =  Set.fromList [ n | n <- nodes g'', isinkdom'' ! n == Nothing]
  where ms = Set.toList msS
        g''   = foldr (flip delSuccessorEdges) g' ms
          where  toMs   = rdfs ms g
                 g' = subgraph toMs g

        isinkdom'' = fmap fromSet $ isinkdomOfTwoFinger8 g''

wccSliceViaISinkDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaISinkDom g msS =  Set.fromList [ n | n <- nodes g''', isinkdom''' ! n == Nothing]
  where ms = Set.toList msS
        g'''   = foldr (flip delSuccessorEdges) g'' ms
          where  toMs   = rdfs ms g
                 g' = subgraph toMs g
                 fromMs =  dfs ms g'
                 g'' = subgraph fromMs g'

        isinkdom''' = fmap fromSet $ isinkdomOfTwoFinger8 g'''












symmetric m = (∐) [ Map.fromList [((m1,m2), ns), ((m2,m1),ns) ] |  ((m1,m2),ns) <- Map.assocs m ]


fMayNaive graph _ _ nextCond toNextCond = f 
  where f maydomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y, (∐) [ maydomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]
mayNaiveGfp graph = domOfGfp graph fMayNaive



















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




