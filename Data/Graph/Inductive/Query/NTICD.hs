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
import Data.Graph.Inductive.Query.Util.GraphTransformations (choiceAtRepresentativesGraphOf, splitRepresentativesGraphOf, splitRepresentativesGraphNoTrivialOf)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers.Numbered (isinkDFNumberedForSinks)
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
import Data.Graph.Inductive.Query.Dominators (dom)

import Debug.Trace
import Control.Exception.Base (assert)

tr msg x = seq x $ trace msg x

ntscdViaMDom g = Map.fromList [ (n, Set.fromList [m | nl <- suc g n,  m <- Set.toList $ mdom ! nl, (∃) (suc g n) (\nr -> not $ m ∈ mdom ! nr), m /= n]) | n <- nodes g]
  where mdom = mdomOfLfp g


nticdViaSinkDom g = Map.fromList [ (n, Set.fromList [m | nl <- suc g n,  m <- Set.toList $ sinkdom ! nl, (∃) (suc g n) (\nr -> not $ m ∈ sinkdom ! nr), m /= n]) | n <- nodes g]
  where sinkdom = sinkdomOfGfp g





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




