{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module CacheStateDependenceReach where

import qualified Data.List as List

import Data.Bits (xor, (.&.), shiftL, shiftR, complement)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Algebra.Lattice(JoinSemiLattice(..), BoundedJoinSemiLattice(..))

import Debug.Trace (traceShow)
import Control.Exception.Base (assert)


import Control.Monad.State
import Control.Monad.List


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic (grev)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.DFS (dfs, rdfs, topsort)
import Data.Graph.Inductive.Query.TransClos (trc)

import Unicode
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
import IRLSOD (CFGNode, CFGEdge(..), GlobalState(..), globalEmpty, ThreadLocalState, Var(..), isGlobal, Array(..), arrayIndex, isArrayIndex, arrayMaxIndex, arrayEmpty, ArrayVal, Val, BoolFunction(..), VarFunction(..), Name(..), useE, defE, useEFor, useBFor, useB, useV, use, def, SimpleShow (..), stepFor)
import qualified IRLSOD as IRLSOD (Input)

import MicroArchitecturalDependence (AbstractMicroArchitecturalGraphNode, stateSets, stateGraphForSets, stateGraphFor, mergeFrom, merged)
import CacheExecution (isCachable, AbstractCacheState, initialAbstractCacheState, CachedObject(..), cachedObjectsFor, cacheOnlyStepFor, costsFor)

import Program (Program(..))
import Program.Generator (toCodeSimple)
import Program.For (compileAllToProgram, For(..), subCommands)

import Data.Graph.Inductive.Util (mergeTwoGraphs, isTransitive, fromSuccMap, delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominance (mdomOfLfp, sinkdomOfGfp, sinkdomsOf, isinkdomOfTwoFinger8)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (isinkDFTwoFinger)
import Data.Graph.Inductive.Query.Slices.PostDominance (wodTEILSliceViaISinkDom)

import           Data.Graph.Inductive.Query.InfiniteDelay (TraceWith (..), Trace)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (Input(..))


type AbstractCacheStateReach = ([(CachedObject, Int)], Set CachedObject)


nextReachable ::  Graph gr => gr (Node, s) CFGEdge  -> Map AbstractMicroArchitecturalGraphNode (Map Node (Set AbstractMicroArchitecturalGraphNode))
nextReachable csGraph = (㎲⊒) init f
  where f nextReach = Map.fromList [ (y, Map.fromList [ (n, Set.fromList [y]) ])                    | (y,(n,_)) <- labNodes csGraph ]
                    ⊔ Map.fromList [ (y, Map.delete n $ (∐) [ nextReach ! x | x <- suc csGraph y] ) | (y,(n,_)) <- labNodes csGraph ]
        init = Map.fromList [ (y, Map.empty) | y <- nodes csGraph ]



cacheStateGraphForVars :: (Graph gr) => Set CachedObject -> gr CFGNode CFGEdge -> AbstractCacheState -> Node -> gr (Node, AbstractCacheStateReach) CFGEdge
cacheStateGraphForVars vars = stateGraphFor α cacheOnlyStepFor
  where α = αFor vars

αFor vars cache = (
            [ (v,i) | (i,v) <- zip [0..] cache, v ∈ vars],
            Set.fromList [ v |  v <- List.dropWhileEnd (\v -> not $ v ∈ vars) cache, not $ v ∈ vars]
           )


αForReach :: Set CachedObject -> Set Name -> AbstractCacheState -> AbstractCacheStateReach
αForReach vars reach cache = (
            [ (v,i) | (i,v) <- zip [0..] cache, v ∈ vars],
            Set.fromList [ v |  v <- List.dropWhileEnd (\v -> not $ v ∈ vars) cache, not $ v ∈ vars, isReachable v]
           )
  where isReachable (CachedVar v)          = VarName   v ∈ reach
        isReachable (CachedArrayRange a _) = ArrayName a ∈ reach
        isReachable (CachedUnknownRange a) = ArrayName a ∈ reach

αForReach2 :: Set CachedObject -> Node -> Set Name -> Node -> AbstractCacheState -> AbstractCacheStateReach
αForReach2 vars mm reach n cache
  | n == mm = (
            [ (v,0) | v <- cache, v ∈ vars],
            Set.empty
           )
  | otherwise = αForReach vars reach cache


cacheStateGraphForVarsAndCacheStatesAndAccessReachable :: (Graph gr) => Set CachedObject -> (Set (Node, AbstractCacheState), Set ((Node, AbstractCacheState), CFGEdge, (Node, AbstractCacheState))) -> Map Node (Set Name) -> gr (Node, AbstractCacheStateReach) CFGEdge
cacheStateGraphForVarsAndCacheStatesAndAccessReachable vars (cs, es) reach =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α (reach !! n) s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α (reach !! n) sn), e, (m, α (reach !! m) sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α = αForReach vars
        
        (!!) m x = Map.findWithDefault Set.empty x m


cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 :: (Graph gr) => Set CachedObject -> (Set (Node, AbstractCacheState), Set ((Node, AbstractCacheState), CFGEdge, (Node, AbstractCacheState))) -> Map Node (Set Name) -> Node -> gr (Node, AbstractCacheStateReach) CFGEdge
cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs, es) reach mm =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α (reach !! n) n s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α (reach !! n) n sn), e, (m, α (reach !! m) m sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α = αForReach2 vars mm

        (!!) m x = Map.findWithDefault Set.empty x m



csd''''Of3 :: (DynGraph gr, Show (gr (Node, AbstractCacheStateReach) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd''''Of3 graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph y,
                                        -- (if (n == 17 ∧ m == 21) then traceShow (vars,y,y's,  g'', "KKKKKK", csGraph) else id) True,
                                        let relevant  = Map.findWithDefault Set.empty m (nextReach ! y),
                                        -- (if (n == 23 ∧ m == 22) then traceShow (vars,y,y's,  relevant) else id) True,
                                        let canonical           = Set.findMin relevant,
                                        let canonicalCacheState = cacheState csGraph canonical,
                                        not $ (∀) relevant (\y' -> cacheState csGraph y' == canonicalCacheState)
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable vars (cs,es) reach :: Gr (Node, AbstractCacheStateReach) CFGEdge,
      let nextReach = nextReachable csGraph,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph],
      let y's  = Set.fromList $ nodesToCsNodes ! m,
      let canonical = Set.findMin y's,
      let canonicalCacheState = cacheState csGraph canonical,
      not $ (∀) y's (\y' -> cacheState csGraph y' == canonicalCacheState),
      let ys = wodTEILSliceViaISinkDom csGraph y's
   ]
  where cacheState csGraph y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        (cs, es)  = stateSets cacheOnlyStepFor graph initialAbstractCacheState n0


csd''''Of4 :: (DynGraph gr, Show (gr (Node, AbstractCacheStateReach) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd''''Of4 graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph y,
                                        n /= m,
                                        -- (if (n == 7 ∧ m == 17) then traceShow (vars,y,y's, "KKKKKK", csGraph, g'') else id) True,
                                        let relevant  = Map.findWithDefault Set.empty m (nextReach ! y),
                                        -- (if (n == 23 ∧ m == 22) then traceShow (vars,y,y's,  relevant) else id) True,
                                        let canonical           = Set.findMin relevant,
                                        let canonicalCacheState = cacheState csGraph canonical,
                                        if (∀) relevant (\y' -> cacheState csGraph y' == canonicalCacheState) then traceShow (n,m,y,vars,relevant) True else True,
                               assert  (not $ (∀) relevant (\y' -> cacheState csGraph y' == canonicalCacheState)) True
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: Gr (Node, AbstractCacheStateReach) CFGEdge,
      let nextReach = nextReachable csGraph,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph],
      let y's  = Set.fromList $ nodesToCsNodes ! m,
      let canonical = Set.findMin y's,
      let canonicalCacheState = cacheState csGraph canonical,
      not $ (∀) y's (\y' -> cacheState csGraph y' == canonicalCacheState),
      let g'' = let { ms = Set.toList y's ;
            g = csGraph ;
            g''   = foldr (flip delSuccessorEdges) g' ms ;
            toMs   = rdfs ms g ;
            g' = subgraph toMs g } in g'',
      let ys = wodTEILSliceViaISinkDom csGraph y's
   ]
  where cacheState csGraph y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        (cs, es)  = stateSets cacheOnlyStepFor graph initialAbstractCacheState n0


accessReachableFrom :: Graph gr => gr CFGNode CFGEdge -> Map Node (Set Name)
accessReachableFrom graph = (㎲⊒) init f
  where f reach = Map.fromList [ (n, (∐) [ Set.filter isCachable $ useE e ∪ defE e | (_,e) <- lsuc graph n ]) | n <- nodes graph ]
                ⊔ Map.fromList [ (n, (∐) [ reach ! x | x <- suc graph n] ) | n <- nodes graph ]
        init    = Map.fromList [ (n, Set.empty) | n <- nodes graph ]


csGraphFromMergeFor graph n0 m = merged csGraph' equivs
    where (equivs, csGraph') = mergeFromFor graph n0 m

mergeFromFor graph n0 m = (mergeFrom graph' csGraph' idom roots, csGraph')
    where (cs, es)  = stateSets cacheOnlyStepFor graph initialAbstractCacheState n0

          vars  = head $ List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars]
          graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m
          reach = accessReachableFrom graph'
          csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: Gr (Node, AbstractCacheStateReach) CFGEdge
          nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph']
          y's  = nodesToCsNodes ! m
          
          csGraph' = let { toY's = subgraph (rdfs y's csGraph) csGraph } in foldr (flip delSuccessorEdges) toY's y's
          idom = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'
          roots = Set.fromList y's

csdMergeOf :: forall gr. (DynGraph gr) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeOf graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraphM'' y,
                                        -- (if (n == 7 ∧ m == 17) then traceShow (vars,y,y's, "KKKKKK", csGraph, g'') else id) True,
                                        n /= m
                     ]
                 )
    | m <- nodes graph,
      mayBeCSDependent m,
      vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraphM = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: gr (Node, AbstractCacheStateReach) CFGEdge,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraphM, n == n' ] ) | n <- nodes graph'],
      let y's  = nodesToCsNodes ! m,
      let csGraphM' = let { toY's = subgraph (rdfs y's csGraphM) csGraphM } in foldr (flip delSuccessorEdges) toY's y's,
      let idom' = Map.fromList $ iPDomForSinks [[y'] | y' <- y's] csGraphM',
      let roots' = Set.fromList y's,
      let equivs = mergeFrom graph' csGraphM' idom' roots',
      let csGraphM'' = merged csGraphM' equivs,
      let idom'' = fmap fromSet $ isinkdomOfTwoFinger8 csGraphM'',
      let ys = Set.fromList [ y | y <- nodes csGraphM'', idom'' ! y == Nothing]
   ]
  where (cs, es)  = stateSets cacheOnlyStepFor graph initialAbstractCacheState n0
        csGraph = stateGraphForSets (cs, es) :: gr (Node, AbstractCacheState) CFGEdge
        costs = costsFor csGraph
        mayBeCSDependent m = (∃) (lsuc graph m) (\(n,l) -> Set.size (costs ! (m,n,l)) > 1)
