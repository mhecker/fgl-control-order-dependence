{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
#define SKIP_INDEPENDENT_NODES_M
module MicroArchitecturalDependence where

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


type ConcreteSemantic a = CFGEdge -> a -> Maybe a

type AbstractSemantic a = CFGEdge -> a -> [a]

type NormalState = (GlobalState,ThreadLocalState, ())

type TimeState = Integer

type TimeCost = Integer

type AbstractMicroArchitecturalGraphNode = Node

data MergedMicroState a a'  = Unmerged a | Merged a' deriving (Eq, Ord, Show)

data MicroArchitecturalAbstraction a a' = MicroArchitecturalAbstraction {
    muMerge :: Bool,
    muGraph'For :: forall gr. DynGraph gr => gr CFGNode CFGEdge -> (Set (Node, a), Set ((Node, a), CFGEdge, (Node, a))) -> Node -> [gr (Node, MergedMicroState a a' ) CFGEdge],
    muInitialState :: a,
    muStepFor :: AbstractSemantic a,
    muCostsFor :: (Set (Node, a), Set ((Node, a), CFGEdge, (Node, a))) -> Map (Node, Node, CFGEdge) (Set TimeCost)
  }


stateSetsSlow :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> (Set (Node, s), Set ((Node, s), CFGEdge, (Node, s)))
stateSetsSlow step g  σ0 n0 = (㎲⊒) (Set.fromList [(n0,σ0)], Set.fromList []) f
  where f (cs, es) = (cs ∪ Set.fromList [  (n', σ') | (n, σ, e, n', σ') <- next ],
                      es ∪ Set.fromList [ ((n,  σ ), e, (n', σ')) | (n, σ, e, n', σ') <- next ]
                     )
          where next = [ (n, σ, e, n', σ')  | (n,σ) <- Set.toList cs, (n',e) <- lsuc g n, σ' <- step e σ]

stateSets :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> (Set (Node, s), Set ((Node, s), CFGEdge, (Node, s)))
stateSets step g σ0 n0 = {- assert (result == stateSetsSlow step g σ0 n0) $ -} result
  where result = go (Set.fromList [(n0,σ0)]) (Set.fromList [(n0,σ0)]) (Set.fromList [])
        go workset cs es
         | Set.null workset = (cs, es)
         | otherwise         = go (workset' ∪ csNew) (cs ∪ csNew) (es ∪ esNew)
             where ((n,σ), workset') = Set.deleteFindMin workset
                   next = [ (n, σ, e, n', σ')  | (n',e) <- lsuc g n, σ' <- step e σ]
                   
                   csNew = Set.fromList [ (n', σ') | (n, σ, e, n', σ') <- next, not $ (n', σ') ∈ cs ]
                   esNew = Set.fromList [ ((n,  σ ), e, (n', σ')) | (n, σ, e, n', σ') <- next ]


stateGraphForSets :: (Ord s, Graph gr) => (Set (Node, s), Set ((Node, s), CFGEdge, (Node, s))) -> gr (Node, s) CFGEdge
stateGraphForSets (cs, es) = mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es]
  where nodes = zip [0..] (Set.toList cs)
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

stateGraph :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> gr (Node, s) CFGEdge
stateGraph step g σ0 n0 = stateGraphForSets (cs, es)
  where (cs, es) = stateSets step g σ0 n0


stateGraphFor :: (Graph gr, Ord s, Ord s') => (s -> s') ->  AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> gr (Node, s') CFGEdge
stateGraphFor α step g σ0 n0 = mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where (cs, es) = stateSets step g σ0 n0
        cs' =  Set.map f cs
          where f (n, s) = (n, α s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α sn), e, (m, α sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes





merged :: (Graph gr) => gr (Node, s) CFGEdge ->  Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode)) -> gr (Node, Set AbstractMicroArchitecturalGraphNode) CFGEdge
merged csGraph' equivs =  mkGraph nodes' edges
  where edges =  Set.toList $ Set.fromList $ fmap f $ (labEdges csGraph')
          where f (y,y',e) = (toNode ! (n,equiv), toNode ! (n', equiv'), e)
                  where Just (n,_)  = lab csGraph' y
                        Just (n',_) = lab csGraph' y'
                        equiv  = representative $ equivs ! n  ! y
                        equiv' = representative $ equivs ! n' ! y'
        nodes = zip [0..] (Set.toList $ Set.fromList $ [ (n, representative equiv) | (n, equivN) <- Map.assocs equivs, equiv <- Map.elems equivN ])
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        representative = Set.findMin -- use the first node in a equivalence class as representative

        nodes' = fmap fromRep nodes
          where fromRep (i,(n,y)) = (i, (n, equivs ! n ! y))






mergeFromSlow ::  (DynGraph gr) => gr CFGNode CFGEdge -> gr (Node, s) CFGEdge -> Map AbstractMicroArchitecturalGraphNode (Maybe AbstractMicroArchitecturalGraphNode) -> Set AbstractMicroArchitecturalGraphNode -> Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
mergeFromSlow graph csGraph idom roots  =  (𝝂) init f 
  where 
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        f :: Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
          -> Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
        f equivs = -- traceShow (Map.filter (\equivs -> (∃) equivs (not . Set.null)) $ equivs, rootOf) $
          (
              Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y' | y' <- ys, Map.lookup y' rootOf == Just r ]) ] | y <- ys, Just r <- [Map.lookup y rootOf ]])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
            ⊔ Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y ] ) ] |  y <- ys])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
            ⊔ Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y' |
                                                                   y' <- ys,
                                                                   (∀) es (\(_,e) ->
                                                                     (∀) (lsuc csGraph y ) (\(x,  ey ) -> if ey  /= e then True else
                                                                     (∀) (lsuc csGraph y') (\(x', ey') -> if ey' /= e then True else
                                                                       let Just (m, _) = lab csGraph x
                                                                           Just (m',_) = lab csGraph x'
                                                                       in assert (m == m') $ 
                                                                       (∃) (equivs ! m) (\equiv -> x ∈ equiv ∧ x' ∈ equiv)
                                                                     ))
                                                                   )
                                                ]
                                  )] | y <- ys, not $ y ∈ roots, let es = lsuc csGraph y ])
                           | (n,ys) <- Map.assocs nodesToCsNodes,
                             assert ((∀) ys (\y -> (∀) ys (\y' -> (Set.fromList $ fmap snd $ lsuc csGraph y) == (Set.fromList $ fmap snd $ lsuc csGraph y')))) True
              ]
           )
        init = Map.fromList [ (n, Map.fromList [ (y, ysS) | y <- ys] ) | (n,ys) <- Map.assocs $ nodesToCsNodes, let ysS = Set.fromList ys]
        rootOf = Map.fromList [ (y, r) | y <- nodes csGraph, let r = maxFromTreeM idom y, r ∈ roots ]





mergeFrom ::  (DynGraph gr) =>
  gr CFGNode CFGEdge ->
  gr (Node, s) CFGEdge ->
  Map AbstractMicroArchitecturalGraphNode (Maybe AbstractMicroArchitecturalGraphNode) ->
  Set AbstractMicroArchitecturalGraphNode ->
  Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
mergeFrom graph csGraph idom roots = mergeFromForEdgeToSuccessor graph csGraph  idom roots



mergeFromForEdgeToSuccessor ::  (DynGraph gr) =>
  gr CFGNode CFGEdge ->
  gr (Node, s) CFGEdge ->
  Map AbstractMicroArchitecturalGraphNode (Maybe AbstractMicroArchitecturalGraphNode) ->
  Set AbstractMicroArchitecturalGraphNode ->
  Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
mergeFromForEdgeToSuccessor graph csGraph idom roots = assert (result == mergeFromSlow graph csGraph idom roots) result
  where result = (go orderToNodes init) ⊔ equivsNBase
          where (⊔) :: Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode)) -> Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode)) -> Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
                (⊔) left right =  Map.unionWithKey f left right
                f n fromSuccessorsN  fromBaseN = Map.unionWithKey g fromSuccessorsN fromBaseN
                g y fromSuccessorsYs fromBaseYs = {- assert (fromBaseYs ⊆ fromSuccessorsYs) $ -} fromSuccessorsYs
        go workset fromSuccessors
           | Map.null workset  = fromSuccessors
           | otherwise         =
               if changed then
                 go (workset' `Map.union` influenced) (Map.insert n (fromSuccessorsN' ⊔ fromRootsN) fromSuccessors)
               else
                 go  workset'                                                                       fromSuccessors
          where ((_,n), workset') = Map.deleteFindMin workset
                ys = nodesToCsNodes ! n
                fromRootsN = fromRoots ! n
                fromSuccessorsN' = goSuccessors (ys ∖ roots) Map.empty
                  where goSuccessors ysLeft fromsucc
                           | Set.null ysLeft = fromsucc
                           | otherwise = assert (y ∈ y's) goSuccessors ysLeft' ((Map.fromSet (const y's) y's) `Map.union` fromsucc)
                          where y = Set.findMin ysLeft
                                es = (∐) [ Map.fromList [ (e, Set.fromList [(x,m)]) ]  | (x,e) <- lsuc csGraph y, let Just (m, _) = lab csGraph x ]

                                y's     = Set.insert y y's0
                                ysLeft' = Set.delete y ysLeft'0
                                (y's0, ysLeft'0) = Set.partition (\y' -> 
                                                                   (∀) (lsuc csGraph y') (\(x', e') -> (∀) (es ! e') (\(x,m) -> 
                                                                          (x  ∈ Map.findWithDefault Set.empty x' (fromSuccessors ! m)  ∨  x ∈ equivsNBase ! m ! x')
                                                                   ))
                                                               )
                                                               ysLeft

                changed = assert (fromSuccessorsN ⊒ fromSuccessorsN') $
                          assert (diffSize == (fromSuccessorsN' /= fromSuccessorsN)) $ diffSize
                  where fromSuccessorsN = fromSuccessors ! n
                        diffSize = Map.size fromSuccessorsN /= Map.size fromSuccessorsN'
                                 ∨ (∃) (zip (Map.toAscList fromSuccessorsN) (Map.toAscList fromSuccessorsN')) (\((y,ys), (y', y's)) -> assert (y == y') $ Set.size ys /= Set.size y's)
                influenced = Map.fromList [ (nodesToOrder ! m, m) | m <- pre graph n]

        init = Map.mapWithKey (\n ys -> Map.fromSet (const ys) ys) nodesToCsNodes
        rootOf = Map.fromList [ (y, r) | y <- nodes csGraph, let r = maxFromTreeM idom y, r ∈ roots ]

        nodesToCsNodes = Map.fromList [ (n, Set.fromList [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

        fromRoots = Map.mapWithKey (\n ys -> go ys Map.empty) nodesToCsNodes
          where go ysLeft fromroots
                  | Set.null ysLeft = fromroots
                  | otherwise = let mr = Map.lookup y rootOf in case mr of
                        Nothing -> go ysLeft0                                          fromroots
                        Just r  -> let (y's, ysLeft') = Set.partition (\y' -> Map.lookup y' rootOf == mr) ysLeft in
                                   go ysLeft' (Map.fromSet (const y's) y's `Map.union` fromroots)
                      where (y, ysLeft0) = Set.deleteFindMin ysLeft

        equivsNBase = Map.mapWithKey (\n ys -> fromRoots ! n ⊔ (Map.fromSet Set.singleton $ ys ∖ roots)) nodesToCsNodes

        order = List.reverse $ topsort graph
        nodesToOrder = Map.fromList $ zip order [0..]
        orderToNodes = Map.fromList $ zip [0..] order



muMergeDirectOf :: forall gr a a'. (DynGraph gr, Ord a) => MicroArchitecturalAbstraction a a' -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
muMergeDirectOf mu@( MicroArchitecturalAbstraction { muMerge, muGraph'For, muInitialState, muStepFor, muCostsFor }) graph n0 = traceShow (Set.size cs) $ invert'' $
  Map.fromList [ (m, ns) | m <- nodes graph,
#ifdef SKIP_INDEPENDENT_NODES_M
      mayBeCSDependent m,
#endif
      csGraph' <- (muGraph'For graph csGraph m ::  [gr (Node, MergedMicroState a a' ) CFGEdge]),
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let y's  = [ y | (y, (n', csy)) <- labNodes csGraph', m == n' ],
      let idom' = Map.fromList $ iPDomForSinks [[y'] | y' <- y's] csGraph',
      let ns = if muMerge then
            let roots' = Set.fromList y's
                equivs = mergeFromForEdgeToSuccessor graph' csGraph'  idom' roots'
                csGraph'' = merged csGraph' equivs
                idom'' = isinkdomOfTwoFinger8 csGraph''
            in Set.fromList [ n | (y, (n,_)) <- labNodes csGraph'', n /= m, Set.null $ idom'' ! y]
          else Set.fromList [ n | (y, (n,_)) <- labNodes csGraph' , n /= m, Nothing == idom'  ! y]
   ]
  where csGraph@(cs, es)  = stateSets muStepFor graph muInitialState n0
#ifdef SKIP_INDEPENDENT_NODES_M
        costs = muCostsFor csGraph
        mayBeCSDependent m = (∃) (lsuc graph m) (\(n,l) -> Set.size (costs ! (m,n,l)) > 1)
#endif         


muGraphFromMergeDirectFor :: forall gr a a'. (DynGraph gr, Ord a) =>
  MicroArchitecturalAbstraction a a' ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) CFGEdge
muGraphFromMergeDirectFor mu graph n0 m = merged muGraph' equivs
    where (equivs, muGraph') = mergeDirectFromFor mu graph n0 m

mergeDirectFromFor :: forall gr a a'. (DynGraph gr, Ord a) =>
  MicroArchitecturalAbstraction a a' ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  (Map Node (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode)),
   gr (Node, MergedMicroState a a') CFGEdge
  )
mergeDirectFromFor mu@( MicroArchitecturalAbstraction { muGraph'For, muInitialState, muStepFor, muCostsFor }) graph n0 m = (mergeFromForEdgeToSuccessor graph' csGraph'  idom roots, csGraph')
  where   csGraph@(cs, es) = stateSets muStepFor graph muInitialState n0
          
          csGraph' = head $ muGraph'For graph csGraph m 
          graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m
          nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph', n == n' ] ) | n <- nodes graph']
          y's  = nodesToCsNodes ! m
          
          idom = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'
          roots = Set.fromList y's

