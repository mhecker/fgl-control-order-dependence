{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheStateDependenceImprecise where

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

import MicroArchitecturalDependence (
    CsGraph,
    AbstractMicroArchitecturalGraphNode,
    AbstractSemantic,
    TimeState,
    MergedMicroState(..),
    MicroArchitecturalAbstraction(..),
    stateGraphForSets, stateGraph, stateSets,
    muMergeDirectOf,
    muGraphFromMergeDirectFor
  )

import CacheExecution (
    AccessTime, registerAccessTime, cacheHitTime, cacheMissTime, cacheWriteTime, guardTime, initTime, noOpTime,
    CacheSize,
    toAlignedIndex, alignedIndicesFor, alignedIndices, nrOfDifferentCacheLinesPerArray,
    CachedObject(..), isCachable,
    Index
  )

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

import           CacheStateDependence        (AbstractCacheState, AbstractCacheStateTimeEquiv, MergedCacheState, AbstractCacheTimeState)
import qualified CacheStateDependence as CSD (
    removeFirstOrButLast, unknownranges,
    sameArrayAs,
    initialAbstractCacheState, cachedObjectsFor,
    cacheOnlyStepFor,
    cacheTimeReadLRUState,  cacheTimeArrayReadLRUState,
    cacheTimeWriteLRUState, cacheTimeArrayWriteLRUState
  )

cacheTimeArrayReadUnknownIndexLRU :: CacheSize -> Array -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeArrayReadUnknownIndexLRU cacheSize arr cache = case arr of
    Array       a -> assert (      isCachable $ ArrayName arr) $ lookup
  where lookup = CSD.unknownranges cacheSize arr cache carr cacheHitTime cacheMissTime
        carr  = CachedUnknownRange arr

cacheTimeArrayReadUnknownIndexLRUState :: CacheSize -> Array -> StateT AbstractCacheTimeState [] ()
cacheTimeArrayReadUnknownIndexLRUState cacheSize arr = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayReadUnknownIndexLRU cacheSize arr cache
    put (cache', time + accessTime)
    return ()


cacheTimeArrayWriteUnknownIndexLRU :: CacheSize -> Array -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeArrayWriteUnknownIndexLRU cacheSize arr cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ write
  where write = CSD.unknownranges cacheSize arr cache carr cacheWriteTime cacheWriteTime
        carr  = CachedUnknownRange arr


cacheTimeArrayWriteUnknownIndexLRUState :: CacheSize -> Array -> StateT AbstractCacheTimeState [] ()
cacheTimeArrayWriteUnknownIndexLRUState cacheSize arr = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayWriteUnknownIndexLRU cacheSize arr cache
    put (cache', time + accessTime)
    return ()



cacheTimeLRUEvalB :: CacheSize -> BoolFunction -> StateT AbstractCacheTimeState [] ()
cacheTimeLRUEvalB cacheSize CTrue     = return ()
cacheTimeLRUEvalB cacheSize CFalse    = return ()
cacheTimeLRUEvalB cacheSize (Leq x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalB cacheSize (Eeq x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalB cacheSize (And b1 b2) = do
  b1Val <- cacheTimeLRUEvalB cacheSize b1
  b2Val <- cacheTimeLRUEvalB cacheSize b2
  return ()
cacheTimeLRUEvalB cacheSize (Or b1 b2) = do
  b1Val <- cacheTimeLRUEvalB cacheSize b1
  b2Val <- cacheTimeLRUEvalB cacheSize b2
  return ()
cacheTimeLRUEvalB cacheSize (Not b) = do
  bVal <- cacheTimeLRUEvalB cacheSize b
  return ()

cacheTimeLRUEvalV :: CacheSize -> VarFunction -> StateT AbstractCacheTimeState [] ()
cacheTimeLRUEvalV cacheSize (Val  x) = return ()
cacheTimeLRUEvalV cacheSize (Var  x) = CSD.cacheTimeReadLRUState cacheSize x
{- special case for constants -}
cacheTimeLRUEvalV cacheSize (ArrayRead a ix@(Val i)) = do
  cacheTimeLRUEvalV cacheSize ix -- does nothing
  CSD.cacheTimeArrayReadLRUState cacheSize a (arrayIndex i)
  return ()
{- special case for assertions -}
cacheTimeLRUEvalV cacheSize (ArrayRead a ix@(AssertRange min max i)) = do
  cacheTimeLRUEvalV cacheSize i
  i <- lift $ alignedIndicesFor min max
  CSD.cacheTimeArrayReadLRUState cacheSize a (arrayIndex i)
  return ()
cacheTimeLRUEvalV cacheSize (ArrayRead a ix) = do
  cacheTimeLRUEvalV cacheSize ix
  cacheTimeArrayReadUnknownIndexLRUState cacheSize a
  return ()
cacheTimeLRUEvalV cacheSize (Plus  x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Minus x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Times x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Div x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Mod x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Xor x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Shl   x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Shr   x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (BAnd  x y) = do
  cacheTimeLRUEvalV cacheSize x
  cacheTimeLRUEvalV cacheSize y
  return ()
cacheTimeLRUEvalV cacheSize (Neg x) = do
  cacheTimeLRUEvalV cacheSize x
  return ()
cacheTimeLRUEvalV cacheSize (BNot x) = do
  cacheTimeLRUEvalV cacheSize x
  return ()
cacheTimeLRUEvalV cacheSize (AssertRange min max x) = do
  cacheTimeLRUEvalV cacheSize x
  return ()



cacheTimeStepForState :: CacheSize -> CFGEdge -> StateT AbstractCacheTimeState [] (CFGEdge, AbstractCacheTimeState)
cacheTimeStepForState cacheSize e@(Guard b bf) = do
        cacheTimeLRUEvalB cacheSize bf
        (cache, time) <- get
        return (e, (cache, time + guardTime))
cacheTimeStepForState cacheSize e@(Assign x vf) = do
        cacheTimeLRUEvalV cacheSize vf
        CSD.cacheTimeWriteLRUState cacheSize x
        σ' <- get
        return (e, σ')
{- special case for constants -}
cacheTimeStepForState cacheSize e@(AssignArray a ix@(Val i) vf) = do
        cacheTimeLRUEvalV cacheSize vf
        cacheTimeLRUEvalV cacheSize ix -- does nothing
        CSD.cacheTimeArrayWriteLRUState cacheSize a (arrayIndex i)
        σ' <- get
        return (e, σ')
{- special case for assertions -}
cacheTimeStepForState cacheSize e@(AssignArray a ix@((AssertRange min max i)) vf) = do
        cacheTimeLRUEvalV cacheSize vf
        cacheTimeLRUEvalV cacheSize i
        i <- lift $ alignedIndicesFor min max
        CSD.cacheTimeArrayWriteLRUState cacheSize a (arrayIndex i)
        σ' <- get
        return (e, σ')
cacheTimeStepForState cacheSize e@(AssignArray a ix vf) = do
        cacheTimeLRUEvalV cacheSize vf
        cacheTimeLRUEvalV cacheSize ix
        cacheTimeArrayWriteUnknownIndexLRUState cacheSize a
        σ' <- get
        return (e, σ')
cacheTimeStepForState cacheSize e@(Init _ _ ) = do
        (cache, time) <- get
        return (e, (cache, time + initTime))
cacheTimeStepForState cacheSize e@(InitArray _ _ ) = do
        (cache, time) <- get
        return (e, (cache, time + initTime))
cacheTimeStepForState cacheSize e@(NoOp) = do
        (cache, time) <- get
        return (e, (cache, time + noOpTime))
cacheTimeStepForState cacheSize (Read  _ _) = undefined
cacheTimeStepForState cacheSize (Print _ _) = undefined
cacheTimeStepForState cacheSize (Spawn    ) = undefined
cacheTimeStepForState cacheSize (Call     ) = undefined
cacheTimeStepForState cacheSize (Return   ) = undefined

cacheTimeStepFor ::  CacheSize -> AbstractSemantic AbstractCacheTimeState CFGEdge
cacheTimeStepFor cacheSize e σ = evalStateT (cacheTimeStepForState cacheSize e) σ

cacheOnlyStepFor ::  CacheSize -> AbstractSemantic AbstractCacheState CFGEdge
cacheOnlyStepFor cacheSize e σ = fmap first $ evalStateT (cacheTimeStepForState cacheSize e) (σ, 0)
  where first (e, σ) = (e, fst σ)


cacheStateGraph :: (Graph gr) => CacheSize -> gr CFGNode CFGEdge -> AbstractCacheState -> Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraph cacheSize = stateGraph (cacheOnlyStepFor cacheSize) (Just csLeq)


csLeq [] [] = True
csLeq [] _  = False
csLeq _  [] = False
csLeq (co : cs) (co' : cs') = leq co co'  ∧  csLeq cs cs'
  where leq (CachedVar x) (CachedVar x') = x == x' 
        leq (CachedVar x) _ = False

        leq (CachedArrayRange a i) (CachedArrayRange a' i') = a == a' ∧ i == i'
        leq (CachedArrayRange a i) (CachedUnknownRange a' ) = a == a'
        leq (CachedArrayRange a i) _                        = False

        leq (CachedUnknownRange a) (CachedUnknownRange a' ) = a == a'
        leq (CachedUnknownRange a) _                        = False



costsFor :: DynGraph gr =>  CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor cacheSize csGraph  =  (∐) [ Map.fromList [ ((n0, m0, e), Set.fromList [time]) ]  |
                                                 (n, (n0,cs)) <- labNodes csGraph,
                                                 (m, e) <- lsuc csGraph n,
                                                 let Just (m0,_) = lab csGraph m,
                                                 (_,fullState'@(_,time)) <- cacheTimeStepFor cacheSize e (cs, 0)
                      ]

costsFor2 :: CacheSize -> CsGraph AbstractCacheState CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor2 cacheSize (css, es)  =  (∐) [ Map.fromList [ ((n, n', e), Set.fromList [time]) ]  |
                                                 (n, σes) <- Map.assocs es,
                                                 (cache, e, (n', cache')) <- Set.toList σes,
                                                 (_,fullState'@(_,time)) <- cacheTimeStepFor cacheSize e (cache, 0)
                      ]


cacheCostDecisionGraphFor :: DynGraph gr => CacheSize -> gr CFGNode CFGEdge -> gr (Node, AbstractCacheState) CFGEdge -> (gr CFGNode CFGEdge, Map (Node, Node) Integer)
cacheCostDecisionGraphFor cacheSize g csGraph = (
      mkGraph
        ((labNodes g) ++ [(nNew, n) | (nNew, n) <-  [ (m', n) | ((e@(n,_,_),_), m') <- Map.assocs nodesFor  ]
                                                 ++ [ (mj, n) | ( e@(n,_,_)   , mj) <- Map.assocs joinFor   ]
                                                 ++ [ (mj, n) | ( e@(n,_,_)   , mj) <- Map.assocs linJoinFor]
                         ])
        (irrelevant ++ [ (n , m', l'  ) | ((e@(n,_,l),_), m') <- Map.assocs nodesFor, let l' = Use $ isDataDependent l ]
                    ++ [ (m', mj, NoOp) | ((e@(_,_,l),_), m') <- Map.assocs nodesFor,                          let mj = joinFor ! e ]
                    ++ [ (mj,  m, l   ) |   e@(_,m,l)         <- relevant,                                     let mj = joinFor ! e ]
                    ++ [ (n , m', l'  ) | ((e@(n,_,l),_), m') <- Map.assocs linNodesFor, let l' = Use $ isDataDependent l ]
                    ++ [ (m', m , l   ) |   e@(_,m,l)         <- linRelevant,                                  let m' = linJoinFor ! e ]
        ),
                  Map.fromList [ ((n ,m ), cost    ) | e@(n,m,l) <- irrelevant, let [cost] = Set.toList $ costs ! e,           assert (cost > 0) True ]
      `Map.union` Map.fromList [ ((n ,m'), cost - 2) | ((e@(n,_,l),cost), m') <- Map.assocs nodesFor,                          assert (cost > 2) True ]
      `Map.union` Map.fromList [ ((m',mj),        1) | ((e@(_,_,l),   _), m') <- Map.assocs nodesFor,                          let mj = joinFor ! e ]
      `Map.union` Map.fromList [ ((mj,m ),        1) |   e@(_,m,l)            <- relevant,                                     let mj = joinFor ! e ]
      `Map.union` Map.fromList [ ((n ,m'), cost - 1) | ((e@(n,_,l),cost), m') <- Map.assocs linNodesFor,                       assert (cost > 1) True ]
      `Map.union` Map.fromList [ ((m',m ),        1) |   e@(_,m,l)            <- linRelevant,                                  let m' = linJoinFor ! e ]
    )
  where
        costs = costsFor cacheSize csGraph

        isRelevant e = nrSuc e > 1
        nrSuc e = Set.size $ costs ! e

        isLinRelevant e@(n,m,l) =
            (nrSuc e == 1) ∧ (not $ List.null $ isDataDependent l) ∧ (length (suc g n) == 1 )

        isDataDependent = isDep
          where isDep l@(AssignArray a (Val _) vf ) = isDataDepV vf
                isDep l@(AssignArray a ix      vf ) = isDataDepV vf ++ [ name | name <- Set.toList $ useV ix ]
                isDep l                             = isDataDepE l

                arrayReadsV a@(ArrayRead _ _) = Set.singleton a
                arrayReadsV   (Val  x)    = Set.empty
                arrayReadsV   (Var  x)    = Set.empty
                arrayReadsV   (Plus  x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Minus x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Times x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Div   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Mod   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Shl   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Shr   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Xor   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (BAnd  x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Neg x)     = arrayReadsV x
                arrayReadsV   (BNot x)    = arrayReadsV x
                arrayReadsV   (AssertRange min max x) = arrayReadsV x

                arrayReadsB = useBFor arrayReadsV
                arrayReadsE = useEFor arrayReadsV arrayReadsB


                isDataDepV vf = [ name | r@(ArrayRead a ix) <- Set.toList $ arrayReadsV vf, case ix of { Val _ -> False ; _ -> True }, name <- Set.toList $ useV ix ]
{- unused
                isDataDepB bf = not $ List.null $ [ r | r@(ArrayRead a ix) <- Set.toList $ arrayReadsB bf, case ix of { Val _ -> False ; _ -> True } ]
-}
                isDataDepE l  = [ name | r@(ArrayRead a ix) <- Set.toList $ arrayReadsE  l, case ix of { Val _ -> False ; _ -> True }, name <- Set.toList $ useV ix ]

        nodesFor =               Map.fromList $ zip [ (e,time) | e <-   relevant, time <- Set.toList $ costs ! e ] nodesNew
        joinFor  =               Map.fromList $ zip                     relevant                                    joinNew

        linNodesFor =            Map.fromList $ zip [ (e,time) | e <-linRelevant, time <- Set.toList $ costs ! e ]  linNew
        linJoinFor  =            Map.fromList $ zip                  linRelevant                                    linNew

        relevant   = [ e | e <- labEdges g,       isRelevant e   , assert (not $ isLinRelevant e) True]
        linRelevant= [ e | e <- labEdges g,       isLinRelevant e, assert (not $ isRelevant    e) True]
        irrelevant = [ e | e <- labEdges g, not $ isRelevant e ∨ isLinRelevant e]
        totalnewSplit = sum $ fmap nrSuc relevant
        totalnewJoin  = length relevant
        totalnewLin   = length linRelevant
        (nodesNew, joinNew, linNew) = (left, mid, right)
          where all = newNodes (totalnewSplit + totalnewJoin + totalnewLin) g
                (tmp, right) = splitAt (totalnewSplit + totalnewJoin) all
                (left,  mid) = splitAt  totalnewSplit                 tmp

cacheCostDecisionGraph :: DynGraph gr => CacheSize -> gr CFGNode CFGEdge -> Node -> (gr CFGNode CFGEdge, Map (Node, Node) Integer)
cacheCostDecisionGraph cacheSize g n0 = cacheCostDecisionGraphFor cacheSize g csGraph
  where csGraph = cacheStateGraph cacheSize g CSD.initialAbstractCacheState n0



cacheStateGraph'ForVarsAtMForGraph2 :: forall gr. (DynGraph gr) => Set CachedObject -> CsGraph AbstractCacheState CFGEdge ->  Node -> gr (Node, MergedCacheState) CFGEdge
cacheStateGraph'ForVarsAtMForGraph2 vars (css, es) mm = result
  where result = subgraph (rdfs [ m | (m, (m',_)) <- labNodes merged, m' == mm ] merged) merged

        merged :: gr (Node, MergedCacheState) CFGEdge
        merged = mkGraph nodes' edges'

        nodes' = zip [0..] [           a                   | (m,σs)  <- Map.assocs css,            c                  <- Set.toList σs,  let cs = (m,c), a <- α cs             ]
        edges' =           [(toNode' ! a, toNode' ! a', e) | (m,σes) <- Map.assocs es,  m /= mm,  (c, e, cs'@(m',c')) <- Set.toList σes, let cs = (m,c), a <- α cs, a' <- α cs']
        toNode' = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes'

        α cs@(n, cache)
            | n == mm = relevantConcreteCombinations
            | otherwise = [ (n,  Unmerged cache)]
          where relevantConcreteCombinations = do
                        cache' <- forM (List.filter relevant cache) concrete
                        return (mm, Merged $ Set.fromList $ cache')

                relevant co@(CachedVar v) = co ∈ vars
                relevant co@(CachedArrayRange a i) = co ∈ vars
                relevant co@(CachedUnknownRange a) = (∃) vars (CSD.sameArrayAs a)

                concrete co@(CachedVar v)          = return co
                concrete co@(CachedArrayRange a i) = return co
                concrete co@(CachedUnknownRange a) = [CachedArrayRange a           aligned | aligned <- alignedIndices ]



cacheAbstraction :: CacheSize -> MicroArchitecturalAbstraction AbstractCacheState AbstractCacheStateTimeEquiv CFGEdge
cacheAbstraction cacheSize = MicroArchitecturalAbstraction {
      muIsDependent = muIsDependent,
      muMerge = False,
      muGraph'For = muGraph'For,
      muInitialState = CSD.initialAbstractCacheState,
      muStepFor = cacheOnlyStepFor cacheSize,
      muLeq = Just csLeq,
      muCostsFor = costsFor2 cacheSize
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph2 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = CSD.cachedObjectsFor e, not $ Set.null vars] ]
        muIsDependent graph roots idom y n (Merged _) = undefined
        muIsDependent graph roots idom y n (Unmerged cache) =
            -- (if n == 11 then traceShow (y, n) $ traceShow roots $ traceShow idom else id) $
            isChoice ∨ isImprecise
          where isChoice    = (length $ suc graph n) > 1
                            ∧ (idom ! y == Nothing)
                isImprecise = (∃) (lsuc graph n) (\(_,e) -> length (CSD.cacheOnlyStepFor cacheSize e cache) > 1)
                            ∧ (not $ maxFromTreeM idom y ∈ roots)
csdMergeDirectOf :: forall gr a a'. (DynGraph gr) => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf cacheSize = muMergeDirectOf (cacheAbstraction cacheSize)

csdGraphFromMergeDirectFor :: forall gr a a'. (DynGraph gr) =>
  CacheSize ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) CFGEdge
csdGraphFromMergeDirectFor cacheSize = muGraphFromMergeDirectFor (cacheAbstraction cacheSize)
