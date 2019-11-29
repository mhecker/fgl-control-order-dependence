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

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

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
import Util (moreSeeds, restrict, invert'', maxFromTreeM, maxFromTreeI, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
import IRLSOD (CFGNode, CFGEdge(..), GlobalState(..), globalEmpty, ThreadLocalState, Var(..), isGlobal, Array(..), arrayIndex, isArrayIndex, arrayMaxIndex, arrayEmpty, ArrayVal, Val, BoolFunction(..), VarFunction(..), Name(..), useE, defE, useEFor, useBFor, useB, useV, use, def, SimpleShow (..), stepFor)
import qualified IRLSOD as IRLSOD (Input)

import MicroArchitecturalDependence (
    CsGraph,
    AbstractMicroArchitecturalGraphNode,
    AbstractSemantic,
    TimeState,
    MergeMode(..),
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
cacheStateGraph cacheSize = stateGraph (cacheOnlyStepFor cacheSize) (Just $ AbstractLeq $ csLeq)


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


cacheStateGraph'ForVarsAtMForGraph2 :: forall gr. (DynGraph gr) => Set CachedObject -> CsGraph AbstractCacheState CFGEdge ->  Node -> gr (Node, MergedCacheState) CFGEdge
cacheStateGraph'ForVarsAtMForGraph2 vars (css, es) mm = result
  where result = subgraph (rdfs [ m | (m, (m',_)) <- labNodes merged, m' == mm ] merged) merged

        merged :: gr (Node, MergedCacheState) CFGEdge
        merged = mkGraph nodes' edges'

        nodes' = zip [0..] [           a                   | (m,σs)  <- IntMap.toList css,            c                  <- Set.toList σs,  let cs = (m,c), a <- α cs             ]
        edges' =           [(toNode' ! a, toNode' ! a', e) | (m,σes) <- IntMap.toList es,  m /= mm,  (c, e, cs'@(m',c')) <- Set.toList σes, let cs = (m,c), a <- α cs, a' <- α cs']
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
      muTimeStepFor = cacheTimeStepFor cacheSize,
      muLeq = Just $ AbstractLeq $ csLeq,
      muToCFGEdge = id
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph2 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = CSD.cachedObjectsFor e, not $ Set.null vars] ]
        muIsDependent graph roots idom y n (Merged _) = undefined
        muIsDependent graph roots idom y n (Unmerged cache) =
            -- (if n == 11 then traceShow (y, n) $ traceShow roots $ traceShow idom else id) $
            isChoice ∨ isImprecise
          where isChoice    = (length $ suc graph n) > 1
                            ∧ (IntMap.lookup y idom == Nothing)
                isImprecise = (∃) (lsuc graph n) (\(_,e) -> length (CSD.cacheOnlyStepFor cacheSize e cache) > 1)
                            ∧ (not $ maxFromTreeI idom y ∈ roots)


csdMergeDirectOf :: forall gr a a'. (DynGraph gr) => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf cacheSize gr n0 = first $ muMergeDirectOf (cacheAbstraction cacheSize) gr n0
  where first (x, _, _) = x

csdGraphFromMergeDirectFor :: forall gr a a'. (DynGraph gr) =>
  CacheSize ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) CFGEdge
csdGraphFromMergeDirectFor cacheSize = muGraphFromMergeDirectFor (cacheAbstraction cacheSize)
