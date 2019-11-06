{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheStateDependenceAgeSetsJoin where

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

import Data.Graph.Inductive.Query.PostDominanceFrontiers (idomToDFFast)
import qualified Data.Graph.Inductive.Query.PostDominance (isinkdomOfTwoFinger8)

import MicroArchitecturalDependence (
    CsGraph, csGraphSize,
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

import qualified CacheStateDependence as CSD (sameArrayAs, cachedObjectsFor, writtenCachedObjectsFor)

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

type Age = Set (Maybe Int)

type AbstractCacheState  = Map CachedObject Age
type AbstractCacheStateTimeEquiv = Set CachedObject
type MergedCacheState = MergedMicroState AbstractCacheState AbstractCacheStateTimeEquiv

type AbstractCacheTimeState = (AbstractCacheState, TimeState)



initialAbstractCacheState :: AbstractCacheState
initialAbstractCacheState = Map.empty

freshTime = Just 0
fresh = Set.singleton freshTime

infTime = Nothing
inf = Set.singleton infTime

freshOrInf = Set.fromList [ infTime, freshTime ]

lt Nothing  x = True
lt (Just a) x = a < x

geq  Nothing x = True
geq (Just a) x = a >= x

defaultTime hit miss cobj cache = case Map.lookup cobj cache of
  Nothing   -> return miss
  Just ages -> if Nothing ∈ ages then [miss, hit] else [hit]

{-
defaultCache' :: CacheSize -> CachedObject -> AbstractCacheState -> AbstractCacheState
defaultCache' cacheSize cobj cache = Map.insert cobj fresh $ cache'
  where cache' = Map.mapMaybe inc cache
        inc ages = if Set.null ages' ∨ ages' == inf then Nothing else Just ages'
          where ages' = Set.filter (`lt` cacheSize) $ Set.mapMonotonic (liftM (+1)) ages
-}

clean :: AbstractCacheState -> AbstractCacheState
clean  cache = Map.mapMaybe c cache
  where c ages = if Set.null ages ∨ ages == inf then Nothing else Just ages

defaultCache' :: CacheSize -> CachedObject -> AbstractCacheState -> AbstractCacheState
defaultCache' cacheSize cobj cache = clean $ Map.insert cobj fresh $ cache'
  where cache' = incAll cacheSize cobj cache

incAll :: CacheSize -> CachedObject -> AbstractCacheState -> AbstractCacheState
incAll cacheSize cobj cache = cache'
  where cobjAges = case Map.lookup cobj cache of
          Nothing   -> inf
          Just ages -> ages
        cache' = fmap inc cache

        inc ages = ages'
          where ages' = filter $ plus1 ages
                filter :: Age -> Age
                filter = Set.map f
                  where f Nothing  = Nothing
                        f ja@(Just a) = if a >= cacheSize then Nothing else ja
                plus1 ages = if infTime ∈ ages then Set.insert infTime plussed else plussed
                  where plussed = (∐) [ as a | Just a <- Set.toList ages ]
                        as a 
                          | (∀) cobjAges (       `geq` a ) = Set.fromList [ Just $ a + 1]
                          | (∀) cobjAges (not . (`geq` a)) = Set.fromList [ Just $ a ]
                          | otherwise               = Set.fromList [ Just $ a, Just $ a + 1]


{-
unknownCache' :: CacheSize -> Array -> [Index] -> AbstractCacheState -> AbstractCacheState
unknownCache' cacheSize arr indices cache = foldr ins cache' [CachedArrayRange arr i | i <- indices]
  where cache' = Map.mapMaybe inc cache
        inc ages = if Set.null ages' ∨ ages' == inf then Nothing else Just ages'
          where ages' = Set.filter (`lt` cacheSize) $ Set.mapMonotonic (liftM (+1)) ages
        ins cobj = Map.alter f cobj
          where f Nothing     = Just freshOrInf
                f (Just ages) = Just $ Set.insert freshTime ages
-}

unknownCache' :: CacheSize -> Array -> [Index] -> AbstractCacheState -> AbstractCacheState
unknownCache' cacheSize arr indices cache = clean $ foldr ins cache' [CachedArrayRange arr i | i <- indices]
  where cache' = (∐) [ incAll cacheSize (CachedArrayRange arr i) cache | i <- indices ]
        ins cobj = Map.alter f cobj
          where f Nothing     = Just freshOrInf
                f (Just ages) = Just $ Set.insert freshTime ages


unknownTimes hit miss arr indices cache
    |    incacheB = return $ hit
    | notincacheB = return $ miss
    | otherwise   = [ hit, miss ]
  where incacheB        = (∀) [CachedArrayRange arr i | i <- indices]    incache
        incache cobj    = case Map.lookup cobj cache of
          Nothing   -> False
          Just ages -> assert (not $ Set.null ages) $ not $ infTime ∈ ages

        notincacheB     = (∀) [CachedArrayRange arr i | i <- indices] notincache
        notincache cobj = case Map.lookup cobj cache of
          Nothing   -> True
          Just ages -> assert (not $ Set.null ages) $ assert (not $ ages == inf) $ False


cacheTimeReadLRU :: CacheSize -> Var -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeReadLRU cacheSize var cache = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ liftM (cache',) time
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ return $ (cache, registerAccessTime)
    Register    _ -> assert (not $ isCachable $ VarName var) $ return $ (cache, registerAccessTime)
  where cvar = CachedVar var
        cache' = defaultCache' cacheSize cvar cache
        time =   defaultTime cacheHitTime cacheMissTime cvar cache






cacheTimeArrayReadLRU :: CacheSize -> Array -> Index -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeArrayReadLRU cacheSize arr ix cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ liftM (cache', ) time
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        cache' = defaultCache' cacheSize carr cache
        time =   defaultTime cacheHitTime cacheMissTime carr cache

cacheTimeReadLRUState :: CacheSize -> Var -> StateT AbstractCacheTimeState [] ()
cacheTimeReadLRUState cacheSize var = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeReadLRU cacheSize var cache
    put (cache', time + accessTime)
    return ()


cacheTimeWriteLRU :: CacheSize -> Var -> AbstractCacheState -> (AbstractCacheState, AccessTime)
cacheTimeWriteLRU cacheSize var cache = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ (cache', cacheWriteTime)
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime )
    Register    _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime )
  where cvar = CachedVar var
        cache' = defaultCache' cacheSize cvar cache



cacheTimeWriteLRUState :: Monad m => CacheSize -> Var -> StateT AbstractCacheTimeState m ()
cacheTimeWriteLRUState cacheSize var = do
    (cache, time) <- get
    let (cache', accessTime) = cacheTimeWriteLRU cacheSize var cache
    put (cache', time + accessTime)
    return ()

cacheTimeArrayReadLRUState :: CacheSize -> Array -> Index -> StateT AbstractCacheTimeState [] ()
cacheTimeArrayReadLRUState cacheSize arr ix = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayReadLRU cacheSize arr ix cache
    put (cache', time + accessTime)
    return ()

cacheTimeArrayWriteLRU :: CacheSize -> Array -> Index -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeArrayWriteLRU cacheSize arr ix cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ return $ (cache', cacheWriteTime)
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        cache' = defaultCache' cacheSize carr cache


cacheTimeArrayWriteLRUState :: CacheSize -> Array -> Index -> StateT AbstractCacheTimeState [] ()
cacheTimeArrayWriteLRUState cacheSize arr ix = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayWriteLRU cacheSize arr ix cache
    put (cache', time + accessTime)
    return ()



cacheTimeArrayReadUnknownIndexLRU :: CacheSize -> Array -> [Index] -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeArrayReadUnknownIndexLRU cacheSize arr indices cache = case arr of
    Array       a -> assert (      isCachable $ ArrayName arr) $ liftM (cache',) times
  where 
        cache' = unknownCache'             cacheSize     arr indices cache
        times  = unknownTimes cacheHitTime cacheMissTime arr indices cache

cacheTimeArrayReadUnknownIndexLRUState :: CacheSize -> Array -> [Index] -> StateT AbstractCacheTimeState [] ()
cacheTimeArrayReadUnknownIndexLRUState cacheSize arr indices = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayReadUnknownIndexLRU cacheSize arr indices cache
    put (cache', time + accessTime)
    return ()

cacheTimeArrayWriteUnknownIndexLRU :: CacheSize -> Array -> [Index] -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeArrayWriteUnknownIndexLRU cacheSize arr indices cache = case arr of
    Array       a -> assert (      isCachable $ ArrayName arr) $ [(cache', cacheWriteTime)]
  where 
        cache' = unknownCache'             cacheSize     arr indices cache

cacheTimeArrayWriteUnknownIndexLRUState :: CacheSize -> Array -> [Index] -> StateT AbstractCacheTimeState [] ()
cacheTimeArrayWriteUnknownIndexLRUState cacheSize arr indices = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayWriteUnknownIndexLRU cacheSize arr indices cache
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
cacheTimeLRUEvalV cacheSize (Var  x) = cacheTimeReadLRUState cacheSize x
{- special case for constants -}
cacheTimeLRUEvalV cacheSize (ArrayRead a ix@(Val i)) = do
  cacheTimeLRUEvalV cacheSize ix -- does nothing
  cacheTimeArrayReadLRUState cacheSize a (arrayIndex i)
  return ()
{- special case for assertions -}
cacheTimeLRUEvalV cacheSize (ArrayRead a ix@(AssertRange min max i)) = do
  cacheTimeLRUEvalV cacheSize i
  case alignedIndicesFor min max of
    [i]     -> cacheTimeArrayReadLRUState             cacheSize a i
    indices -> cacheTimeArrayReadUnknownIndexLRUState cacheSize a indices
  return ()
cacheTimeLRUEvalV cacheSize (ArrayRead a ix) = do
  cacheTimeLRUEvalV cacheSize ix
  cacheTimeArrayReadUnknownIndexLRUState cacheSize a alignedIndices
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
        cacheTimeWriteLRUState cacheSize x
        σ' <- get
        return (e, σ')
{- special case for constants -}
cacheTimeStepForState cacheSize e@(AssignArray a ix@(Val i) vf) = do
        cacheTimeLRUEvalV cacheSize vf
        cacheTimeLRUEvalV cacheSize ix -- does nothing
        cacheTimeArrayWriteLRUState cacheSize a (arrayIndex i)
        σ' <- get
        return (e, σ')
{- special case for assertions -}
cacheTimeStepForState cacheSize e@(AssignArray a ix@((AssertRange min max i)) vf) = do
        cacheTimeLRUEvalV cacheSize vf
        cacheTimeLRUEvalV cacheSize i
        case alignedIndicesFor min max of
          [i]     -> cacheTimeArrayWriteLRUState             cacheSize a i
          indices -> cacheTimeArrayWriteUnknownIndexLRUState cacheSize a indices
        σ' <- get
        return (e, σ')
cacheTimeStepForState cacheSize e@(AssignArray a ix vf) = do
        cacheTimeLRUEvalV cacheSize vf
        cacheTimeLRUEvalV cacheSize ix
        cacheTimeArrayWriteUnknownIndexLRUState cacheSize a  alignedIndices
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


csLeq = Nothing

cacheStateGraph :: (Graph gr) => CacheSize -> gr CFGNode CFGEdge -> AbstractCacheState -> Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraph cacheSize = stateGraph (cacheOnlyStepFor cacheSize) csLeq


costsFor :: DynGraph gr =>  CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor cacheSize csGraph  =  (∐) [ Map.fromList [ ((n0, m0, e), Set.fromList [time]) ]  |
                                                 (n, (n0,cs)) <- labNodes csGraph,
                                                 (m, e) <- lsuc csGraph n,
                                                 let Just (m0,_) = lab csGraph m,
                                                 (_, fullState'@(_,time)) <- cacheTimeStepFor cacheSize e (cs, 0)
                      ]

costsFor2 :: CacheSize -> CsGraph AbstractCacheState CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor2 cacheSize (css, es)  =  (∐) [ Map.fromList [ ((n, n', e), Set.fromList [time]) ]  |
                                                 (n, σes) <- Map.assocs es,
                                                 (cache, e, (n', cache')) <- Set.toList σes,
                                                 (_, fullState'@(_,time)) <- cacheTimeStepFor cacheSize e (cache, 0)
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



cacheCostDecisionGraph :: DynGraph gr => CacheSize -> gr CFGNode CFGEdge -> Node -> (gr CFGNode CFGEdge, Map (Node, Node) Integer)
cacheCostDecisionGraph cacheSize g n0 = cacheCostDecisionGraphFor cacheSize g csGraph
  where csGraph = cacheStateGraph cacheSize g initialAbstractCacheState n0




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
                        cache' <- forM (Set.toList vars) incache
                        return (mm, Merged $ Set.fromList [ co | Just co <- cache' ])

                incache co = case Map.lookup co cache of
                  Nothing   -> [ Nothing ]
                  Just ages -> if Set.size ages == 1 then [ Just co ]  else [ Nothing, Just co ]



cacheAbstraction :: CacheSize -> MicroArchitecturalAbstraction AbstractCacheState AbstractCacheStateTimeEquiv CFGEdge
cacheAbstraction cacheSize = MicroArchitecturalAbstraction {
      muIsDependent = muIsDependent,
      muMerge = False,
      muGraph'For = muGraph'For,
      muInitialState = initialAbstractCacheState,
      muStepFor = cacheOnlyStepFor cacheSize,
      muLeq = csLeq,
      muCostsFor = costsFor2 cacheSize
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph2 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = CSD.cachedObjectsFor e, not $ Set.null vars] ]
        muIsDependent graph roots idom y n (Merged _) = undefined
        muIsDependent graph roots idom y n (Unmerged cache) = (isChoice ∨ isImprecise) ∧ (not isRootDominated)
          where isRootDominated = maxFromTreeM idom y ∈ roots
                isChoice    = (length $ suc graph n) > 1
                isImprecise = (∃) (lsuc graph n) (\(_,e) -> not $ List.null $ isDataDependent e)


csdMergeDirectOf :: forall gr a a'. (DynGraph gr) => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf cacheSize = muMergeDirectOf (cacheAbstraction cacheSize)

csdGraphFromMergeDirectFor :: forall gr a a'. (DynGraph gr) =>
  CacheSize ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) CFGEdge
csdGraphFromMergeDirectFor cacheSize = muGraphFromMergeDirectFor (cacheAbstraction cacheSize)





cacheDataDep :: CacheSize -> CsGraph AbstractCacheState CFGEdge -> Map (Node, AbstractCacheState, CachedObject) (Set (Node, AbstractCacheState))
cacheDataDep cacheSize (cs, es)  =  (∐) [ Map.fromList [ ((m, cache, co), Set.fromList [ (n, cache') ]) ] | ((m, cache), deps) <- Map.assocs seesDef, ((n, cache'), co) <- Set.toList deps ]
  where seesDef :: Map (Node, AbstractCacheState) (Set ((Node, AbstractCacheState), CachedObject))
        seesDef = (㎲⊒) (Map.fromList [ ((m,cache), Set.empty) | (m, caches) <- Map.assocs cs, cache <- Set.toList caches ]) f
          where f sees =  (∐) [ Map.fromList [ ((m, cache'), (killedFor cache' $ transDefs cacheSize n e cache cache' (sees ! (n, cache)) (defs (n, cache, cache'))) ) ]
                                      | (n, caches) <- Map.assocs cs, cache <- Set.toList caches, (cache_, e, (m, cache' )) <- Set.toList $ es ! n, cache == cache_ ]

        defs = defsFor cacheSize id

{-
killFor nodeFor  (n, cache, cache')   = Set.fromList [ (nodeFor (n, cache), co)  | (co, ages) <- Map.assocs cache,
                                                                assert (not $ Set.null ages) True,
                                                                assert (not $ ages == inf) True,
                                                                let agesM' = Map.lookup co cache',
                                                                case agesM' of
                                                                  Nothing -> True 
                                                                  Just ages' -> ages == fresh
-}
killedFor cache' sees'  = Set.fromList [ (node, co)  | (node, co) <- Set.toList sees',
                                                                let agesM' = Map.lookup co cache',
                                                                case agesM' of
                                                                  Nothing -> False
                                                                  Just ages' -> not $ ages' == fresh
                                            ]

{-
defsFor nodeFor (n, cache, cache')   = Set.fromList [ (nodeFor (n, cache), co) | (co, ages) <- Map.assocs cache,
                                                                assert (not $ Set.null ages) True,
                                                                assert (not $ ages == inf) True,
                                                                let agesM' = Map.lookup co cache',
                                                                case agesM' of
                                                                  Nothing -> False 
                                                                  Just ages' -> Set.size ages' > Set.size ages
                                            ]
                          ∪ Set.fromList [ (nodeFor (n, cache), co) | (co, ages') <- Map.assocs cache',
                                                                assert (not $ Set.null ages') True,
                                                                assert (not $ ages' == inf) True,
                                                                let agesM = Map.lookup co cache,
                                                                case agesM of
                                                                  Nothing -> ages' /= fresh
                                                                  Just ages -> Set.size ages' > Set.size ages
                                            ]
-}

defsFor cacheSize nodeFor (n, cache, cache')   = Set.fromList [ (nodeFor (n, cache), co) | (co, ages) <- Map.assocs cache,
                                                                assert (not $ Set.null ages) True,
                                                                assert (not $ ages == inf) True,
                                                                let ages' = Map.findWithDefault inf co cache',
                                                                not $ ages' `elem` [ pushedBack cacheSize ages, readToFront ages]
                                            ]
                          ∪ Set.fromList [ (nodeFor (n, cache), co) | (co, ages') <- Map.assocs cache',
                                                                assert (not $ Set.null ages') True,
                                                                assert (not $ ages' == inf) True,
                                                                let ages = Map.findWithDefault inf co cache,
                                                                -- if n == 16 then traceShow (n, ages, ages') $ traceShow (pushedBack cacheSize ages) $ traceShow (readToFront ages) True else True,
                                                                not $ ages' `elem` [ pushedBack cacheSize ages, readToFront ages]
                                            ]



pushedBack cacheSize = Set.map pb
  where pb Nothing = Nothing
        pb (Just a)
          | a + 1 == cacheSize = Nothing
          | otherwise          = Just $ a + 1

readToFront _ = fresh


transDefs cacheSize n e cache cache' seesN defsN =
            -- (if n `elem` [14,16,17] then traceShow "=======" $ traceShow (n, e, relevant) $ traceShow choices $ traceShow (seesN, defsN) $ traceShow (fromSeen, fromDefs) else id) $
            seesN ∪ fromSeen ∪ fromDefs 
          where fromSeen  =  -- Set.fromList [ (n', co)  | (n, co) <- Set.toList defsN, (n', co') <- Set.toList $ seesN, co' ∈ relevant, not $ isConst cache co' ]
                             Set.fromList [ (n', co)  | co <- Map.keys cache ++ Map.keys cache', let ages = Map.findWithDefault inf co cache, let ages' = Map.findWithDefault inf co cache', not $ ages' `elem` [ pushedBack cacheSize ages, readToFront ages], (n', co') <- Set.toList $ seesN, co' ∈ relevant, not $ isConst cache co']
                fromDefs  =  if not $ List.null choices then defsN else Set.empty

                choices = makesChoice e cache
                relevant = CSD.cachedObjectsFor e ∪ CSD.writtenCachedObjectsFor e

makesChoice e cache = [ co | choices <- Set.toList $ useE e, not $ List.length choices == 1, co <- choices ]
  where

    useE :: CFGEdge -> Set [CachedObject]
    useE (AssignArray a ix@(Val i)                 vf) = useV vf ∪ Set.singleton [CachedArrayRange a (toAlignedIndex $ arrayIndex i) ]
    useE (AssignArray a ix@(AssertRange min max i) vf) = useV vf ∪ Set.singleton [CachedArrayRange a  aligned                       | aligned <- alignedIndicesFor min max ]
    useE (AssignArray a ix                         vf) = useV vf ∪ Set.singleton [CachedArrayRange a  aligned                       | aligned <- alignedIndices ]
    useE e = useEFor useV useB e

    useB :: BoolFunction -> Set [CachedObject]
    useB = useBFor useV

    useV :: VarFunction -> Set [CachedObject]

    {- special case for constants -}
    useV (ArrayRead a ix@(Val i)) = Set.singleton [CachedArrayRange a (toAlignedIndex $ arrayIndex i) ]
    {- special case for assertions -}
    useV (ArrayRead a ix@(AssertRange min max i)) =
                                    Set.singleton [CachedArrayRange a           aligned | aligned <- alignedIndicesFor min max ]
    useV (ArrayRead a ix        ) = Set.singleton [CachedArrayRange a           aligned | aligned <- alignedIndices ]
                                  ∪ useV ix
    useV (Val  x)    = Set.empty
    useV (Var  x)    = Set.empty
    useV (Plus  x y) = useV x ∪ useV y
    useV (Minus x y) = useV x ∪ useV y
    useV (Times x y) = useV x ∪ useV y
    useV (Div   x y) = useV x ∪ useV y
    useV (Mod   x y) = useV x ∪ useV y
    useV (BAnd  x y) = useV x ∪ useV y
    useV (Shl   x y) = useV x ∪ useV y
    useV (Shr   x y) = useV x ∪ useV y
    useV (Xor   x y) = useV x ∪ useV y
    useV (Neg x)     = useV x
    useV (BNot x)    = useV x
    useV (AssertRange _ _ x) = useV x


isConst cache co = case Map.lookup co cache of { Nothing -> True ; Just ages -> (Set.size ages == 1) ∧ (not $ infTime ∈ ages) }

cacheDataDepG :: Graph gr => CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, CachedObject) (Set Node)
cacheDataDepG cacheSize csGraphG  = (∐) [ Map.fromList [ ((yM, co), Set.fromList [ yN ]) ] | (yM, deps) <- Map.assocs seesDef, (yN, co) <- Set.toList deps ]
  where seesDef :: Map Node (Set (Node, CachedObject))
        seesDef = (㎲⊒) (Map.fromList [ (y, Set.empty) | y <- nodes csGraphG ]) f
          where f sees =  (∐) [ Map.fromList [ (yM, (killedFor cache' $ transDefs cacheSize yN e cache cache' (sees ! yN) (defs yN (n, cache, cache'))) ) ]
                                      | (yN, (n, cache)) <- labNodes csGraphG, (yM, e) <- lsuc csGraphG yN, let Just (m, cache') = lab csGraphG yM]

{-
        kill yN = killFor (const yN)
-}
        defs yN = defsFor cacheSize (const yN)


cacheDataDepGWork :: Graph gr => CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, CachedObject) (Set Node)
cacheDataDepGWork cacheSize csGraphG  = (∐) [ Map.fromList [ ((yM, co), Set.fromList [ yN ]) ] | (yM, deps) <- Map.assocs seesDef, (yN, co) <- Set.toList deps ]
  where seesDef = go (Set.fromList $ nodes csGraphG) (Map.fromList [ (y, Set.empty) | y <- nodes csGraphG ])

        go workset sees
            | Set.null workset = sees
            | otherwise = if changed then go (foldr Set.insert workset0 (suc csGraphG yM)) (Map.insert yM seesM' sees)
                                     else go                   workset0                                          sees
          where (yM, workset0) = Set.deleteFindMin workset
                seesM  = sees ! yM
                Just (m, cache') = lab csGraphG yM

                seesM' = (∐) [(killedFor cache' $ transDefs cacheSize yN e cache cache' (sees ! yN) (defs yN (n, cache, cache')))  | (yN,e) <- lpre csGraphG yM,  let Just (n, cache)  = lab csGraphG yN ]
                changed = seesM /= seesM'

{-
        kill yN = killFor (const yN)
-}
        defs yN = defsFor cacheSize (const yN)



                           

cacheStateGraph'ForVarsAtMForGraph3 :: forall gr. (DynGraph gr) => Set CachedObject -> CsGraph AbstractCacheState CFGEdge ->  Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraph'ForVarsAtMForGraph3 vars (css, es) mm = result
  where result = subgraph (rdfs [ m | (m, (m',_)) <- labNodes merged, m' == mm ] merged) merged

        merged :: gr (Node, AbstractCacheState) CFGEdge
        merged = mkGraph nodes' edges'

        nodes' = zip [0..] [           a                   | (m,σs)  <- Map.assocs css,            c                  <- Set.toList σs,  let cs = (m,c), a <- α cs             ]
        edges' =           [(toNode' ! a, toNode' ! a', e) | (m,σes) <- Map.assocs es,  m /= mm,  (c, e, cs'@(m',c')) <- Set.toList σes, let cs = (m,c), a <- α cs, a' <- α cs']
        toNode' = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes'

        α :: (Node, AbstractCacheState) -> [ (Node, AbstractCacheState) ]
        α cs@(n, cache)
            | n == mm ∧ (∀) vars (isConst cache) = [ (n, fmap (Set.map (liftM (const 0))) $ restrict cache vars) ]
            | n == mm                            = [ (n,                                             cache     ) ]
            | otherwise = [ cs ]


csdFromDataDep :: DynGraph gr => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdFromDataDep cacheSize graph n0 = traceShow (csGraphSize csGraph) $
    invert'' $ Map.fromList [ (m, slice) | m <- nodes graph, mayBeCSDependent m, let slice = Set.delete m $ cacheDataDepSlice cacheSize csGraph csGraphG m]
  where  mu = cacheAbstraction cacheSize
         csGraph@(cs, es) = stateSets (muStepFor mu) (muLeq mu) graph (muInitialState mu) n0
         csGraphG = stateGraphForSets csGraph :: Gr (Node, AbstractCacheState) CFGEdge

         costs = (muCostsFor mu) csGraph
         mayBeCSDependent m = (∃) (lsuc graph m) (\(n,l) -> Set.size (costs ! (m,n,l)) > 1)



cacheDataDepSlice :: Graph gr => CacheSize -> CsGraph AbstractCacheState CFGEdge ->  gr (Node, AbstractCacheState) CFGEdge -> Node -> Set Node
cacheDataDepSlice cacheSize csGraph csGraphG m = Set.fromList [ n | y <- Set.toList slice, let Just (n,_) = lab csGraphG' y ]
  where ddeps = cacheDataDepGWork cacheSize csGraphG

        msCsGraph  = [ y | (y, (m_, _)) <- labNodes csGraphG , m_ == m ]
        msCsGraph' = [ y | (y, (m_, _)) <- labNodes csGraphG', m_ == m ]

        csGraphG' = cacheStateGraph'ForVarsAtMForGraph3 relevantCos csGraph m :: Gr (Node, AbstractCacheState) CFGEdge

        edges = Set.fromList [ e | y <- msCsGraph, (_,e) <- lsuc csGraphG y ]
        relevantCos = Set.fromList [ co | e <- Set.toList edges, co <- Set.toList $ CSD.cachedObjectsFor e]

        isinkdom' = isinkdomOfTwoFinger8 csGraphG'
        df'       = idomToDFFast         csGraphG' isinkdom'

        viaDDep = Set.fromList [ y' | (y', (n, cache)) <- labNodes csGraphG', (n,cache) ∈ ns ]
          where ns = Set.fromList [ (n, cacheN) | y <- msCsGraph, 
                                     co <- Set.toList relevantCos,
                                     let Just (m, cacheM) = lab csGraphG y,
                                     not $ isConst cacheM co,
                                     let deps = Map.findWithDefault Set.empty (y,co) ddeps,
                                     yN <- Set.toList $ deps, let Just (n, cacheN) = lab csGraphG yN
                     ]

        slice =
                   go Set.empty (Set.fromList msCsGraph')
              ∪ ((go Set.empty                 viaDDep))
          where go s workset
                    | Set.null workset =    s
                    | otherwise        = go s' (workset0 ∪ new)
                 where (y, workset0) = Set.deleteFindMin workset
                       s' =  Set.insert y s
                       new = fromDF ∖ s'
                       fromDF = Map.findWithDefault Set.empty y df'
