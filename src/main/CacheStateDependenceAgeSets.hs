{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheStateDependenceAgeSets where

import Data.Ord (comparing)
import qualified Data.List as List

import Data.Bits (xor, (.&.), shiftL, shiftR, complement)

import Data.Maybe (isJust)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Algebra.Lattice(JoinSemiLattice(..), BoundedJoinSemiLattice(..), MeetSemiLattice(..), BoundedMeetSemiLattice(..))

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

import MicroArchitecturalDependence (
    CsGraph, csGraphSize,
    AbstractMicroArchitecturalGraphNode,
    AbstractSemantic,
    TimeState,
    MergedMicroState(..),
    MicroArchitecturalAbstraction(..),
    stateGraphForSets, stateGraph, stateSets,
    muMergeDirectOf,
    merged, mergeFromSlow,
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

newtype Age = Age (Maybe Int) deriving (Show, Eq, SimpleShow)

oneA :: Age
oneA = 1

toAge x = Age $ Just $ x

instance Ord Age where
  compare (Age Nothing ) (Age Nothing ) = EQ
  compare (Age Nothing ) (Age (Just _)) = GT
  compare (Age (Just _)) (Age Nothing ) = LT
  compare (Age (Just x)) (Age (Just y)) = compare x y

instance Num Age where
  (Age Nothing ) + (Age Nothing ) =                    Age Nothing
  (Age Nothing ) + (Age (Just y)) = require (y >= 0) $ Age Nothing
  (Age (Just x)) + (Age Nothing ) = require (x >= 0) $ Age Nothing
  (Age (Just x)) + (Age (Just y)) = require (x >= 0) $ require (y >=0) $ Age $ Just $ x + y

  (Age Nothing ) * (Age Nothing ) =                    Age Nothing
  (Age Nothing ) * (Age (Just y)) = require (y >= 0) $ Age Nothing
  (Age (Just x)) * (Age Nothing ) = require (x >= 0) $ Age Nothing
  (Age (Just x)) * (Age (Just y)) = require (x >= 0) $ require (y >=0) $ Age $ Just $ x * y

  abs a@(Age Nothing)  =                    a
  abs a@(Age (Just x)) = require (x >= 0) $ a

  signum a@(Age Nothing)  =                    oneA
  signum a@(Age (Just x)) = require (x >= 0) $ oneA

  fromInteger = Age . Just . fromInteger

  negate _ = undefined

instance JoinSemiLattice Age where
  join = max

instance BoundedJoinSemiLattice Age where
  bottom = Age $ Just 0

instance MeetSemiLattice Age where
  meet = min

instance BoundedMeetSemiLattice Age where
  top = Age Nothing


type Ages = Set Age

type AbstractCacheState  = Map CachedObject Ages
type AbstractCacheStateTimeEquiv = Set CachedObject
type MergedCacheState = MergedMicroState AbstractCacheState AbstractCacheStateTimeEquiv

type AbstractCacheTimeState = (AbstractCacheState, TimeState)



initialAbstractCacheState :: AbstractCacheState
initialAbstractCacheState = Map.empty

freshTime = Age $ Just 0
fresh = Set.singleton freshTime

infTime = Age $ Nothing
inf = Set.singleton infTime

freshOrInf = Set.fromList [ infTime, freshTime ]

defaultTime hit miss cobj cache = case Map.lookup cobj cache of
  Nothing   -> return miss
  Just ages -> if infTime ∈ ages then [miss, hit] else [hit]

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
  where cacheSizeA = toAge cacheSize
        cobjAges = case Map.lookup cobj cache of
          Nothing   -> inf
          Just ages -> ages
        cache' = fmap inc cache

        inc ages = ages'
          where ages' = filter $ plus1 ages
                filter :: Ages -> Ages
                filter = Set.map f
                  where f a = if a >= cacheSizeA then infTime else a
                plus1 ages = if infTime ∈ ages then Set.insert infTime plussed else plussed
                  where plussed = (∐) [ as a | a@(Age (Just _)) <- Set.toList ages ]
                        as a 
                          | (∀) (Set.delete a $ cobjAges) (       >= a ) = Set.fromList [     a + 1]
                          | (∀) (Set.delete a $ cobjAges) (not . (>= a)) = Set.fromList [ a        ]
                          | otherwise                                     = Set.fromList [ a, a + 1]


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

{-
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
-}

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


{-
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
-}

type AssumedConcreteCachedObject = CachedObject


cacheTimeLRUEvalB :: CacheSize -> BoolFunction -> StateT AbstractCacheTimeState [] [AssumedConcreteCachedObject]
cacheTimeLRUEvalB cacheSize CTrue     = return []
cacheTimeLRUEvalB cacheSize CFalse    = return []
cacheTimeLRUEvalB cacheSize (Leq x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalB cacheSize (Eeq x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalB cacheSize (And b1 b2) = do
  b1Val <- cacheTimeLRUEvalB cacheSize b1
  b2Val <- cacheTimeLRUEvalB cacheSize b2
  return $ b1Val ++ b2Val
cacheTimeLRUEvalB cacheSize (Or b1 b2) = do
  b1Val <- cacheTimeLRUEvalB cacheSize b1
  b2Val <- cacheTimeLRUEvalB cacheSize b2
  return $ b2Val ++ b2Val
cacheTimeLRUEvalB cacheSize (Not b) = do
  bVal <- cacheTimeLRUEvalB cacheSize b
  return $ bVal

cacheTimeLRUEvalV :: CacheSize -> VarFunction -> StateT AbstractCacheTimeState [] [AssumedConcreteCachedObject]
cacheTimeLRUEvalV cacheSize (Val  x) = return []
cacheTimeLRUEvalV cacheSize (Var  x) = do
  cacheTimeReadLRUState cacheSize x
  return []
{- special case for constants -}
cacheTimeLRUEvalV cacheSize (ArrayRead a ix@(Val i)) = do
  cacheTimeLRUEvalV cacheSize ix -- does nothing
  cacheTimeArrayReadLRUState cacheSize a (arrayIndex i)
  return []
{- special case for assertions -}
cacheTimeLRUEvalV cacheSize (ArrayRead a ix@(AssertRange min max i)) = do
  iVal <- cacheTimeLRUEvalV cacheSize i
  i <- lift $ alignedIndicesFor min max
  cacheTimeArrayReadLRUState cacheSize a i
  return $ iVal ++ [CachedArrayRange a i]
cacheTimeLRUEvalV cacheSize (ArrayRead a ix) = do
  ixVal <- cacheTimeLRUEvalV cacheSize ix
  i <- lift alignedIndices
  cacheTimeArrayReadLRUState cacheSize a i
  return $ ixVal ++ [CachedArrayRange a i]
cacheTimeLRUEvalV cacheSize (Plus  x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Minus x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Times x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Div x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Mod x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Xor x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Shl   x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Shr   x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (BAnd  x y) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  yVal <- cacheTimeLRUEvalV cacheSize y
  return $ xVal ++ yVal
cacheTimeLRUEvalV cacheSize (Neg x) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  return $ xVal
cacheTimeLRUEvalV cacheSize (BNot x) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  return $ xVal
cacheTimeLRUEvalV cacheSize (AssertRange min max x) = do
  xVal <- cacheTimeLRUEvalV cacheSize x
  return $ xVal






cacheTimeStepForState :: CacheSize -> CFGEdge -> StateT AbstractCacheTimeState [] ((CFGEdge, [AssumedConcreteCachedObject]), AbstractCacheTimeState)
cacheTimeStepForState cacheSize e@(Guard b bf) = do
        assumed <- cacheTimeLRUEvalB cacheSize bf
        (cache, time) <- get
        return ((e, assumed), (cache, time + guardTime))
cacheTimeStepForState cacheSize e@(Assign x vf) = do
        assumed <- cacheTimeLRUEvalV cacheSize vf
        cacheTimeWriteLRUState cacheSize x
        σ' <- get
        return ((e, assumed), σ')
{- special case for constants -}
cacheTimeStepForState cacheSize e@(AssignArray a ix@(Val i) vf) = do
        assumed <- cacheTimeLRUEvalV cacheSize vf
        [] <- cacheTimeLRUEvalV cacheSize ix -- does nothing
        cacheTimeArrayWriteLRUState cacheSize a (arrayIndex i)
        σ' <- get
        return ((e, assumed), σ')
{- special case for assertions -}
cacheTimeStepForState cacheSize e@(AssignArray a ix@((AssertRange min max i)) vf) = do
        assumedVf <- cacheTimeLRUEvalV cacheSize vf
        assumedI  <- cacheTimeLRUEvalV cacheSize i
        i <- lift $ alignedIndicesFor min max
        cacheTimeArrayWriteLRUState cacheSize a i
        σ' <- get
        return ((e, assumedVf ++ assumedI), σ')
cacheTimeStepForState cacheSize e@(AssignArray a ix vf) = do
        assumedVf <- cacheTimeLRUEvalV cacheSize vf
        assumedIx <- cacheTimeLRUEvalV cacheSize ix
        i <- lift $ alignedIndices
        cacheTimeArrayWriteLRUState cacheSize a i
        σ' <- get
        return ((e, assumedVf ++ assumedIx ++ [CachedArrayRange a i]), σ')
cacheTimeStepForState cacheSize e@(Init _ _ ) = do
        (cache, time) <- get
        return ((e,[]), (cache, time + initTime))
cacheTimeStepForState cacheSize e@(InitArray _ _ ) = do
        (cache, time) <- get
        return ((e,[]), (cache, time + initTime))
cacheTimeStepForState cacheSize e@(NoOp) = do
        (cache, time) <- get
        return ((e,[]), (cache, time + noOpTime))
cacheTimeStepForState cacheSize (Read  _ _) = undefined
cacheTimeStepForState cacheSize (Print _ _) = undefined
cacheTimeStepForState cacheSize (Spawn    ) = undefined
cacheTimeStepForState cacheSize (Call     ) = undefined
cacheTimeStepForState cacheSize (Return   ) = undefined

cacheTimeStepsFor ::  CacheSize -> AbstractSemantic AbstractCacheTimeState (CFGEdge, [AssumedConcreteCachedObject])
cacheTimeStepsFor cacheSize e σ = evalStateT (cacheTimeStepForState cacheSize e) σ

cacheOnlyStepsFor ::  CacheSize -> AbstractSemantic AbstractCacheState (CFGEdge, [AssumedConcreteCachedObject])
cacheOnlyStepsFor cacheSize e σ = fmap first $ evalStateT (cacheTimeStepForState cacheSize e) (σ, 0)
  where first (e, σ) = (e, fst σ)

cacheTimeStepFor ::  CacheSize -> AbstractSemantic AbstractCacheTimeState CFGEdge
cacheTimeStepFor cacheSize e σ = [ (e, (joined, time)) | (_, (_, time)) <- timed]
  where timed  = fmap (\((e, assumed), timedCache) -> (e, timedCache)) $ cacheTimeStepsFor cacheSize e σ
        joined = (∐) timed
        (∐) l@((e, (cache, time)):xs) = foldr join cache xs
          where join (e', (cache', time')) cache = assert (e' == e) (cache `joinNothingCache` cache')

cacheOnlyStepFor ::  CacheSize -> AbstractSemantic AbstractCacheState CFGEdge
cacheOnlyStepFor cacheSize e σ = [ (e, joined) ]
  where untimed = fmap (\((e, assumed), cache) -> (e, cache)) $ cacheOnlyStepsFor cacheSize e σ
        joined = (∐) untimed
        (∐) l@((e,  cache       ):xs) = foldr join cache xs
          where join (e',  cache'        ) cache = assert (e' == e) (cache `joinNothingCache` cache')

joinNothingCache :: AbstractCacheState -> AbstractCacheState -> AbstractCacheState
joinNothingCache cache cache' = left `Map.union` Map.intersectionWith (∪) cache cache' `Map.union` right
  where left  = fmap (Set.insert infTime) $ Map.difference cache  cache'
        right = fmap (Set.insert infTime) $ Map.difference cache' cache

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
cacheDataDep cacheSize (cs, es)  =  (∐) [ Map.fromList [ ((m, cache, co), Set.fromList [ (n, cache') ]) ] | ((m, cache), deps) <- Map.assocs seesDef, ((n, cache'), co) <- Map.keys deps ]
  where seesDef :: Map (Node, AbstractCacheState) (Map ((Node, AbstractCacheState), CachedObject) MinAge)
        seesDef = (㎲⊒) (Map.fromList [ ((m,cache), Map.empty) | (m, caches) <- Map.assocs cs, cache <- Set.toList caches ]) f
          where f sees =  (∐) [ Map.fromList [ ((m, cache'), (killedFor cacheSize e cache cache' $ transDefs cacheSize n e cache cache' (sees ! (n, cache))) ⊔ (defs (n, e, cache, cache')) ) ]
                                      | (n, caches) <- Map.assocs cs, cache <- Set.toList caches, (cache_, e, (m, cache' )) <- Set.toList $ es ! n, cache == cache_ ]

        defs = defsFor cacheSize id

killedFor ::  forall n. (Show n, Ord n) => CacheSize -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) MinAge -> Map (n, CachedObject) MinAge
killedFor cacheSize e cache cache' sees'  = result
  where minUses = minUsesOf e cache
        result = Map.mapMaybeWithKey (newMinAge cacheSize cache cache' minUses) sees'

newMinAge :: CacheSize -> AbstractCacheState -> AbstractCacheState -> [Age] -> (n, CachedObject) -> MinAge -> Maybe MinAge
newMinAge cacheSize cache cache' minUses (_, co) minAge =       let maxCo = mmaximum (Map.findWithDefault inf co    cache)
                                                                    minAge' = if (∃) minUses (\minUse ->
                                                                                   minUse == infTime  ∨  maxCo < minUse
                                                                                 ) then minAge + 1 else minAge

{-
                                                                    minAge'Slow = if (∃) (makesUses e) (\uses -> (∀) uses (\coUse ->
                                                                                   (∀) (Map.findWithDefault inf coUse cache) (\aU -> 
                                                                                   (∀) (Map.findWithDefault inf co    cache) (\a  ->
                                                                                     aU == infTime ∨ a < aU
                                                                                   ))
                                                                                  )) then minAge + 1 else minAge
-}
                                                                    stillValid = minAge' < MinAge cacheSize

                                                                    singular = case Map.lookup co cache' of
                                                                      Nothing -> True
                                                                      Just ages' -> Set.size ages' == 1
                                                                in if (not $ singular) ∧ stillValid then Just minAge' else Nothing

minUsesOf e cache = [ minUse  | uses <- Set.toList $ makesUses e, let mins = [ mminimum $ Map.findWithDefault inf coUse cache | coUse <- uses ], let minUse = List.minimum mins ]


defsFor :: forall n. (Show n, Ord n) => CacheSize -> ((Node, AbstractCacheState) -> n) -> (Node, CFGEdge, AbstractCacheState, AbstractCacheState) -> Map (n, CachedObject) MinAge
defsFor = defsForFast

defsForSlowDef cacheSize nodeFor (n, e, cache, cache') =
     require ([(e, cache')] == cacheOnlyStepFor cacheSize e cache)
   $ assert ((List.null choices) → (Set.null result))
   $ result 
  where result = Set.fromList [ (nodeFor (n, cache), co) | cacheSelected  <- concrete cacheSize cache, co <- Set.toList $ differing cacheSelected ]
        differing selectedCache = result
          where unjoined             = Set.fromList [ cacheU | (_, cacheU) <- cacheOnlyStepsFor cacheSize e selectedCache]
                [(_,selectedCache')] =                                        cacheOnlyStepFor  cacheSize e selectedCache
                result = Set.fromList [ co | cacheU <- Set.toList unjoined, (co, ages) <- Map.assocs cacheU,                                         Just ages /= Map.lookup co selectedCache' ]
                       ∪ Set.fromList [ co |                                (co, ages) <- Map.assocs selectedCache', cacheU <- Set.toList unjoined,  Just ages /= Map.lookup co cacheU         ]

        choices = makesChoice e
        trace = False ∧ n == 52


defsForFast :: forall n. (Show n, Ord n) => CacheSize -> ((Node, AbstractCacheState) -> n) -> (Node, CFGEdge, AbstractCacheState, AbstractCacheState) -> Map (n, CachedObject) MinAge
defsForFast cacheSize nodeFor (n, e, cache, cache') =
     require ([(e, cache')] == cacheOnlyStepFor cacheSize e cache)
   $ require (Set.size (makesUses e) <= 1) -- up to one indetermined (e.g.: array) access
   $ let result' = defsForSlowDef cacheSize nodeFor (n, e, cache, cache') in assert (Map.keysSet result ⊇ result')
   $ result
  where
                second (_,aU,_  ) = aU
                third  (_,_ ,aU') = aU'

                result = (∐) [ Map.fromList [ ((nodeFor (n, cache), co), MinAge a) ] | uses  <- Set.toList $ makesUses e,
                                                      let withMinMax = fmap (\coUse -> let agesUse = Map.findWithDefault inf coUse  cache in (coUse, mminimum agesUse, mmaximum agesUse)) uses,
                                                      let byMin = List.sortBy (comparing second) withMinMax,
                                                      (coUse', _ ,  aU') <- byMin,
                                                      (coUse , aU,  _  ) <- takeWhile ( (< aU') . second) byMin,
                                                      coUse' /= coUse,
                                                      assert (aU < aU') True,
                                                      (co, ages) <- Map.assocs cache,
                                                      let as = [ a  | a  <- Set.toList ages, aU < a ∧ a < aU' ],
                                                      not $ List.null as,
                                                      let (Age (Just a)) = List.minimum as
                            ]
                       ⊔ Map.fromList [ ((nodeFor (n, cache), coChoice), MinAge 0) | choices <- Set.toList $ makesUses e,  not $ List.length choices == 1, coChoice <- choices ]

mminimum :: Ages -> Age
mminimum ages
 | Set.null ages = infTime
 | otherwise     = Set.findMin ages

mmaximum :: Ages -> Age
mmaximum = Set.findMax






concrete :: CacheSize -> AbstractCacheState -> [AbstractCacheState ]
concrete cacheSize cache = concr (Set.fromList [0..cacheSize - 1]) cache

concr :: Set Int -> AbstractCacheState -> [AbstractCacheState ]
concr available cache
                    | Map.null cache = return cache
                    | otherwise = do
                        ma <- Set.toList (ages ∩ (Set.insert infTime $ Set.map toAge available))
                        case ma of
                          (Age Nothing ) ->   concr               available  cache0
                          (Age (Just a)) -> do
                            cache0' <- concr (Set.delete a available) cache0
                            return $ Map.insert co (Set.singleton ma) cache0'
                  where ((co, ages), cache0) = Map.deleteFindMin cache


pseudoConcrete :: AbstractCacheState -> [AbstractCacheState ]
pseudoConcrete = pseudoConcr

pseudoConcr ::  AbstractCacheState -> [AbstractCacheState ]
pseudoConcr cache
                    | Map.null cache = return cache
                    | otherwise = do
                        ma <- Set.toList ages
                        case ma of
                          (Age Nothing ) ->   pseudoConcr cache0
                          (Age (Just a)) -> do
                            cache0' <- pseudoConcr cache0
                            return $ Map.insert co (Set.singleton ma) cache0'
                  where ((co, ages), cache0) = Map.deleteFindMin cache


data TransGraphNode = Object CachedObject | ConcreteState AbstractCacheState | Result AbstractCacheState deriving (Ord, Eq, Show)
instance SimpleShow TransGraphNode where
  simpleShow (Object co) = simpleShow co
  simpleShow (ConcreteState cache) = simpleShow cache
  simpleShow (Result        cache) = simpleShow cache

data TransGraphEdge = Choice Age | Transition deriving (Ord, Eq, Show)
instance SimpleShow TransGraphEdge where
  simpleShow (Choice ma)  = simpleShow ma
  simpleShow (Transition) = ""

data TransGraphTree = Leaf AbstractCacheState | TreeNode CachedObject [(Age, TransGraphTree)] deriving (Show, Eq, Ord)

-- concrCacheTransDecisionGraphs :: CacheSize -> AbstractCacheState -> [(Gr TransGraphNode TransGraphEdge, [CachedObject])]
concrCacheTransDecisionGraphs :: CacheSize -> AbstractCacheState -> [CachedObject] -> CFGEdge -> (Gr TransGraphNode TransGraphEdge)
concrCacheTransDecisionGraphs cacheSize cache assumed e = mkGraph ns es
  where
        (_, ns, es) = evalState (graph tree) 0
        
        graph :: TransGraphTree -> State Int (Int, [(Node, TransGraphNode)], [(Node, Node, TransGraphEdge)])
        graph (Leaf concreteCache) = do
          id <- get
          let idResult = id + 1
          let result = (Map.fromList $ cacheOnlyStepsFor cacheSize e concreteCache) ! (e,assumed)
          put (idResult + 1)
          return $ (id, [(id, ConcreteState concreteCache), (idResult, Result result)], [(id, idResult, Transition)])
        graph (TreeNode co ts) = do
          id <- get
          put (id + 1)
          graphs <- forM (fmap snd ts) graph
          let (ids0, ns0, es0) = foldr cat ([], [], []) graphs
          return $ (
             id,
             (id, Object co) : ns0,
             [(id, id0, Choice c) | (id0, c) <- zip ids0 (fmap fst ts) ] ++ es0
           )

        cat :: forall a b. (Int, [a], [b]) -> ([Int], [a], [b]) -> ([Int], [a], [b])
        cat (id, l, r) (ids, l', r') = (id: ids, l ++ l', r ++ r')

        tree = concrT (Set.fromList [0..cacheSize - 1]) cache Map.empty
        concrT :: Set Int -> AbstractCacheState -> AbstractCacheState -> TransGraphTree
        concrT available cache concreteCache
                    | Map.null cache = Leaf concreteCache
                    | otherwise = TreeNode co successors
                  where ((co, ages), cache0) = Map.deleteFindMin cache
                        successors = do
                          -- ma <- Set.toList (ages ∩ (Set.insert infTime $ Set.map Just available))
                          ma <- Set.toList  ages
                          case ma of
                            (Age Nothing ) -> return $ (ma, concrT               available  cache0                                   concreteCache)
                            (Age (Just a)) -> return $ (ma, concrT (Set.delete a available) cache0 (Map.insert co (Set.singleton ma) concreteCache))


concrCacheTransDecisionGraphsForCo ::
  CacheSize ->
  AbstractCacheState ->
  [CachedObject] ->
  CFGEdge ->
  CachedObject ->
  (Gr (TransGraphNode, TransGraphNode) TransGraphEdge, Gr (TransGraphNode, Set Node) TransGraphEdge)
concrCacheTransDecisionGraphsForCo cacheSize cache assumed e co = {- traceShow toNode' $ traceShow nodes' $ -} (reached, result)
  where graph = concrCacheTransDecisionGraphs cacheSize cache assumed e

        resultReached =  subgraph (rdfs [ m | (m, (Result _, Result _) ) <- labNodes coEquived] coEquived) coEquived
        result = merged reached equivs
            --     idom'' = isinkdomOfTwoFinger8 csGraph''
            -- in Set.fromList [ n | (y, (n,_))   <- labNodes csGraph'', n /= m, Set.null $ idom'' ! y] -- TODO: can we make this wotk with muIsDependent, too?
          where nodesToCsNodes = (∐) [ Map.fromList [ (tag, Set.fromList [ y ]) ] | (y, (tag, _)) <- labNodes reached]
                idom   = fmap fromSet $ isinkdomOfTwoFinger8 reached
                roots  = Set.fromList [ y | (y, (Result _, Result _)) <- labNodes reached]
                equivs = mergeFromSlow nodesToCsNodes reached idom roots
        reached = subgraph (rdfs [ m | (m, (Result _, Result _) ) <- labNodes coEquived] coEquived) coEquived

        coEquived :: Gr (TransGraphNode, TransGraphNode) TransGraphEdge
        coEquived = mkGraph (fmap second nodes') edges'
          where second (n, (e, l)) = (n, (tag l,l))
                tag l@(Object co)     = l
                tag (ConcreteState _) = (ConcreteState Map.empty)
                tag  (Result        _) = (Result        Map.empty)
        nodes' = zip [0..] (Set.toList $ Set.fromList $
                           [           a                   | (n, l)     <- labNodes graph, let a  = α (n , l )]
                           )
        edges' =           [(toNode' ! a, toNode' ! a', e) | (n, n', e) <- labEdges graph, let (Just l) = lab graph n, let (Just l') = lab graph n',
                                                                                           let a  = α (n , l ),
                                                                                           let a' = α (n', l')
                                                                                           -- traceShow (n,l,a, toNode' ! a, "====>", (n',l',a', toNode' ! a')) True
                           ]
        toNode' = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes'

        α cs@(n, Object co)           = cs
        α cs@(n, ConcreteState cache) = cs
        α cs@(_, Result cache') = (sameId, Result $ restrict cache' (Set.singleton co))

        sameId = -1



transDefs :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) MinAge ->   Map (n, CachedObject) MinAge
transDefs = transDefsFast

transDefsSlowPseudoDef :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) MinAge -> Set (n, CachedObject)
transDefsSlowPseudoDef cacheSize n e cache cache' seesN =
     require ([(e, cache')] == cacheOnlyStepFor cacheSize e cache)
   $ result 
          where result   = Map.keysSet seesN ∪ fromSeen
                fromSeen = Set.fromList [ (n', co)  | (co', n's) <- Map.assocs co'Map,
                                                      Just ages <- [Map.lookup co' cache], Set.size ages > 1,

                                                      ((cacheA, cacheA's), (cacheC, cacheC's)) <- cachePairs co' ages,
                                              assert (Map.lookup co' cacheA /= Map.lookup co' cacheC)                                              True,
                                              assert ((∀) (Map.keys cache) (\co -> (co == co') ∨ (Map.lookup co cacheA  == Map.lookup co cacheC))) True,

                                                      (assumed, cacheA') <- Map.assocs          cacheA's,
                                                      let Just  cacheC'  =  Map.lookup assumed  cacheC's,

                                               assert ((Set.fromList $ Map.keys cacheA' ++ Map.keys cacheC') ⊆ cos) True,
                                                      co <- Set.toList cos,
                                                      Map.lookup co cacheA /= Map.lookup co' cacheA,
                                                      Map.lookup co cacheC /= Map.lookup co' cacheC,
                                                      Map.lookup co cacheA' /= Map.lookup co cacheC',

                                                      n' <- Set.toList n's
                            ]
                co'Map :: Map CachedObject (Set n)
                co'Map = (∐) [ Map.fromList [ (co', Set.fromList [ n' ]) ]  | (n', co') <- Map.keys seesN]
                cos = Set.fromList $ Map.keys cache ++ Map.keys cache'


                cachePairs co' ages = [ ((cacheA, cacheA's), (cacheC, cacheC's)) | cachePC <- pseudoConcrete (Map.delete co' cache),
                                                                                   maA <- Set.toList ages,
                                                                                   maC <- Set.toList ages, maA /= maC,
                                                                                   let cacheA = ins co' maA cachePC,
                                                                                   let cacheC = ins co' maC cachePC,
                                                                                   let cacheA's = Map.fromList $ cacheOnlyStepsFor cacheSize e cacheA,
                                                                                   let cacheC's = Map.fromList $ cacheOnlyStepsFor cacheSize e cacheC
                                      ]
                  where ins co' ma cachePC =  case ma of
                          (Age Nothing ) ->                                   cachePC
                          (Age (Just _)) -> Map.insert co' (Set.singleton ma) cachePC




transDefsMegaSlowPseudoDef :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Set (n, CachedObject) -> Set (n, CachedObject)
transDefsMegaSlowPseudoDef cacheSize n e cache cache' seesN = (if cacheCombNr > 20 then traceShow (n, List.length $ assumeds, Map.size cache, Set.size cos, cacheCombNr) else id) $ 
     require ([(e, cache')] == cacheOnlyStepFor cacheSize e cache)
   $ result 
          where cacheCombNr = Map.fold (\s k -> Set.size s * k) 1 cache
                result   = seesN ∪ fromSeen
                assumeds :: [[CachedObject]]
                assumeds = fmap second $ cacheOnlyStepsFor cacheSize e cache
                  where second ((e, assumed), cache) = assumed

                fromSeen = Set.fromList [ (n', co)  | assumed <- assumeds,
                                                      co <- Set.toList cos,
                                                      let equivG = snd $ concrCacheTransDecisionGraphsForCo cacheSize cache assumed e co,
                                                      let idom = isinkdomOfTwoFinger8 equivG,
                                                      (y, y's) <- Map.assocs idom,
                                                      Set.null y's,
                                                      let n's = case lab equivG y of
                                                                 Just (Result _, _)     ->                     Set.empty
                                                                 Just ((Object co'), _) -> Map.findWithDefault Set.empty co' co'Map,
                                                      n' <- Set.toList n's
                            ]
                co'Map :: Map CachedObject (Set n)
                co'Map = (∐) [ Map.fromList [ (co', Set.fromList [ n' ]) ]  | (n', co') <- Set.toList seesN]
                cos = Set.fromList $ Map.keys cache ++ Map.keys cache'



newtype MinAge = MinAge Int deriving (Show, Eq, Ord, Num, Enum, Real, Integral)
instance JoinSemiLattice MinAge where
  join = min

{-
instance BoundedJoinSemiLattice MyInteger where
  bottom = 0
-}

transDefsFast :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) MinAge -> Map (n, CachedObject) MinAge
transDefsFast cacheSize n e cache cache' seesN =
     require ([(e, cache')] == cacheOnlyStepFor cacheSize e cache)
   $ let result' = transDefsSlowPseudoDef cacheSize n e cache cache' seesN in
     assert ((∀) (result' ∖ (Map.keysSet result)) (\(n'Missing, coMissing) ->
                (∃) (Map.assocs seesN) (\((n', coUse), minAge) -> n' == n'Missing ∧
                   (∃) (Map.findWithDefault Set.empty coUse ddeps) (\(co, min) -> co == coMissing ∧ (min < minAge))
                )
            ))
   $ result 
          where result = seesN ⊔ fromSeen

                fromSeen = (∐) [ Map.fromList [ ((n', co), min) ] | ((n', coUse), minAge) <- Map.assocs seesN,
                                                      Just cos <- [Map.lookup coUse ddeps],
                                                      (co, min) <- Set.toList cos,
                                                      not $ min < minAge
                           ]

                ddeps = cacheDepsFast cacheSize e cache


cacheDepsFast :: CacheSize -> CFGEdge -> AbstractCacheState -> Map CachedObject (Set (CachedObject, MinAge))
cacheDepsFast cacheSize e cache =
     id
   $ result 
          where 
                result = Map.fromList [ (coUse, Set.fromList [ (co, min) | (co, ages) <- Map.assocs cache,
                                                      let amin = mminimum ages,
                                                      let amax = mmaximum ages,

                                                      not $ (aUmax <= amin) ∨ (amax <= aUmin),

                                       let as = [ MinAge aa | a@(Age (Just aa)) <- Set.toList ages,
                                                      let lt = aUmax <= a    ,
                                                      let gt =    a  <= aUmin,
                                                      not $ lt ∨ gt
                                                ],
                                                      not $ List.null $ as,
                                                      let min = foldl1 (⊔) as
                                                ]
                                         )
                           | coUseWithMinMax <- coUseWithMinMaxs, (coUse, aUmin, aUmax) <- coUseWithMinMax ]


                coUseWithMinMaxs = [fmap (\coUse -> let agesUse = Map.findWithDefault inf coUse cache in (coUse,       mminimum agesUse, mmaximum agesUse))              uses | uses <- Set.toList $ makesUses e]


cacheDefsFast :: CacheSize -> CFGEdge -> AbstractCacheState -> Set CachedObject
cacheDefsFast cacheSize e cache =
     id
   $ require (Set.size (makesUses e) <= 1) -- up to one indetermined (e.g.: array) access
   $ result
  where
                second (_,aU,_  ) = aU
                third  (_,_ ,aU') = aU'

                result = Set.fromList [ co | uses  <- Set.toList $ makesUses e,
                                                      let withMinMax = fmap (\coUse -> let agesUse = Map.findWithDefault inf coUse  cache in (coUse, mminimum agesUse, mmaximum agesUse)) uses,
                                                      let byMin = List.sortBy (comparing second) withMinMax,
                                                      (coUse', _ ,  aU') <- byMin,
                                                      (coUse , aU,  _  ) <- takeWhile ( (< aU') . second) byMin,
                                                      coUse' /= coUse,
                                                      assert (aU < aU') True,
                                                      (co, ages) <- Map.assocs cache,
                                                      a   <- Set.toList ages,
                                                      aU < a ∧ a < aU'
                            ]
                       ∪ Set.fromList [ coChoice | choices <- Set.toList $ makesUses e,  not $ List.length choices == 1, coChoice <- choices ]

cacheSlice  :: Graph gr => CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Node -> Set Node
cacheSlice cacheSize csGraph = \yM -> undefined

  where cdefs = Map.fromList [ (y, Map.fromList [ (e, cacheDefsFast cacheSize e cache) | (_,e) <- lsuc csGraph y]) | (y, (n, cache)) <- labNodes csGraph ]
        ddeps = Map.fromList [ (y, Map.fromList [ (e, cacheDepsFast cacheSize e cache) | (_,e) <- lsuc csGraph y]) | (y, (n, cache)) <- labNodes csGraph ]



makesChoice e = [ co | choices <- Set.toList $ makesUses e, not $ List.length choices == 1, co <- choices ]
makesUses   e = useE e 
  where

    useE :: CFGEdge -> Set [CachedObject]
    useE (AssignArray a ix@(Val i)                 vf) = useV vf ∪ Set.singleton [CachedArrayRange a (toAlignedIndex $ arrayIndex i) ]
    useE (AssignArray a ix@(AssertRange min max i) vf) = useV vf ∪ Set.singleton [CachedArrayRange a  aligned                       | aligned <- alignedIndicesFor min max ]
    useE (AssignArray a ix                         vf) = useV vf ∪ Set.singleton [CachedArrayRange a  aligned                       | aligned <- alignedIndices ]
    useE (Assign      x vf                           )
      | isCachable (VarName x) = useV vf ∪ Set.singleton [CachedVar x]
      | otherwise              = useV vf
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
    useV (Var  x)
      | isCachable (VarName x) = Set.singleton [CachedVar x]
      | otherwise              = Set.empty
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
cacheDataDepG cacheSize csGraphG  = (∐) [ Map.fromList [ ((yM, co), Set.fromList [ yN ]) ] | (yM, deps) <- Map.assocs seesDef, (yN, co) <- Map.keys deps ]
  where seesDef :: Map Node (Map (Node, CachedObject) MinAge)
        seesDef = (㎲⊒) (Map.fromList [ (y, Map.empty) | y <- nodes csGraphG ]) f
          where f sees =  (∐) [ Map.fromList [ (yM, (killedFor cacheSize e cache cache' $ transDefs cacheSize yN e cache cache' (sees ! yN)) ⊔ (defs yN (n, e, cache, cache'))) ]
                                      | (yN, (n, cache)) <- labNodes csGraphG, (yM, e) <- lsuc csGraphG yN, let Just (m, cache') = lab csGraphG yM]

        defs yN = defsFor cacheSize (const yN)


cacheDataDepGWork :: Graph gr => CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, CachedObject) (Set Node)
cacheDataDepGWork cacheSize csGraphG  = (∐) [ Map.fromList [ ((yM, co), Set.fromList [ yN ]) ] | (yM, deps) <- Map.assocs seesDef, (yN, co) <- Map.keys deps ]
  where seesDef = go (Map.fromList $ zip [0..] orderedNodes) (Map.fromList [ (y, Map.empty) | y <- nodes csGraphG ])

        go workset sees
            | Map.null workset = sees
            | otherwise = if changed then go workset0' (Map.insert yM seesM' sees)
                                     else go workset0                        sees
          where ((_,yM), workset0) = Map.deleteFindMin workset
                seesM  = sees ! yM
                Just (m, cache') = lab csGraphG yM

                seesM' = (∐) [(killedFor cacheSize e cache cache' $ transDefs cacheSize yN e cache cache' (sees ! yN)) ⊔ (defs yN (n, e, cache, cache'))  | (yN,e) <- lpre csGraphG yM,  let Just (n, cache)  = lab csGraphG yN ]
                changed = seesM /= seesM'

                workset0' = foldl (\ws (i, n) -> Map.insert i n ws) workset0 [(node2number ! m, m) | m <- suc csGraphG yM]

        defs yN = defsFor cacheSize (const yN)

        orderedNodes = topsort csGraphG
        node2number = Map.fromList $ zip orderedNodes [0..]


cacheDataDepGWork2 :: Graph gr => CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, CachedObject) (Set Node)
cacheDataDepGWork2 cacheSize csGraphG = reaches
  where defs yN = defsFor cacheSize (const yN)

        reaches :: Map (Node, CachedObject) (Set Node)
        reaches = foldr reachesFor Map.empty (labNodes csGraphG)

        succsM = Map.fromList [ (yN, [(e, yM, cache', minUsesOf e cache, cacheDepsFast cacheSize e cache) | (yM, e) <- lsuc csGraphG yN, let Just (m, cache') = lab csGraphG yM]) | (yN, (n, cache)) <- labNodes csGraphG ]

        reachesFor :: (Node, (Node, AbstractCacheState)) -> Map (Node, CachedObject) (Set Node) -> Map (Node, CachedObject) (Set Node)
        reachesFor (yN, (n, cache)) reaches = foldr ins reaches (Map.keys $ go2 reached reached)

          where reached = Map.fromList [ ((yM, co), minAge) | (yM, e) <- lsuc csGraphG yN, let Just (m, cache') = lab csGraphG yM, ((_, co), minAge) <- Map.assocs $ defs yN (n, e, cache, cache') ]

                ins (yM, co) reaches = Map.alter f (yM, co) reaches
                  where f  Nothing   = Just $ Set.singleton yN
                        f (Just set) = Just $ Set.insert    yN set

                go2 :: Map (Node, CachedObject) MinAge -> Map (Node, CachedObject) MinAge -> Map (Node, CachedObject) MinAge
                go2 workset reached
                    | Map.null workset =                 reached
                    | otherwise        =  go2  workset0' reached'
                  where (((yN, co), minAge), workset0) = Map.deleteFindMin workset
                        Just (n,cache) = lab csGraphG yN
                        succs = succsM ! yN

                        flow  = [ ((yM, co ), minAge') | (e, yM, cache', minUses, _        ) <- succs,
                                                                               Just minAge' <- [newMinAge cacheSize cache cache' minUses (undefined, co) minAge],
                                                                               isNew yM co minAge'
                              ]
                        trans = [ ((yM, co'), min'   ) | (e, yM, cache', minUses, cacheDeps) <- succs,
                                                                               Just cos <- [Map.lookup co cacheDeps ],
                                                                               (co', min) <- Set.toList cos,
                                                                               not $ min < minAge,
                                                                               Just min' <- [newMinAge cacheSize cache cache' minUses (undefined, co') min],
                                                                               isNew yM co' min'
                              ]
                        reached'  = fold ins flow $ fold ins trans $ reached
                        workset0' = fold ins flow $ fold ins trans $ workset0

                        fold f xs y0 = foldr f y0 xs

                        ins (k, v) = Map.insertWith (⊔) k v

                        isNew yM co minAge' = case Map.lookup (yM, co) reached of
                          Nothing       -> True
                          Just minAge'0 -> minAge' < minAge'0


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
            | n == mm ∧ (∀) vars (isConst cache) = [ (n, fmap (Set.map (       const 0 )) $ restrict cache vars) ]
            | n == mm                            = [ (n,                                             cache     ) ]
            | otherwise = [ cs ]


csdFromDataDep :: DynGraph gr => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdFromDataDep cacheSize graph n0 = traceShow (csGraphSize csGraph) $
    invert'' $ Map.fromList [ (m, slice) | m <- nodes graph, mayBeCSDependent m, let slice = Set.delete m $ cacheDataDepSlice cacheSize csGraph csGraphG ddeps m]
  where  mu = cacheAbstraction cacheSize
         csGraph@(cs, es) = stateSets (muStepFor mu) (muLeq mu) graph (muInitialState mu) n0
         csGraphG = stateGraphForSets csGraph :: Gr (Node, AbstractCacheState) CFGEdge

         costs = (muCostsFor mu) csGraph
         mayBeCSDependent m = (∃) (lsuc graph m) (\(n,l) -> Set.size (costs ! (m,n,l)) > 1)

         ddeps = cacheDataDepGWork2 cacheSize csGraphG

cacheDataDepSlice :: Graph gr => CacheSize -> CsGraph AbstractCacheState CFGEdge ->  gr (Node, AbstractCacheState) CFGEdge ->  Map (Node, CachedObject) (Set Node) -> Node -> Set Node
cacheDataDepSlice cacheSize csGraph csGraphG ddeps m = Set.fromList [ n | y <- Set.toList slice, let Just (n,_) = lab csGraphG' y ]
  where

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
