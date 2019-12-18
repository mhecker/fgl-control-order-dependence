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

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap


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
import Util (moreSeeds, restrict, invert'', maxFromTreeM, maxFromTreeI, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
import IRLSOD (CFGNode, CFGEdge(..), GlobalState(..), globalEmpty, ThreadLocalState, Var(..), isGlobal, Array(..), arrayIndex, isArrayIndex, arrayMaxIndex, arrayEmpty, ArrayVal, Val, BoolFunction(..), VarFunction(..), Name(..), useE, defE, useEFor, useBFor, useB, useV, use, def, SimpleShow (..), stepFor)
import qualified IRLSOD as IRLSOD (Input)

import Data.Graph.Inductive.Query.PostDominanceFrontiers (idomToDFFast, isinkDFTwoFinger)

import MicroArchitecturalDependence (
    Costs,
    CsGraph, csGraphSize,
    AbstractMicroArchitecturalGraphNode,
    AbstractSemantic,
    TimeState,
    MergeMode(..),
    MergedMicroState(..),
    MicroArchitecturalAbstraction(..),
    stateGraphForSets, stateGraph, stateSets,
    muMergeDirectOf,
    merged, mergeFromSlow,
    edgeCostsFor, isDataDependent,
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
import Data.Graph.Inductive.Query.Slices.PostDominanceFrontiers (nticdNTIODSlice)

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

        max = Set.findMax cobjAges
        min = Set.findMin cobjAges

        plus1Widening a = let a' = a + 1 in if a' >= cacheSizeA then infTime else a'

        inc ages = ages'
          where ages'
                  | max     < minAges  = ages
                  | maxAges < min      = Set.mapMonotonic plus1Widening ages
                  | otherwise          = plus1 ages

                maxAges = Set.findMax ages
                minAges = Set.findMin ages

                plus1 ages = if infTime ∈ ages then Set.insert infTime plussed' else plussed'
                  where plussed = Set.fromList [ if a' >= cacheSizeA then infTime else a' | a@(Age (Just _)) <- Set.toList ages, a' <- as a ]
                        as a 
                          | (∀) cobjAges' (       >= a ) = [     a + 1]
                          | (∀) cobjAges' (not . (>= a)) = [ a        ]
                          | otherwise                    = [ a,  a + 1]
                         where cobjAges' = Set.delete a cobjAges

                        plussed' = assert (result == plussed) $ result
                          where result =  Set.fromAscList [ if a' >= cacheSizeA then infTime else a' | a@(Age (Just _)) <- Set.toAscList ages, a' <- as' a ]
                        as' a 
                          | min >= a  = [     a + 1]
                          | max <= a  = [ a        ]
                          | otherwise = [ a,  a + 1]


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
      muTimeStepFor = cacheTimeStepFor cacheSize,
      muToCFGEdge = id,
      muLeq = csLeq
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph2 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = CSD.cachedObjectsFor e, not $ Set.null vars] ]
        muIsDependent graph roots idom y n (Merged _) = undefined
        muIsDependent graph roots idom y n (Unmerged cache) = (isChoice ∨ isImprecise) ∧ (not isRootDominated)
          where isRootDominated = maxFromTreeI idom y ∈ roots
                isChoice    = (length $ suc graph n) > 1
                isImprecise = (∃) (lsuc graph n) (\(_,e) -> not $ List.null $ isDataDependent e)


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





