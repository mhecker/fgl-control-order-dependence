{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheStateDependence where

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

type AbstractCacheState  = [CachedObject]
type AbstractCacheStateTimeEquiv = Set CachedObject
type MergedCacheState = MergedMicroState AbstractCacheState AbstractCacheStateTimeEquiv

type AbstractCacheTimeState = (AbstractCacheState, TimeState)



initialAbstractCacheState :: AbstractCacheState
initialAbstractCacheState = []

removeFirstOrButLast      = removeFirstOrButLastMaxSize


cachedObjectsFor :: CFGEdge -> Set CachedObject
cachedObjectsFor = useE
  where 
    useE :: CFGEdge -> Set CachedObject
    useE = useEFor useV useB

    useB :: BoolFunction -> Set CachedObject
    useB = useBFor useV

    useV :: VarFunction -> Set CachedObject
    {- special case for constants -}
    useV (ArrayRead a ix@(Val i)) = Set.fromList [CachedArrayRange a (toAlignedIndex $ arrayIndex i) ]
    {- special case for assertions -}
    useV (ArrayRead a ix@(AssertRange min max i)) =
                                    Set.fromList [CachedArrayRange a           aligned | aligned <- alignedIndicesFor min max ]
    useV (ArrayRead a ix        ) = Set.fromList [CachedArrayRange a           aligned | aligned <- alignedIndices ]
                                  ∪ useV ix
    useV (Val  x)    = Set.empty
    useV (Var  x)    = Set.fromList [CachedVar x]
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


writtenCachedObjectsFor :: CFGEdge -> Set CachedObject
writtenCachedObjectsFor (AssignArray a ix@(Val i)                 _) = Set.fromList [CachedArrayRange a (toAlignedIndex $ arrayIndex i) ]
writtenCachedObjectsFor (AssignArray a ix@(AssertRange min max i) _) = Set.fromList [CachedArrayRange a  aligned                       | aligned <- alignedIndicesFor min max ]
writtenCachedObjectsFor (AssignArray a ix                         _) = Set.fromList [CachedArrayRange a  aligned                       | aligned <- alignedIndices ]
writtenCachedObjectsFor _ = Set.empty




cacheTimeReadLRU :: CacheSize -> Var -> AbstractCacheState -> (AbstractCacheState, AccessTime)
cacheTimeReadLRU cacheSize var cache = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ lookup
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime)
    Register    _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime)
  where cvar = CachedVar var
        lookup =
          case removeFirstOrButLast cacheSize cvar cache of
            Right                       cache0  ->
              ( cvar : cache0, cacheMissTime)
            Left                        cache0  ->
              ( cvar : cache0, cacheHitTime )


sameArrayAs a (CachedArrayRange   a' _ ) = a' == a
sameArrayAs a (CachedUnknownRange a'   ) = a' == a
sameArrayAs _ _                          = False


unknownranges cacheSize arr cache carr hitTime missTime =
    require (isArray carr) $ incache ++ notincache
  where isArray (CachedArrayRange _ _) = True
        isArray (CachedUnknownRange _) = True
        isArray _ = False
        
        incache = do
              (left, carr', right) <- focus (mayMatch carr) cache
              return $
                ( carr' : ( left ++ right            ), hitTime)
        notincache 
            | length carrs < nrOfDifferentCacheLinesPerArray =
               [( carr  : (take (cacheSize - 1) cache), missTime)]
            | otherwise = []
        carrs = [ carr' | carr' <- cache, sameArray carr']
        sameArray = sameArrayAs arr

        mayMatch _                      (CachedVar _) = False
        mayMatch x@(CachedVar _)          _             = error $ "called with carr == " ++ (show x)
        mayMatch (CachedArrayRange a i) (CachedArrayRange a' i') =
            require (toAlignedIndex i == i   ∧  toAlignedIndex i' == i')
          $ a == a' ∧ i == i'
        mayMatch (CachedArrayRange a _) (CachedUnknownRange a') =
            a == a'
        mayMatch (CachedUnknownRange a) (CachedArrayRange a' _) =
            a == a'
        mayMatch (CachedUnknownRange a) (CachedUnknownRange a') =
            a == a'



cacheTimeArrayReadLRU :: CacheSize -> Array -> Index -> AbstractCacheState -> [(AbstractCacheState, AccessTime)]
cacheTimeArrayReadLRU cacheSize arr ix cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ lookup
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        lookup = 
          case removeFirstOrButLast cacheSize carr cache of
            Right _ ->
              unknownranges cacheSize arr cache carr cacheHitTime cacheMissTime
            Left cache0 ->
              [( carr : cache0, cacheHitTime)]

cacheTimeReadLRUState :: Monad m => CacheSize -> Var -> StateT AbstractCacheTimeState m ()
cacheTimeReadLRUState cacheSize var = do
    (cache, time) <- get
    let (cache', accessTime) = cacheTimeReadLRU cacheSize var cache
    put (cache', time + accessTime)
    return ()


cacheTimeWriteLRU :: CacheSize -> Var -> AbstractCacheState -> (AbstractCacheState, AccessTime)
cacheTimeWriteLRU cacheSize var cache = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ write
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime )
    Register    _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime )
  where cvar = CachedVar var
        write = 
          case removeFirstOrButLast cacheSize cvar cache of
            Right cache0      -> ( cvar : cache0, cacheWriteTime )
            Left  cache0      -> ( cvar : cache0, cacheWriteTime )



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
    Array       _ -> assert (      isCachable $ ArrayName arr) $ write
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        write = 
          case removeFirstOrButLast cacheSize carr cache of
            Right _ ->  unknownranges cacheSize arr cache carr cacheWriteTime cacheWriteTime
            Left cache0 ->  [( carr : cache0, cacheWriteTime )]



cacheTimeArrayWriteLRUState :: CacheSize -> Array -> Index -> StateT AbstractCacheTimeState [] ()
cacheTimeArrayWriteLRUState cacheSize arr ix = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayWriteLRU cacheSize arr ix cache
    put (cache', time + accessTime)
    return ()


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
  [] <- cacheTimeLRUEvalV cacheSize ix -- does nothing
  cacheTimeArrayReadLRUState cacheSize a (arrayIndex i)
  return []
{- special case for assertions -}
cacheTimeLRUEvalV cacheSize (ArrayRead a ix@(AssertRange min max i)) = do
  iVal <- cacheTimeLRUEvalV cacheSize i
  i <- lift $ alignedIndicesFor min max
  cacheTimeArrayReadLRUState cacheSize a (arrayIndex i)
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
        cacheTimeArrayWriteLRUState cacheSize a (arrayIndex i)
        σ' <- get
        return ((e, assumedVf ++ assumedI), σ')
cacheTimeStepForState cacheSize e@(AssignArray a ix vf) = do
        assumedVf <- cacheTimeLRUEvalV cacheSize vf
        assumedIx <- cacheTimeLRUEvalV cacheSize ix
        i <- lift alignedIndices
        cacheTimeArrayWriteLRUState cacheSize a i
        σ' <- get
        return ((e,assumedVf ++ assumedIx ++ [CachedArrayRange a i]), σ')
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

cacheTimeStepFor ::  CacheSize -> AbstractSemantic AbstractCacheTimeState (CFGEdge, [AssumedConcreteCachedObject])
cacheTimeStepFor cacheSize e σ = evalStateT (cacheTimeStepForState cacheSize e) σ

cacheOnlyStepFor ::  CacheSize -> AbstractSemantic AbstractCacheState (CFGEdge, [AssumedConcreteCachedObject])
cacheOnlyStepFor cacheSize e σ = fmap first $ evalStateT (cacheTimeStepForState cacheSize e) (σ, 0)
  where first (e, σ) = (e, fst σ)

csLeq = Nothing

cacheStateGraph :: (Graph gr) => CacheSize -> gr CFGNode CFGEdge -> AbstractCacheState -> Node -> gr (Node, AbstractCacheState) (CFGEdge, [AssumedConcreteCachedObject])
cacheStateGraph cacheSize = stateGraph (cacheOnlyStepFor cacheSize) csLeq



cacheStateGraph'ForVarsAtMForGraph2 :: forall gr. (DynGraph gr) => Set CachedObject -> CsGraph AbstractCacheState (CFGEdge, [AssumedConcreteCachedObject]) ->  Node -> gr (Node, MergedCacheState) (CFGEdge, [AssumedConcreteCachedObject])
cacheStateGraph'ForVarsAtMForGraph2 vars (css, es) mm = result
  where result = subgraph (rdfs [ m | (m, (m',_)) <- labNodes merged, m' == mm ] merged) merged

        merged :: gr (Node, MergedCacheState) (CFGEdge, [AssumedConcreteCachedObject])
        merged = mkGraph nodes' edges'

        nodes' = zip [0..] (Set.toList $ Set.fromList $ [           α cs                      | (m,σs)  <- IntMap.toList css,            c                  <- Set.toList σs,  let cs = (m,c)])
        edges' =           [(toNode' ! α cs, toNode' ! α cs', e) | (m,σes) <- IntMap.toList es,  m /= mm,  (c, e, cs'@(m',c')) <- Set.toList σes, let cs = (m,c)]
        toNode' = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes'

        α cs@(n, cache)
          | n == mm   = (mm, Merged $ Set.fromList [ v | v <- cache, v ∈ vars])
          | otherwise = (n,  Unmerged cache)


cacheAbstraction :: CacheSize -> MicroArchitecturalAbstraction AbstractCacheState AbstractCacheStateTimeEquiv (CFGEdge, [AssumedConcreteCachedObject])
cacheAbstraction cacheSize = MicroArchitecturalAbstraction {
      muIsDependent = muIsDependent,
      muMerge = True,
      muGraph'For = muGraph'For,
      muInitialState = initialAbstractCacheState,
      muStepFor = cacheOnlyStepFor cacheSize,
      muTimeStepFor = cacheTimeStepFor cacheSize,
      muToCFGEdge = muToCFGEdge,
      muLeq = csLeq
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph2 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars] ]
        muIsDependent graph roots idom y n (Merged _) = undefined
        muIsDependent graph roots idom y n (Unmerged _) = idom ! y == Nothing
        muToCFGEdge (e,_) = e

csdMergeDirectOf :: forall gr a a'. (DynGraph gr) => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf cacheSize gr n0 = first $ muMergeDirectOf (cacheAbstraction cacheSize) gr n0
  where first (x, _, _) = x

csdGraphFromMergeDirectFor :: forall gr a a'. (DynGraph gr) =>
  CacheSize ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) (CFGEdge, [AssumedConcreteCachedObject])
csdGraphFromMergeDirectFor cacheSize = muGraphFromMergeDirectFor (cacheAbstraction cacheSize)




