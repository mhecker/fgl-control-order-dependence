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



costsFor :: DynGraph gr =>  CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor cacheSize csGraph  =  (∐) [ Map.fromList [ ((n0, m0, e), Set.fromList [time]) ]  |
                                                 (n, (n0,cs)) <- labNodes csGraph,
                                                 (m, e) <- lsuc csGraph n,
                                                 let Just (m0,_) = lab csGraph m,
                                                 (_,fullState'@(_,time)) <- cacheTimeStepFor cacheSize e (cs, 0)
                      ]

costsFor2 :: CacheSize -> CsGraph AbstractCacheState (CFGEdge, [AssumedConcreteCachedObject]) -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor2 cacheSize (css, es)  =  (∐) [ Map.fromList [ ((n, n', e), Set.fromList [time]) ]  |
                                                 (n, σes) <- IntMap.toList es,
                                                 (cache, (e,_), (n', cache')) <- Set.toList σes,
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
cacheCostDecisionGraph cacheSize g n0 = cacheCostDecisionGraphFor cacheSize g $ emap fst $ csGraph
  where csGraph = cacheStateGraph cacheSize g initialAbstractCacheState n0



cacheAbstraction :: CacheSize -> MicroArchitecturalAbstraction AbstractCacheState AbstractCacheStateTimeEquiv (CFGEdge, [AssumedConcreteCachedObject])
cacheAbstraction cacheSize = MicroArchitecturalAbstraction {
      muIsDependent = muIsDependent,
      muMerge = True,
      muGraph'For = muGraph'For,
      muInitialState = initialAbstractCacheState,
      muStepFor = cacheOnlyStepFor cacheSize,
      muLeq = csLeq,
      muCostsFor = costsFor2 cacheSize
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph2 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars] ]
        muIsDependent graph roots idom y n (Merged _) = undefined
        muIsDependent graph roots idom y n (Unmerged _) = idom ! y == Nothing

csdMergeDirectOf :: forall gr a a'. (DynGraph gr) => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf cacheSize = muMergeDirectOf (cacheAbstraction cacheSize)

csdGraphFromMergeDirectFor :: forall gr a a'. (DynGraph gr) =>
  CacheSize ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) (CFGEdge, [AssumedConcreteCachedObject])
csdGraphFromMergeDirectFor cacheSize = muGraphFromMergeDirectFor (cacheAbstraction cacheSize)




