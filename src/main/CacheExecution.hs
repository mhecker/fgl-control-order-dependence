{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheExecution where

import Data.Map.Ordered (OMap, (<|), (|<), (>|), (|>), (<>|), (|<>))
import qualified Data.Map.Ordered as OMap

import qualified Data.List as List


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
import Data.Graph.Inductive.Query.DFS (dfs, rdfs)
import Data.Graph.Inductive.Query.TransClos (trc)

import Unicode
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet)
import           IRLSOD (CFGNode, CFGEdge(..), GlobalState, ThreadLocalState, Var(..), Val, BoolFunction(..), VarFunction(..), useE, defE, use, def)
import qualified IRLSOD as IRLSOD (Input)

import Program (Program(..))
import Program.Generator (toCodeSimple)
import Program.For (compileAllToProgram, For(..))

import Data.Graph.Inductive.Util (mergeTwoGraphs, isTransitive, fromSuccMap, delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominance (mdomOfLfp, sinkdomOfGfp, sinkdomsOf, isinkdomOfTwoFinger8)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (isinkDFTwoFinger)
import Data.Graph.Inductive.Query.Slices.PostDominance (wodTEILSliceViaISinkDom)

import           Data.Graph.Inductive.Query.InfiniteDelay (TraceWith (..), Trace)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (Input(..))




cacheSize = 4

type AccessTime = Integer

cacheMissTime :: AccessTime
cacheMissTime = 10

cacheHitTime  :: AccessTime
cacheHitTime  =  2

-- My cache model assumes a "asynchronous" write-throuh cache, i.e.: writes update the cache, and the main memory update executes "asynchronously" in the background, without stalling the cpu
cacheWriteTime :: AccessTime 
cacheWriteTime = 2

registerAccessTime :: AccessTime
registerAccessTime = 1

noOpTime  :: AccessTime
noOpTime = 1 

undefinedCache = [ "_undef_" ++ (show i) | i <- [1..cacheSize]]
undefinedCacheValue = -1

type ConcreteSemantic a = CFGEdge -> a -> Maybe a

type AbstractSemantic a = CFGEdge -> a -> [a]

type NormalState = (GlobalState,ThreadLocalState, ())
type CacheState = OMap Var Val

type TimeState = Integer


type CacheTimeState = (CacheState, TimeState)
type FullState = (NormalState, CacheState, TimeState)


isCachable (Global _) = True
isCachable (ThreadLocal _) = True -- maybe we dont want this?
isCachable (Register _) = False


twoAddressCode :: For -> For
twoAddressCode (If bf c1 c2) =
  let (loads, bf', _) = twoAddressCodeB 0 bf in case loads of
    Nothing ->          (If bf' (twoAddressCode c1) (twoAddressCode c2))
    Just ls -> ls `Seq` (If bf' (twoAddressCode c1) (twoAddressCode c2))
twoAddressCode (Ass var vf)  =
  let (loads, vf', _) = twoAddressCodeV 0 vf in case loads of
    Nothing ->          (Ass var vf')
    Just ls -> ls `Seq` (Ass var vf')
twoAddressCode (ForC val c) = ForC val (twoAddressCode c)
twoAddressCode (ForV var c) = ForV var (twoAddressCode c)
twoAddressCode (Seq c1 c2 ) = Seq (twoAddressCode c1) (twoAddressCode c2)
twoAddressCode c = c


twoAddressCodeB :: Int -> BoolFunction -> (Maybe For, BoolFunction, Int)
twoAddressCodeB r bf@CTrue =  (Nothing, bf, r)
twoAddressCodeB r bf@CFalse = (Nothing, bf, r)
twoAddressCodeB r bf@(Leq x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Leq x' y', r'')
twoAddressCodeB r bf@(And x y) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
        (loadsY, y', r'') = twoAddressCodeB r' y
    in (loadsX `sseq` loadsY, And x' y', r'')
twoAddressCodeB r bf@(Or x y) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
        (loadsY, y', r'') = twoAddressCodeB r' y
    in (loadsX `sseq` loadsY, And x' y', r'')
twoAddressCodeB r bf@(Not x) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
    in (loadsX, Not x', r')


sseq Nothing r = r
sseq l Nothing = l
sseq (Just l) (Just r) = Just (l `Seq` r)


twoAddressCodeV :: Int -> VarFunction -> (Maybe For, VarFunction, Int)
twoAddressCodeV r vf@(Val _) = (Nothing, vf, r)
twoAddressCodeV r    (Var (Register _)) = undefined
twoAddressCodeV r vf@(Var x) = (Just $ Ass (Register r) vf, Var (Register r), r + 1)
twoAddressCodeV r vf@(Plus x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Plus x' y', r'')
twoAddressCodeV r vf@(Times x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Times x' y', r'')
twoAddressCodeV r bf@(Neg x) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
    in (loadsX, Neg x', r')


consistent :: FullState -> Bool
consistent σ@((globalσ,tlσ,i), cache, _) = OMap.size cache == cacheSize && (∀) (OMap.assocs cache) cons
  where cons (var@(Global      x), val) = x `elem` undefinedCache ||  val == globalσ ! var
        cons (var@(ThreadLocal x), val) = x `elem` undefinedCache ||  val ==     tlσ ! var


cacheAwareReadLRU :: Var -> FullState -> (Val, CacheState, AccessTime)
cacheAwareReadLRU var σ@((globalσ,tlσ,i), cache, _) = case var of
    Global      _ -> lookup globalσ
    ThreadLocal _ -> lookup     tlσ
    Register    _ -> (tlσ ! var, cache, registerAccessTime)
  where lookup someσ = 
          require (consistent σ) $
          case OMap.lookup var cache of
            Nothing  -> let val = someσ ! var in (val, OMap.fromList $ (var, val) : (take (cacheSize - 1) $ OMap.assocs                   cache), cacheMissTime )
            Just val ->                          (val, OMap.fromList $ (var, val) : (                       OMap.assocs $ OMap.delete var cache), cacheHitTime  )


cacheOnlyReadLRU :: Var -> CacheState -> CacheState
cacheOnlyReadLRU var cache = case var of
    Global      _ -> lookup
    ThreadLocal _ -> lookup
    Register    _ -> cache
  where lookup = 
          case OMap.lookup var cache of
            Nothing  -> OMap.fromList $ (var, undefinedCacheValue) : (take (cacheSize - 1) $ OMap.assocs                   cache)
            Just val -> assert (val == undefinedCacheValue) $
                        OMap.fromList $ (var, undefinedCacheValue) : (                       OMap.assocs $ OMap.delete var cache)


cacheAwareReadLRUState :: Monad m => Var -> StateT FullState m Val
cacheAwareReadLRUState var = do
    σ@((globalσ,tlσ,i), cache, time) <- get
    let (val, cache', accessTime) = cacheAwareReadLRU var σ
    put ((globalσ,tlσ,i), cache', time + accessTime)
    return val


cacheOnlyReadLRUState :: Monad m => Var -> StateT CacheState m ()
cacheOnlyReadLRUState var = do
    cache <- get
    let cache' = cacheOnlyReadLRU var cache
    put cache'
    return ()

cacheOnlyWriteLRUState :: Monad m => Var -> StateT CacheState m ()
cacheOnlyWriteLRUState = cacheOnlyReadLRUState



cacheAwareWriteLRU :: Var -> Val -> FullState -> FullState
cacheAwareWriteLRU var val σ@((globalσ,tlσ,i), cache, time ) = case var of
    Global      _ -> let (globalσ', cache', accessTime) = write globalσ in ((globalσ',tlσ ,i), cache', time + accessTime)
    ThreadLocal _ -> let (    tlσ', cache', accessTime) = write     tlσ in ((globalσ ,tlσ',i), cache', time + accessTime)
    Register    _ -> let tlσ' = Map.insert var val tlσ in  ((globalσ,tlσ',i), cache, time + registerAccessTime )
  where write someσ = 
          require (consistent σ) $
          case OMap.lookup var cache of
            Nothing  ->  (Map.insert var val someσ, OMap.fromList $ (var, val) : (take (cacheSize - 1) $ OMap.assocs                   cache), cacheWriteTime )
            Just _   ->  (Map.insert var val someσ, OMap.fromList $ (var, val) : (                       OMap.assocs $ OMap.delete var cache), cacheWriteTime  )


cacheAwareWriteLRUState :: Monad m => Var -> Val -> StateT FullState m ()
cacheAwareWriteLRUState var val = do
    σ <- get
    put $ cacheAwareWriteLRU var val σ
    return ()

initialCacheState :: CacheState
initialCacheState = OMap.fromList [(Global undef, undefinedCacheValue) | undef <- undefinedCache]

initialFullState :: FullState
initialFullState = ((Map.empty, Map.empty, ()), initialCacheState, 0)

exampleSurvey1 :: FullState
exampleSurvey1 = ((  Map.fromList [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4), (Global "x", 42)], Map.empty, ()),
                    OMap.fromList [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4)],
                    0
                 )



cacheAwareLRUEvalB :: Monad m => BoolFunction -> StateT FullState m Bool
cacheAwareLRUEvalB CTrue     = return True
cacheAwareLRUEvalB CFalse    = return False
cacheAwareLRUEvalB (Leq x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal <= yVal
cacheAwareLRUEvalB (And b1 b2) = do
  b1Val <- cacheAwareLRUEvalB b1
  b2Val <- cacheAwareLRUEvalB b2
  return $ b1Val && b2Val
cacheAwareLRUEvalB (Or b1 b2) = do
  b1Val <- cacheAwareLRUEvalB b1
  b2Val <- cacheAwareLRUEvalB b2
  return $ b1Val || b2Val
cacheAwareLRUEvalB (Not b) = do
  bVal <- cacheAwareLRUEvalB b
  return $ not bVal

cacheAwareLRUEvalV :: Monad m => VarFunction -> StateT FullState m Val
cacheAwareLRUEvalV (Val  x) = return x
cacheAwareLRUEvalV (Var  x) = cacheAwareReadLRUState x
cacheAwareLRUEvalV (Plus  x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal + yVal
cacheAwareLRUEvalV (Times x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal * yVal
cacheAwareLRUEvalV (Neg x) = do
  xVal <- cacheAwareLRUEvalV x
  return $ - xVal

{-
instance MonadTrans (StateT s)
lift :: (Monad m, MonadTrans t) => m a -> t m a
lift (cacheAwareLRUevalB bf) :: StateT FullState (State FullState) Val
-}

cacheStepForState :: CFGEdge -> StateT FullState [] FullState
cacheStepForState (Guard b bf) = do
        bVal <- cacheAwareLRUEvalB bf
        σ' <- get
        if (b == bVal) then return σ' else lift []
cacheStepForState (Assign x vf) = do
        xVal <- cacheAwareLRUEvalV vf
        cacheAwareWriteLRUState x xVal
        σ' <- get
        return σ'
cacheStepForState NoOp = do
        σ@(normal,cache,time) <- get
        let σ' = (normal,cache,time + noOpTime)
        put σ'
        return σ'
cacheStepForState (Read  _ _) = undefined
cacheStepForState (Print _ _) = undefined
cacheStepForState (Spawn    ) = undefined
cacheStepForState (Call     ) = undefined
cacheStepForState (Return   ) = undefined

cacheStepFor ::  AbstractSemantic FullState
cacheStepFor e σ = evalStateT (cacheStepForState e) σ




cacheTimeStepForState :: CFGEdge -> StateT FullState [] CacheTimeState
cacheTimeStepForState (Guard b bf) = do
        bVal <- cacheAwareLRUEvalB bf
        (_,cache,time) <- get
        return (cache,time)
cacheTimeStepForState (Assign x vf) = do
        xVal <- cacheAwareLRUEvalV vf
        cacheAwareWriteLRUState x xVal
        (_,cache,time) <- get
        return (cache,time)
cacheTimeStepForState NoOp = do
        (normal,cache,time) <- get
        put (normal, cache, time + noOpTime)
        return (cache,time + noOpTime)
cacheTimeStepForState (Read  _ _) = undefined
cacheTimeStepForState (Print _ _) = undefined
cacheTimeStepForState (Spawn    ) = undefined
cacheTimeStepForState (Call     ) = undefined
cacheTimeStepForState (Return   ) = undefined

cacheTimeStepFor ::  AbstractSemantic CacheTimeState
cacheTimeStepFor e σ = evalStateT (cacheTimeStepForState e) fullState
  where fullState = fakeFullState e σ








cacheOnlyLRUEvalB :: Monad m => BoolFunction -> StateT CacheState m ()
cacheOnlyLRUEvalB CTrue     = return ()
cacheOnlyLRUEvalB CFalse    = return ()
cacheOnlyLRUEvalB (Leq x y) = do
  xVal <- cacheOnlyLRUEvalV x
  yVal <- cacheOnlyLRUEvalV y
  return ()
cacheOnlyLRUEvalB (And b1 b2) = do
  b1Val <- cacheOnlyLRUEvalB b1
  b2Val <- cacheOnlyLRUEvalB b2
  return ()
cacheOnlyLRUEvalB (Or b1 b2) = do
  b1Val <- cacheOnlyLRUEvalB b1
  b2Val <- cacheOnlyLRUEvalB b2
  return ()
cacheOnlyLRUEvalB (Not b) = do
  bVal <- cacheOnlyLRUEvalB b
  return ()

cacheOnlyLRUEvalV :: Monad m => VarFunction -> StateT CacheState m ()
cacheOnlyLRUEvalV (Val  x) = return ()
cacheOnlyLRUEvalV (Var  x) = cacheOnlyReadLRUState x
cacheOnlyLRUEvalV (Plus  x y) = do
  xVal <- cacheOnlyLRUEvalV x
  yVal <- cacheOnlyLRUEvalV y
  return ()
cacheOnlyLRUEvalV (Times x y) = do
  xVal <- cacheOnlyLRUEvalV x
  yVal <- cacheOnlyLRUEvalV y
  return ()
cacheOnlyLRUEvalV (Neg x) = do
  xVal <- cacheOnlyLRUEvalV x
  return ()







cacheOnlyStepForState :: CFGEdge -> StateT CacheState [] CacheState
cacheOnlyStepForState (Guard b bf) = do
        cacheOnlyLRUEvalB bf
        σ' <- get
        return σ'
cacheOnlyStepForState (Assign x vf) = do
        cacheOnlyLRUEvalV vf
        cacheOnlyWriteLRUState x
        σ' <- get
        return σ'
cacheOnlyStepForState NoOp = do
        σ' <- get
        return σ'
cacheOnlyStepForState (Read  _ _) = undefined
cacheOnlyStepForState (Print _ _) = undefined
cacheOnlyStepForState (Spawn    ) = undefined
cacheOnlyStepForState (Call     ) = undefined
cacheOnlyStepForState (Return   ) = undefined

cacheOnlyStepFor ::  AbstractSemantic CacheState
cacheOnlyStepFor e σ = evalStateT (cacheOnlyStepForState e) σ



stateSets :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> (Set (Node, s), Set ((Node, s), CFGEdge, (Node, s)))
stateSets step g  σ0 n0 = (㎲⊒) (Set.fromList [(n0,σ0)], Set.fromList []) f
  where f (cs, es) = (cs ∪ Set.fromList [  (n', σ') | (n, σ, e, n', σ') <- next ],
                      es ∪ Set.fromList [ ((n,  σ ), e, (n', σ')) | (n, σ, e, n', σ') <- next ]
                     )
          where next = [ (n, σ, e, n', σ')  | (n,σ) <- Set.toList cs, (n',e) <- lsuc g n, σ' <- step e σ]

stateGraph :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> gr (Node, s) CFGEdge
stateGraph step g σ0 n0 = mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es]
  where (cs, es) = stateSets step g σ0 n0
        nodes = zip [0..] (Set.toList cs)
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

stateGraphFor :: (Graph gr, Ord s, Ord s') => (s -> s') ->  AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> gr (Node, s') CFGEdge
stateGraphFor α step g σ0 n0 = mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where (cs, es) = stateSets step g σ0 n0
        cs' =  Set.map f cs
          where f (n, s) = (n, α s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α sn), e, (m, α sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

type AbstractCacheState = ([(Var, OMap.Index)], Set Var)

cacheStateGraphForVars :: (Graph gr) => Set Var -> gr CFGNode CFGEdge -> CacheState -> Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVars vars = stateGraphFor α cacheOnlyStepFor
  where α = αFor vars

αFor vars cache = (
            [ (v,i) | (i,(v,s)) <- zip [0..] (OMap.assocs cache), v ∈ vars],
            Set.fromList [ v |  (v,s) <- List.dropWhileEnd (\(v,s) -> not $ v ∈ vars) (OMap.assocs cache), not $ v ∈ vars]
           )

αForReach vars reach cache = (
            [ (v,i) | (i,(v,s)) <- zip [0..] (OMap.assocs cache), v ∈ vars],
            Set.fromList [ v |  (v,s) <- List.dropWhileEnd (\(v,s) -> not $ v ∈ vars) (OMap.assocs cache), not $ v ∈ vars, v ∈ reach]
           )


αForReach2 :: Set Var -> Node -> Set Var -> Node -> OMap Var OMap.Index -> AbstractCacheState
αForReach2 vars mm reach n cache
  | n == mm = (
            [ (v,0) | (v,s) <- OMap.assocs cache, v ∈ vars],
            Set.empty
           )
  | otherwise = αForReach vars reach cache




cacheStateGraphForVarsAndCacheStates :: (Graph gr) => Set Var -> (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVarsAndCacheStates vars (cs, es) =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α sn), e, (m, α sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α = αFor vars

cacheStateGraphForVarsAndCacheStatesAndAccessReachable :: (Graph gr) => Set Var -> (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) -> Map Node (Set Var) -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVarsAndCacheStatesAndAccessReachable vars (cs, es) reach =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α (reach !! n) s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α (reach !! n) sn), e, (m, α (reach !! m) sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α = αForReach vars
        
        (!!) m x = Map.findWithDefault Set.empty x m


cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 :: (Graph gr) => Set Var -> (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) -> Map Node (Set Var) -> Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs, es) reach mm =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α (reach !! n) n s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α (reach !! n) n sn), e, (m, α (reach !! m) m sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α = αForReach2 vars mm

        (!!) m x = Map.findWithDefault Set.empty x m


cacheStateGraphForVarsAtM :: (Graph gr) => Set Var -> (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) ->  Node -> gr (Node, CacheState) CFGEdge
cacheStateGraphForVarsAtM vars (cs, es) mm =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α n s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α n sn), e, (m, α m sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α n cache
          | n == mm   = OMap.fromList [ (v,undefinedCacheValue) | (v,s) <- OMap.assocs cache, v ∈ vars]
          | otherwise = cache






cacheExecutionGraph :: (Graph gr) => gr CFGNode CFGEdge -> FullState -> Node -> gr (Node, FullState) CFGEdge
cacheExecutionGraph = stateGraph cacheStepFor


cacheStateGraph :: (Graph gr) => gr CFGNode CFGEdge -> CacheState -> Node -> gr (Node, CacheState) CFGEdge
cacheStateGraph = stateGraph cacheOnlyStepFor




cacheExecution :: (Graph gr) => gr CFGNode CFGEdge -> FullState -> Node -> [[(Node,TimeState)]]
cacheExecution g σ0 n0 = run σ0 n0
  where run σ@(_,_,time) n = case try σ n of
                    [] -> [[(n, time)]]
                    ts -> ts
        try σ@(_,_,time) n = do
                    (n', e) <- lsuc g n
                    σ' <- cacheStepFor e σ
                    trace0 <- run σ' n'
                    return $ (n, time) : trace0


cacheExecutionLimit :: (Graph gr) => Int -> gr CFGNode CFGEdge -> FullState -> Node -> [[(Node,TimeState)]]
cacheExecutionLimit limit g σ0 n0 = run σ0 n0 0
  where run σ@(_,_,time) n i = if i >= limit then [] else case try σ n i of
                    [] -> [[(n, time)]]
                    ts -> ts
        try σ@(_,_,time) n i = do
                    (n', e) <- lsuc g n
                    σ' <- cacheStepFor e σ
                    trace0 <- run σ' n' (i+1)
                    return $ (n, time) : trace0


prependInitialization :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Node -> Map Var Node -> Map Var Val -> gr CFGNode CFGEdge
prependInitialization g0 n0 newN0 varToNode state =
    g0 `mergeTwoGraphs` g1
  where g1 = mkGraph
               [(n,n) | n <- newN0 : Map.elems varToNode]
               (   [(newN0, if Map.null varToNode then n0 else snd $ head $ Map.assocs varToNode, NoOp)]
                ++ [ (n,n', Assign var (Val $ state ! var))  | ((var,n),(_,n')) <- zip (Map.assocs varToNode) ((tail $ Map.assocs varToNode) ++ [(undefined,n0)]) ]
               )


costsFor :: DynGraph gr =>  gr (Node, CacheState) CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor csGraph  =  (∐) [ Map.fromList [ ((n0, m0, e), Set.fromList [time]) ]  |
                                                 (n, (n0,cs)) <- labNodes csGraph,
                                                 (m, e) <- lsuc csGraph n,
                                                 let Just (m0,_) = lab csGraph m,
                                                 fullState'@(_,time) <- cacheTimeStepFor e (cs, 0)
                      ]

fakeFullState :: CFGEdge -> CacheTimeState -> FullState
fakeFullState e (cs,time) = (
      ((Map.fromList $ OMap.assocs cs) `Map.union` Map.fromList [(var, 0) | var@(Global      _) <- Set.toList $ useE e],
       (Map.fromList $ OMap.assocs cs) `Map.union` Map.fromList [(var, 0) | var@(ThreadLocal _) <- Set.toList $ useE e] `Map.union` Map.fromList [(var, 0) | var@(Register _) <- Set.toList $ useE e],
       ()
      ),
      cs,
      time
     )
   where findWithDefault n x m = case OMap.lookup x m of
           Nothing -> n
           Just v  -> v

cacheCostDecisionGraph :: DynGraph gr => gr CFGNode CFGEdge -> Node -> (gr CFGNode CFGEdge, Map (Node, Node) Integer)
cacheCostDecisionGraph g n0 = (
      mkGraph
        ((labNodes g) ++ ([(n,n) | n <- new]))
        (irrelevant ++ [ (n,m',l)    | ((e@(n,_,l),_), m') <- Map.assocs nodesFor ]
                    ++ [ (m',m,NoOp) | ((e@(_,m,_),_), m') <- Map.assocs nodesFor ]
        ),
                  Map.fromList [ ((n ,m),  cost    ) | e@(n,m,l) <- irrelevant, let [cost] = Set.toList $ costs ! e ]
      `Map.union` Map.fromList [ ((n ,m'), cost - 1) | ((e@(n,_,_),cost), m') <- Map.assocs nodesFor, assert (cost > 1) True   ]
      `Map.union` Map.fromList [ ((m',m ),        1) | ((e@(_,m,_),   _), m') <- Map.assocs nodesFor ]
    )
  where csGraph = cacheStateGraph g initialCacheState n0
        costs = costsFor csGraph

        isRelevant e = nrSuc e > 1
        nrSuc e = Set.size $ costs ! e
        
        nodesFor =               (Map.fromList $ zip [ (e,time) | e <-   relevant, time <- Set.toList $ costs ! e ] new)
                    -- `Map.union`  (Map.fromList       [ ((e,time), | e@(n,m,l) <- irrelevant, let time = 1 ])
        relevant   = [ e | e <- labEdges g,       isRelevant e]
        irrelevant = [ e | e <- labEdges g, not $ isRelevant e]
        totalnew = sum $ fmap nrSuc relevant
        new = newNodes totalnew g



type CacheGraphNode = Node

csdOfLfp graph n0 = (∐) [ Map.fromList [ (n, Set.fromList [ csNodeToNode ! m' | csdom <- csdoms,  m' <- Set.toList csdom, let m = csNodeToNode ! m', let cs' = cacheState  m m',
                                                                           (∃) csdoms (\csdom' -> (∃) (csdom') (\m'' -> csNodeToNode ! m'' == m ∧ cacheState m m'' /= cs')) ]) ] |
                    n  <- nodes graph,
                    n' <- nodesToCsNodes ! n,
                    let csdoms = [ csdom ! x' | x' <- suc csGraph n']
                  ]
  where csdom = sinkdomOfGfp csGraph
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        csNodeToNode   = Map.fromList [ (y, n)  | (y, (n,    _)) <- labNodes csGraph]
        
        cacheState n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e, isCachable var ]
           where cs = assert (n == n') $ cs'
                 Just (n', cs') = lab csGraph y'


fCacheDomNaive :: Graph gr => gr CFGNode CFGEdge -> gr (Node, CacheState) CFGEdge -> Map Node [CacheGraphNode] -> (Map CacheGraphNode (Set Node) ->  Map CacheGraphNode (Set Node))
fCacheDomNaive graph csGraph nodeToCsNodes  = f 
  where f cachedomOf = -- traceShow nodeToCsNodes $ 
                      Map.fromList [ (y, Set.fromList [n])                                                                     | (y, (n, csy)) <- labNodes csGraph]
                    ⊔ Map.fromList [ (y, Set.fromList [ n | n <- Set.toList $ (∏) [ cachedomOf ! x | x <- suc csGraph y ],
                                                            let canonical           = head $ nodeToCsNodes ! n,
                                                            let canonicalCacheState = cacheState n canonical,
                                                            -- traceShow (n, canonical) $
                                                            -- traceShow canonicalCacheState $
                                                            (∀) (nodeToCsNodes ! n) (\y' ->cacheState n y' == canonicalCacheState)
                                                                                                                            ]) | (y, (n, csy)) <- labNodes csGraph, suc csGraph y /= []]
        cacheState n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e, isCachable var ]
           where cs = assert (n == n') $ cs'
                 Just (n', cs') = lab csGraph y'

cacheDomNaiveLfp graph n0 = (㎲⊒) init f
  where init = Map.fromList [ (y, Set.empty) | y <- nodes csGraph]
        f = fCacheDomNaive graph csGraph nodesToCsNodes
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

cacheDomNaiveGfp graph n0 = (𝝂) init f
  where init = Map.fromList [ (y, Set.empty) | y <- nodes csGraph]
             ⊔ Map.fromList [ (y, Set.fromList $ reachable y) | y <- nodes graph]
             ⊔ Map.fromList [ (y, all ∖ (Set.fromList $ reachable y)) | y <- nodes graph]
        f = fCacheDomNaive graph csGraph nodesToCsNodes
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        
        reachable x = suc trncl x
        trncl = trc graph
        all = Set.fromList $ nodes graph


        
cacheDomNodesLfp graph n0 = Map.fromList [ (n, (∏) [ cachedomOf ! y| y <-nodesToCsNodes ! n ]) | n <- nodes graph]
  where cachedomOf = cacheDomNaiveLfp graph n0
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

cacheDomNodesGfp graph n0 = Map.fromList [ (n, (∏) [ cachedomOf ! y| y <-nodesToCsNodes ! n ]) | n <- nodes graph]
  where cachedomOf = cacheDomNaiveGfp graph n0
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]


cacheDepNodesGfp graph n0 = (∐) [ Map.fromList [ (n, Set.fromList [ m | csdom <- csdoms,  m <- Set.toList csdom,
                                                                           (∃) csdoms (\csdom' -> not $ m ∈ csdom') ]) ] |
                    n  <- nodes graph,
                    let csdoms = [ csdom ! x | x <- suc graph n]
                  ]
  where csdom = cacheDomNodesGfp graph n0
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        csNodeToNode   = Map.fromList [ (y, n)  | (y, (n,    _)) <- labNodes csGraph]
        


-- fCacheDomNaive' csGraph all = f 
--   where f cachedomOf = traceShow (restrict cachedomOf (Set.fromList [11, 17, 33])) $
--                       Map.fromList [ (y, Set.fromList [y])                             | y <- nodes csGraph]
--                     ⊔ Map.fromList [ (y, all             )                             | y <- nodes csGraph, suc csGraph y == []]
--                     ⊔ Map.fromList [ (y,  (∏) [ cachedomOf ! x | x <- suc csGraph y ]) | y <- nodes csGraph, suc csGraph y /= []]

-- cacheDomNaive'Gfp graph n0 = (𝝂) init f
--   where init = Map.fromList [ (y, Set.empty) | y <- nodes csGraph]
--              ⊔ Map.fromList [ (y, Set.fromList $ reachable y) | y <- nodes csGraph]
--              ⊔ Map.fromList [ (y, all ∖ (Set.fromList $ reachable y)) | y <- nodes csGraph]
--         f = fCacheDomNaive' csGraph all
--         csGraph = cacheStateGraph graph initialCacheState n0
--         nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        
--         reachable x = suc trncl x
--         trncl = trc csGraph
--         all = Set.fromList $ nodes csGraph

        

fCacheDomNaive' :: Graph gr => gr CFGNode CFGEdge -> gr (Node, CacheState) CFGEdge -> Map Node [CacheGraphNode] -> Map CacheGraphNode (Map Node (Set CacheGraphNode)) -> Set Node -> (Map CacheGraphNode (Set Node) ->  Map CacheGraphNode (Set Node))
fCacheDomNaive' graph csGraph nodeToCsNodes nextReach all = f 
  where f cachedomOf = -- traceShow (restrict cachedomOf (Set.fromList [10, 11, 12, 17, 33])) $ 
                      Map.fromList [ (y, Set.fromList [n])                                                                     | (y, (n, csy)) <- labNodes csGraph]
                    ⊔ Map.fromList [ (y, Set.fromList [ n | n <- Set.toList $ (∏) [ cachedomOf ! x | x <- suc csGraph y ],
                                                            let relevant  = Map.findWithDefault Set.empty n (nextReach ! y),
                                                            let canonical           = Set.findMin relevant,
                                                            let canonicalCacheState = cacheState n canonical,
                                                            -- traceShow (n, canonical) $
                                                            -- traceShow canonicalCacheState $
                                                            (∀) relevant (\y' -> cacheState n y' == canonicalCacheState)
                                                                                                                            ]) | (y, (_, csy)) <- labNodes csGraph, suc csGraph y /= []]
                    ⊔ Map.fromList [ (y, all)                                                                                  | (y, (_, csy)) <- labNodes csGraph, suc csGraph y == []]
        cacheState = cacheStateFor graph csGraph

cacheStateFor graph csGraph n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e, isCachable var ]
           where cs = assert (n == n') $ cs'
                 Just (n', cs') = lab csGraph y'

cacheStateOnFor csGraph vars y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | var <- Set.toList $ vars ]
           where Just (_, cs) = lab csGraph y'



cacheStateUnsafeFor graph csGraph n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e, isCachable var ]
           where cs = cs'
                 Just (_, cs') = lab csGraph y'


allCacheStateFor graph csGraph n y' = fmap (const ()) cs
           where cs = assert (n == n') $ cs'
                 Just (n', cs') = lab csGraph y'



cacheDomNaive'Gfp :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map CacheGraphNode (Set Node)
cacheDomNaive'Gfp graph n0 = (𝝂) init f
  where init = Map.fromList [ (y, Set.empty) | y <- nodes csGraph]
             -- ⊔ Map.fromList [ (y, (∐) [ Set.fromList [n] | y' <- reachable y, let Just (n,_) = lab csGraph y' ]) | y <- nodes csGraph]
              ⊔ Map.fromList [ (y, all ) | y <- nodes csGraph]
        f = fCacheDomNaive' graph csGraph nodesToCsNodes nextReach all
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

        nextReach = nextReachable csGraph
        
        allCs = Set.fromList $ nodes csGraph
        all   = Set.fromList $ nodes   graph

nextReachable ::  Graph gr => gr (Node, s) CFGEdge  -> Map CacheGraphNode (Map Node (Set CacheGraphNode))
nextReachable csGraph = (㎲⊒) init f
  where f nextReach = Map.fromList [ (y, Map.fromList [ (n, Set.fromList [y]) ])                    | (y,(n,_)) <- labNodes csGraph ]
                    ⊔ Map.fromList [ (y, Map.delete n $ (∐) [ nextReach ! x | x <- suc csGraph y] ) | (y,(n,_)) <- labNodes csGraph ]
        init = Map.fromList [ (y, Map.empty) | y <- nodes csGraph ]

cacheDomNodes'Gfp graph n0 = Map.fromList [ (n, (Set.fromList $ dfs [n] graph ) ∩ (∏) [ cachedomOf ! y| y <-nodesToCsNodes ! n ]) | n <- nodes graph]
  where cachedomOf = cacheDomNaive'Gfp graph n0
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]


csd'Of graph n0 = Map.fromList [ (n, Set.fromList [ m | csdom' <- [ csdom ! x | x <- suc graph n] , m <- Set.toList csdom', not $ m ∈ csdom ! n ]) | n <- nodes graph]
  where
        csdom = cacheDomNodes'Gfp graph n0



csd'OfReach graph n0 = -- assert (isTransitive $ (fromSuccMap csdom :: Gr () ())) $ 
    Map.fromList [ (n, Set.fromList [ m | m <- Set.toList $ csdom ! n, (∃) [ csdom ! x | x <- suc graph n, m `elem` suc reach x] (\csdom' -> not $ m ∈ csdom') ] ) | n <- nodes graph]
  where
        csdom = Map.fromList [(n, (all ∖ ms) ∩ (Set.fromList $ suc reach n) ) | (n,ms) <- Map.assocs $ cacheDomNodes'Gfp graph n0]
        reach = trc graph
        all   = Set.fromList $ nodes   graph


csd'''Of :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd'''Of graph n0 = csd
                  -- ⊔ Map.fromList [ (n, Set.fromList [ m' | m <- nodes graph, m' <- Set.toList $ csd ! m, (∃) (nodesToCsNodes ! n) (\y -> (∃) (nodesToCsNodes ! m) (\y' ->  y ∈ csnticd' ! y'))]) | n <- nodes graph]
                  ⊔ Map.fromList [ (n, Set.fromList [ m' | m <- nodes graph, m' <- Set.toList $ csd ! m, 
                         (∃) (suc graph n) (\x -> (∃) (nodesToCsNodes ! x) (\y -> let csY = Set.fromList [cacheState m yy | yy <- Set.toList $ Map.findWithDefault Set.empty m (nextReach ! y) ] in
                           (∃) (suc graph n) (\x' -> (∃) (nodesToCsNodes ! x') (\y' -> let csY' = Set.fromList [cacheState m yy' | yy' <- Set.toList $ Map.findWithDefault Set.empty m (nextReach ! y') ] in
                             (if (n == 9) then traceShow (n,m,m',x,y, x',y', csY, csY') else id) $
                             csY /= csY'
                           ))
                         ))
                       ]
                   ) | n <- nodes graph ]

  where csd = Map.fromList [ (n, Set.fromList [ m  | csdom' <- [ csdom ! x | x <- suc graph n] , m <- Set.toList csdom', not $ m ∈ csdom ! n ]) | n <- nodes graph]
        --  (㎲⊒) (Map.fromList [(n, Set.empty) | n <- nodes graph]) f
        f csd = Map.fromList [ (n, Set.fromList [ m  | csdom' <- [ csdom ! x | x <- suc graph n] , m <- Set.toList csdom', not $ m ∈ csdom ! n ]) | n <- nodes graph]
              ⊔ Map.fromList [ (n, Set.fromList [ m' | m <- nodes graph, m' <- Set.toList $ csd ! m, (∃) (nodesToCsNodes ! n) (\y -> (∃) (nodesToCsNodes ! m) (\y' ->  y ∈ csnticd' ! y'))]) | n <- nodes graph]
              -- ⊔ Map.fromList [ (n, Set.fromList [ m' | m <- nodes graph, m' <- Set.toList $ csd ! m, 
              --            (∃) (suc graph n) (\x -> (∃) (nodesToCsNodes ! x) (\y -> let csY = Set.fromList [cacheState m yy | yy <- Set.toList $ Map.findWithDefault Set.empty m (nextReach ! y) ] in
              --              (∃) (suc graph n) (\x' -> (∃) (nodesToCsNodes ! x') (\y' -> let csY' = Set.fromList [cacheState m yy' | yy' <- Set.toList $ Map.findWithDefault Set.empty m (nextReach ! y') ] in
              --                (if (n == 9) then traceShow (n,m,m',x,y, x',y', csY, csY') else id) $
              --                csY /= csY'
              --              ))
              --            ))
              --          ]
              --      ) | n <- nodes graph ]
        csnticd' = isinkDFTwoFinger csGraph
        csdom = cacheDomNodes'Gfp graph n0
        csGraph = cacheStateGraph graph initialCacheState n0
        cacheState = cacheStateUnsafeFor graph csGraph
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

        nextReach = nextReachable csGraph




fCacheDomNaive'' :: Graph gr => gr CFGNode CFGEdge -> gr (Node, CacheState) CFGEdge -> Map Node [CacheGraphNode] -> Map CacheGraphNode (Map Node (Set CacheGraphNode)) -> Set Node -> [Set Var] -> ( Map (Set Var) (Map CacheGraphNode (Set Node)) ->  Map (Set Var) (Map CacheGraphNode (Set Node))  )
fCacheDomNaive'' graph csGraph nodeToCsNodes nextReach all relevant = f 
  where f cachedomOf = -- traceShow (restrict cachedomOf (Set.fromList [10, 11, 12, 17, 33])) $ 
                      Map.fromList [ (vars, Map.fromList [ (y, Set.fromList [n])                                                                     | (y, (n, csy)) <- labNodes csGraph]) | vars <- relevant ]
                    ⊔ Map.fromList [ (vars, Map.fromList [ (y, Set.fromList [ n | n <- Set.toList $ (∏) [ cachedomOf ! vars ! x | x <- suc csGraph y ],
                                                            let relevant  = Map.findWithDefault Set.empty n (nextReach ! y),
                                                            let canonical           = Set.findMin relevant,
                                                            let canonicalCacheState = cacheState vars canonical,
                                                            -- traceShow (n, canonical) $
                                                            -- traceShow canonicalCacheState $
                                                            (∀) relevant (\y' -> cacheState vars y' == canonicalCacheState)
                                                                                                                            ]) | (y, (_, csy)) <- labNodes csGraph, suc csGraph y /= []] ) | vars <- relevant ]
                    ⊔ Map.fromList [ (vars, Map.fromList [ (y, all)                                                            | (y, (_, csy)) <- labNodes csGraph, suc csGraph y == []] ) | vars <- relevant ]
        cacheState = cacheStateOnFor csGraph


cacheDomNaive''Gfp :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map (Set Var) (Map CacheGraphNode (Set Node))
cacheDomNaive''Gfp graph n0 = (𝝂) init f
  where init = Map.fromList [ (vars, Map.fromList [(y, Set.empty) | y <- nodes csGraph]) | vars <- relevant]
             -- ⊔ Map.fromList [ (y, (∐) [ Set.fromList [n] | y' <- reachable y, let Just (n,_) = lab csGraph y' ]) | y <- nodes csGraph]
              ⊔ Map.fromList [(vars, Map.fromList [(y, all ) | y <- nodes csGraph]) | vars <- relevant ]
        f = fCacheDomNaive'' graph csGraph nodesToCsNodes nextReach all relevant
        csGraph = cacheStateGraph graph initialCacheState n0
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

        nextReach = nextReachable csGraph

        relevant =  [ Set.filter isCachable $ useE e | (n,m,e) <- labEdges graph ] 
        
        allCs = Set.fromList $ nodes csGraph
        all   = Set.fromList $ nodes   graph


-- nextReachableBefore ::  Graph gr => Set Var -> gr CFGNode CFGEdge -> Node -> Map CacheGraphNode (Set CacheGraphNode)
-- nextReachableBefore vars graph n0 = (㎲⊒) init f
--   where f nextReach = Map.fromList [ (y, Set.fromList [y])                                           | (y,(n,_)) <- labNodes csGraph ]
--                     ⊔ Map.fromList [ (y, (∐) [ nextReach ! x | x <- suc csGraph y] )                | (y,(n,_)) <- labNodes csGraph,
--                                                                                                        let canonical = head $ nodesToCsNodes ! n,
--                                                                                                        let canonicalCacheState = cacheState canonical,
--                                                                                                        not $ (∀) (nodesToCsNodes ! n) (\y' -> cacheState y' == canonicalCacheState) ]
--         init = Map.fromList [ (y, Set.empty) | y <- nodes csGraph ]
--         nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
--         cacheState y' = cs
--           where Just (_,cs) = lab csGraph y'
--         csGraph = cacheStateGraphForVars vars graph initialCacheState n0

--         sinkdoms = sinkdomsOf csGraph 


reachableBefore ::  DynGraph gr => Set Var -> gr CFGNode CFGEdge -> Node -> CacheGraphNode -> (Set CacheGraphNode)
reachableBefore vars graph n0 y = Set.fromList [ y' | x <- suc csGraph y,
                                                      y' <- dfs [x] (foldr (flip delSuccessorEdges) csGraph (Set.toList $ sinkdoms ! y)),
                                                      not $ y' ∈ sinkdoms ! y,
                                                      (∃) (lsuc csGraph y') (\(_,e) -> (Set.filter isCachable $ useE e) == vars),
                                                      let Just (m,_) = lab csGraph y',
                                                      let canonicalCacheState = cacheState y',
                                                      not $ (∀) (nodesToCsNodes ! m) (\y'' -> cacheState y'' == canonicalCacheState)
                                  ]
  where
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        cacheState y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        csGraph = cacheStateGraphForVars vars graph initialCacheState n0

        sinkdoms = sinkdomsOf csGraph 



-- reachableBeforeSome ::  DynGraph gr => Set Var -> gr CFGNode CFGEdge -> Node -> Node -> (Set Node)
-- reachableBeforeSome vars graph n0 n m = not $ Set.null $ Set.fromList [ () | y <- nodesToCsNodes ! n,
--                                                       x <- suc csGraph y,
--                                                       y' <- dfs [x] (foldr (flip delSuccessorEdges) csGraph (Set.toList $ sinkdoms ! y)),
--                                                       not $ y' ∈ sinkdoms ! y,
--                                                       (∃) (lsuc csGraph y') (\(_,e) -> useE e == vars),
--                                                       let Just (m,_) = lab csGraph y',
--                                                       let canonicalCacheState = cacheState y',
--                                                       not $ (∀) (nodesToCsNodes ! m) (\y'' -> cacheState y'' == canonicalCacheState),
--                                                       traceShow ((n,y), "->", x, "->*", (y',m)) True
--                                   ]
--   where
--         nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
--         cacheState y' = filter (/= Nothing) $ fmap fst $ cs
--           where Just (_,cs) = lab csGraph y'
--         csGraph = cacheStateGraphForVars vars graph initialCacheState n0

--         sinkdoms = sinkdomsOf csGraph 


reachableBeforeSome ::  DynGraph gr => Set Var -> gr CFGNode CFGEdge -> Node -> Node -> Node -> Bool
reachableBeforeSome vars graph n0 n m = not $ Set.null $ Set.fromList [ () |
                                                      let csGraph' = fromtoNode n m,
                                                      let sinkdoms = sinkdomsOf csGraph',
                                                      let nodesToCsNodes' = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph', n == n' ] ) | n <- nodes graph],
                                                      not $ List.null $ nodes csGraph',
                                                      y  <- nodesToCsNodes' ! n,
                                                      y' <- nodesToCsNodes' ! m,
                                                      (∃) (lsuc csGraph y') (\(_,e) -> (Set.filter isCachable $ useE e) == vars),
                                                      -- traceShow (n,m,y,y', nodes csGraph', sinkdoms ! y, nodesToCsNodes ! m) True,
                                                      x <- suc csGraph y,
                                                      y' `elem` dfs [x] (foldr (flip delSuccessorEdges) csGraph' (Set.toList $ sinkdoms ! y)),
                                                      not $ y' ∈ sinkdoms ! y,
                                                      let Just (m,_) = lab csGraph y',
                                                      let canonicalCacheState = cacheState y',
                                                      not $ (∀) (nodesToCsNodes ! m) (\y'' -> cacheState y'' == canonicalCacheState),
                                                      traceShow ((n,y), "->", x, "->*", (y',m)) True
                                  ]
  where
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        cacheState y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        csGraph = cacheStateGraphForVars vars graph initialCacheState n0
        fromto y m = if List.null $ nodes g'' then g'' else foldr (flip delSuccessorEdges) g'' (nodesToCsNodes ! m)
          where  toM   = rdfs (nodesToCsNodes ! m) csGraph
                 g' = subgraph toM csGraph
                 
                 fromY =  dfs [y] g'
                 g'' = subgraph fromY g'

        fromtoNode n m = Set.fold (flip delSuccessorEdges) g' (Set.fromList (nodesToCsNodes ! m) ∩ (Set.fromList $ nodes g'))
          where  g = csGraph
                 toM   = rdfs (nodesToCsNodes ! m) csGraph
                 g' = subgraph toM csGraph
                 
                 fromN =  dfs (nodesToCsNodes ! n) g'
                 g'' = subgraph fromN g'

        sinkdoms = sinkdomsOf csGraph 

csd''''Of :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd''''Of graph n0 = Map.fromList [ (n, Set.fromList [ m | m <- nodes graph, (_,e) <- lsuc graph m, let vars = Set.filter isCachable $ useE e, reachableBeforeSome vars graph n0 n m ]) | n <- nodes graph]
  -- where fromto n m = sinkdomOfGfp $ g''
  --         where  toM   = rdfs [m] graph
  --                g' = subgraph toM graph
                 
  --                fromN =  dfs [n] g'
  --                g'' = subgraph fromN g'

reachableBeforeSome2 ::  DynGraph gr => Set Var -> gr CFGNode CFGEdge -> Node -> Node -> Set Node
reachableBeforeSome2 vars graph n0 m = Set.fromList [ n |
                                                      let csGraph' = fromtoNode m,
                                                      let isinkdoms = isinkdomOfTwoFinger8 csGraph',
                                                      let nodesToCsNodes' = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph', n == n' ] ) | n <- nodes graph],
                                               assert (not $ List.null $ nodes csGraph') True,
                                               assert (nodesToCsNodes ! m == nodesToCsNodes' ! m) True,
                                                      n <- nodes graph,
                                                      y  <- nodesToCsNodes' ! n,
                                                      -- traceShow (n,m,y,y', nodes csGraph', sinkdoms ! y, nodesToCsNodes ! m) True,
                                                      x <- suc csGraph y,
                                                      y' <- dfs [x] (foldr (flip delSuccessorEdges) csGraph' (Set.toList $ isinkdoms ! y)),
                                                      y' `elem` nodesToCsNodes ! m,
                                               assert ((∃) (lsuc csGraph y') (\(_,e) -> (Set.filter isCachable $ useE e) == vars)) True,
                                                      not $ y' ∈ isinkdoms ! y,
                                                      let Just (mm,_) = lab csGraph y', assert (mm == m) True,
                                                      let canonicalCacheState = cacheState y',
                                                      not $ (∀) ((Set.fromList $ nodesToCsNodes ! m) ∩ (Set.fromList $ dfs [y] csGraph')) (\y'' -> cacheState y'' == canonicalCacheState),
                                                      -- traceShow ((n,y), "->", x, "->*", (y',m)) True,
                                                      True
                                  ]
  where
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        cacheState y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        csGraph = cacheStateGraphForVars vars graph initialCacheState n0

        fromtoNode m = foldr (flip delSuccessorEdges) g' (nodesToCsNodes ! m)
          where  g = csGraph
                 toM   = rdfs (nodesToCsNodes ! m) csGraph
                 g' = subgraph toM csGraph


csd''''Of2 :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd''''Of2 graph n0 = invert'' $ Map.fromList [ (m, reachableBeforeSome2 vars graph n0 m) | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = Set.filter isCachable $ useE e] ]


csd''''Of3 :: (DynGraph gr, Show (gr (Node, AbstractCacheState) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
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
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = Set.filter isCachable $ useE e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable vars (cs,es) reach :: Gr (Node, AbstractCacheState) CFGEdge,
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
        (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0


csd''''Of4 :: (DynGraph gr, Show (gr (Node, AbstractCacheState) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
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
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = Set.filter isCachable $ useE e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: Gr (Node, AbstractCacheState) CFGEdge,
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
        (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0


accessReachableFrom :: Graph gr => gr CFGNode CFGEdge -> Map Node (Set Var)
accessReachableFrom graph = (㎲⊒) init f
  where f reach = Map.fromList [ (n, (∐) [ Set.filter isCachable $ useE e ∪ defE e | (_,e) <- lsuc graph n ]) | n <- nodes graph ]
                ⊔ Map.fromList [ (n, (∐) [ reach ! x | x <- suc graph n] ) | n <- nodes graph ]
        init    = Map.fromList [ (n, Set.empty) | n <- nodes graph ]




merged :: (Graph gr) => gr (Node, s) CFGEdge ->  Map Node (Map CacheGraphNode (Set CacheGraphNode)) -> gr (Node, Set CacheGraphNode) CFGEdge
merged csGraph' equivs =  mkGraph nodes edges
  where edges =  List.nub $ fmap f $ (labEdges csGraph')
          where f (y,y',e) = (toNode ! (n,equiv), toNode ! (n', equiv'), e)
                  where Just (n,_)  = lab csGraph' y
                        Just (n',_) = lab csGraph' y'
                        equiv  = equivs ! n  ! y
                        equiv' = equivs ! n' ! y'
        nodes = zip [0..] [ (n, equiv) | (n, equivN) <- Map.assocs equivs, equiv <- Set.toList $ Set.fromList $ Map.elems equivN ]
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

csGraphFromMergeFor graph n0 m = merged csGraph' equivs
    where (equivs, csGraph') = mergeFromFor graph n0 m

mergeFromFor graph n0 m = (mergeFrom graph' csGraph' idom roots, csGraph')
    where (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0

          vars  = head $ List.nub [ vars | (_,e) <- lsuc graph m, let vars = Set.filter isCachable $ useE e, not $ Set.null vars]
          graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m
          reach = accessReachableFrom graph'
          csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: Gr (Node, AbstractCacheState) CFGEdge
          nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph']
          y's  = nodesToCsNodes ! m
          
          csGraph' = let { toY's = subgraph (rdfs y's csGraph) csGraph } in foldr (flip delSuccessorEdges) toY's y's
          idom = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'
          roots = Set.fromList y's

csdMergeOf :: forall gr. (DynGraph gr, Show (gr (Node, AbstractCacheState) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeOf graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph'' y,
                                        -- (if (n == 7 ∧ m == 17) then traceShow (vars,y,y's, "KKKKKK", csGraph, g'') else id) True,
                                        n /= m
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = Set.filter isCachable $ useE e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: gr (Node, AbstractCacheState) CFGEdge,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph'],
      let y's  = nodesToCsNodes ! m,
      let csGraph' = let { toY's = subgraph (rdfs y's csGraph) csGraph } in foldr (flip delSuccessorEdges) toY's y's,
      let idom' = fmap fromSet $ isinkdomOfTwoFinger8 csGraph',
      let roots' = Set.fromList y's,
      let equivs = mergeFrom graph' csGraph' idom' roots',
      let csGraph'' = merged csGraph' equivs,
      let idom'' = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'',
      let ys = Set.fromList [ y | y <- nodes csGraph'', idom'' ! y == Nothing]
   ]
  where cacheState csGraph y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0

csdMergeDirectOf :: forall gr. (DynGraph gr, Show (gr (Node, CacheState) CFGEdge),  Show (gr (Node, Set CacheGraphNode) CFGEdge )) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph'' y,
                                        -- (if (n == 7 ∧ m == 17) then traceShow (vars,y,y's, "KKKKKK", csGraph, g'') else id) True,
                                        n /= m
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = Set.filter isCachable $ useE e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAtM vars (cs,es) m :: gr (Node, CacheState) CFGEdge,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph'],
      let y's  = nodesToCsNodes ! m,
      let csGraph' = let { toY's = subgraph (rdfs y's csGraph) csGraph } in foldr (flip delSuccessorEdges) toY's y's,
      let idom' = fmap fromSet $ isinkdomOfTwoFinger8 csGraph',
      let roots' = Set.fromList y's,
      let equivs = mergeFrom graph' csGraph' idom' roots',
      let csGraph'' = merged csGraph' equivs,
      let idom'' = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'',
      let ys = Set.fromList [ y | y <- nodes csGraph'', idom'' ! y == Nothing]
   ]
  where cacheState csGraph y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0




mergeFrom ::  (DynGraph gr, Show (gr (Node, s) CFGEdge))=> gr CFGNode CFGEdge -> gr (Node, s) CFGEdge -> Map CacheGraphNode (Maybe CacheGraphNode) -> Set CacheGraphNode -> Map Node (Map CacheGraphNode (Set CacheGraphNode))
mergeFrom graph csGraph idom roots  =  (㎲⊒) init f
  where 
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        f :: Map Node (Map CacheGraphNode (Set CacheGraphNode))
          -> Map Node (Map CacheGraphNode (Set CacheGraphNode))
        f equivs = -- traceShow (Map.filter (\equivs -> (∃) equivs (not . Set.null)) $ equivs, rootOf) $
          (
              Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y' | y' <- ys, Map.lookup y' rootOf == Just r ]) ] | y <- ys, Just r <- [Map.lookup y rootOf ]])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
            ⊔ Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y ] ) ] |  y <- ys, not $ y ∈ roots ])
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
        init = (Map.fromList [ (n, Map.empty) | n <- nodes graph ])
        rootOf = Map.fromList [ (y, r) | y <- nodes csGraph, let r = maxFromTreeM idom y, r ∈ roots ]

-- cacheDomNodes''Gfp graph n0 = Map.fromList [ (n, (Set.fromList $ dfs [n] graph ) ∩ (∏) [ cachedomOf ! y| y <-nodesToCsNodes ! n ]) | n <- nodes graph]
--   where cachedomOf = cacheDomNaive'Gfp graph n0
--         csGraph = cacheStateGraph graph initialCacheState n0
--         nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]




-- cndDef :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
-- cndDef graph n0 = Map.fromList [ (n, Set.fromList [ m | y <- nodesToCsNodes ! n, y' <- Set.toList $ onPathBetween (suc csGraph y) (Set.toList $ sinkdoms ! y) ∖ (Set.insert y $ sinkdoms ! y),
--                                                         let Just (m,_) = lab csGraph y',
--                                                         not $ Set.size $ Set.fromList [ cacheState m y'
--                                                   ]
--                                                         ) | n <- nodes graph]
--   where csGraph = cacheStateGraph graph initialCacheState n0
--         nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
--         sinkdoms = sinkdomsOf csGraph
--         onPathBetween ss ts = fwd
--           where g' = foldr (flip delSuccessorEdges) csGraph ts
--                 fwd = Set.fromList $  dfs ss g'
--         nextReach = nextReachable csGraph
