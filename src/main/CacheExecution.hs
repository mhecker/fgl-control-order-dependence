{-# LANGUAGE CPP #-}
#define require assert
module CacheExecution where

import Data.Map.Ordered (OMap, (<|), (|<), (>|), (|>), (<>|), (|<>))
import qualified Data.Map.Ordered as OMap

import qualified Data.List as List


import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set


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
import Util (moreSeeds, restrict, invert'')
import           IRLSOD (CFGNode, CFGEdge(..), GlobalState, ThreadLocalState, Var(..), Val, BoolFunction(..), VarFunction(..), useE, use, def)
import qualified IRLSOD as IRLSOD (Input)

import Program (Program(..))
import Program.Generator (toCodeSimple)
import Program.For (compileAllToProgram)

import Data.Graph.Inductive.Util (mergeTwoGraphs, isTransitive, fromSuccMap, delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominance (mdomOfLfp, sinkdomOfGfp, sinkdomsOf, isinkdomOfTwoFinger8)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (isinkDFTwoFinger)
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



consistent :: FullState -> Bool
consistent σ@((globalσ,tlσ,i), cache, _) = OMap.size cache == cacheSize && (∀) (OMap.assocs cache) cons
  where cons (var@(Global      x), val) = x `elem` undefinedCache ||  val == globalσ ! var
        cons (var@(ThreadLocal x), val) = x `elem` undefinedCache ||  val ==     tlσ ! var


cacheAwareReadLRU :: Var -> FullState -> (Val, CacheState, AccessTime)
cacheAwareReadLRU var σ@((globalσ,tlσ,i), cache, _) = case var of
    Global      _ -> lookup globalσ
    ThreadLocal _ -> lookup     tlσ
  where lookup someσ = 
          require (consistent σ) $
          case OMap.lookup var cache of
            Nothing  -> let val = someσ ! var in (val, OMap.fromList $ (var, val) : (take (cacheSize - 1) $ OMap.assocs                   cache), cacheMissTime )
            Just val ->                          (val, OMap.fromList $ (var, val) : (                       OMap.assocs $ OMap.delete var cache), cacheHitTime  )


cacheOnlyReadLRU :: Var -> CacheState -> CacheState
cacheOnlyReadLRU var cache = case var of
    Global      _ -> lookup
    ThreadLocal _ -> lookup
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

type AbstractCacheState = [(Maybe Var, Val)]
cacheStateGraphForVars :: (Graph gr) => Set Var -> gr CFGNode CFGEdge -> CacheState -> Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVars vars = stateGraphFor α cacheOnlyStepFor
  where α cache = [ (if v ∈ vars then Just v else Nothing, s) | (v,s) <- OMap.assocs cache]



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


-- run :: SimpleProgram -> Integer -> Integer -> [[(Node,TimeState)]]
run generated seed1 seed2 = 
                    let pr :: Program Gr
                        pr = compileAllToProgram a b
                          where (a,b) = toCodeSimple generated
                        g0 = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        vars = Set.fromList [ var | n <- nodes g0, var@(Global x) <- Set.toList $ use g0 n ∪ def g0 n]
                        (newN0:new) = (newNodes (Set.size vars) g0)
                        varToNode = Map.fromList $ zip (Set.toList vars) new

                        ms = [ (abs m) `mod` (length $ nodes g0) | m <- moreSeeds seed2 2]
                        initialGlobalState = Map.fromList $ zip (Set.toList vars) (fmap (`rem` 32) $ moreSeeds seed1 (Set.size vars))
                        initialFullState   = ((initialGlobalState, Map.empty, ()), initialCacheState, 0)
                     in prependInitialization g0 n0 newN0 varToNode initialGlobalState

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
       (Map.fromList $ OMap.assocs cs) `Map.union` Map.fromList [(var, 0) | var@(ThreadLocal _) <- Set.toList $ useE e],
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
        
        cacheState n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e ]
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
        cacheState n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e ]
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

cacheStateFor graph csGraph n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e ]
           where cs = assert (n == n') $ cs'
                 Just (n', cs') = lab csGraph y'

cacheStateOnFor csGraph vars y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | var <- Set.toList $ vars ]
           where Just (_, cs) = lab csGraph y'



cacheStateUnsafeFor graph csGraph n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e ]
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

nextReachable ::  Graph gr => gr (Node, CacheState) CFGEdge  -> Map CacheGraphNode (Map Node (Set CacheGraphNode))
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

        relevant =  [ useE e | (n,m,e) <- labEdges graph ] 
        
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
                                                      (∃) (lsuc csGraph y') (\(_,e) -> useE e == vars),
                                                      let Just (m,_) = lab csGraph y',
                                                      let canonicalCacheState = cacheState y',
                                                      not $ (∀) (nodesToCsNodes ! m) (\y'' -> cacheState y'' == canonicalCacheState)
                                  ]
  where
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        cacheState y' = filter (/= Nothing) $ fmap fst $ cs
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
                                                      (∃) (lsuc csGraph y') (\(_,e) -> useE e == vars),
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
        cacheState y' = filter (/= Nothing) $ fmap fst $ cs
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
csd''''Of graph n0 = Map.fromList [ (n, Set.fromList [ m | m <- nodes graph, (_,e) <- lsuc graph m, let vars = useE e, reachableBeforeSome vars graph n0 n m ]) | n <- nodes graph]
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
                                                      y' <- nodesToCsNodes' ! m,
                                               assert ((∃) (lsuc csGraph y') (\(_,e) -> useE e == vars)) True,
                                                      n <- nodes graph,
                                                      y  <- nodesToCsNodes' ! n,
                                                      -- traceShow (n,m,y,y', nodes csGraph', sinkdoms ! y, nodesToCsNodes ! m) True,
                                                      x <- suc csGraph y,
                                                      y' `elem` dfs [x] (foldr (flip delSuccessorEdges) csGraph' (Set.toList $ isinkdoms ! y)),
                                                      not $ y' ∈ isinkdoms ! y,
                                                      let Just (m,_) = lab csGraph y',
                                                      let canonicalCacheState = cacheState y',
                                                      not $ (∀) (nodesToCsNodes' ! m) (\y'' -> cacheState y'' == canonicalCacheState),
                                                      traceShow ((n,y), "->", x, "->*", (y',m)) True
                                  ]
  where
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        cacheState y' = filter (/= Nothing) $ fmap fst $ cs
          where Just (_,cs) = lab csGraph y'
        csGraph = cacheStateGraphForVars vars graph initialCacheState n0

        fromtoNode m = Set.fold (flip delSuccessorEdges) g' (Set.fromList (nodesToCsNodes ! m) ∩ (Set.fromList $ nodes g'))
          where  g = csGraph
                 toM   = rdfs (nodesToCsNodes ! m) csGraph
                 g' = subgraph toM csGraph


csd''''Of2 :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd''''Of2 graph n0 = invert'' $ Map.fromList [ (m, reachableBeforeSome2 vars graph n0 m) | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = useE e] ]





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
