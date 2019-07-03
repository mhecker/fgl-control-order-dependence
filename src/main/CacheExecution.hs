{-# LANGUAGE CPP #-}
#define require assert
module CacheExecution where

import Data.Map.Ordered (OMap, (<|), (|<), (>|), (|>), (<>|), (|<>))
import qualified Data.Map.Ordered as OMap

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set


import Debug.Trace (traceShow)
import Control.Exception.Base (assert)


import Control.Monad.State
import Control.Monad.List


import Data.Graph.Inductive.Graph

import Unicode
import           IRLSOD (CFGNode, CFGEdge(..), GlobalState, ThreadLocalState, Var(..), Val, BoolFunction(..), VarFunction(..), useE)
import qualified IRLSOD as IRLSOD (Input)

import Data.Graph.Inductive.Query.PostDominance (mdomOfLfp, sinkdomOfGfp)
import           Data.Graph.Inductive.Query.InfiniteDelay (TraceWith (..), Trace)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (Input(..))


cacheSize = 4


undefinedCache = [ "_undef_" ++ (show i) | i <- [1..cacheSize]]
undefinedCacheValue = -1

type ConcreteSemantic a = CFGEdge -> a -> Maybe a

type AbstractSemantic a = CFGEdge -> a -> [a]

type NormalState = (GlobalState,ThreadLocalState, ())
type CacheState = OMap Var Val
type FullState = (NormalState, CacheState)

consistent :: FullState -> Bool
consistent σ@((globalσ,tlσ,i), cache) = OMap.size cache == cacheSize && (∀) (OMap.assocs cache) cons
  where cons (var@(Global      x), val) = x `elem` undefinedCache ||  val == globalσ ! var
        cons (var@(ThreadLocal x), val) = x `elem` undefinedCache ||  val ==     tlσ ! var


cacheAwareReadLRU :: Var -> FullState -> (Val, CacheState)
cacheAwareReadLRU var σ@((globalσ,tlσ,i), cache) = case var of
    Global      _ -> lookup globalσ
    ThreadLocal _ -> lookup     tlσ
  where lookup someσ = 
          require (consistent σ) $
          case OMap.lookup var cache of
            Nothing  -> let val = someσ ! var in (val, OMap.fromList $ (var, val) : (take (cacheSize - 1) $ OMap.assocs                   cache) )
            Just val ->                          (val, OMap.fromList $ (var, val) : (                       OMap.assocs $ OMap.delete var cache) )


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
    σ@((globalσ,tlσ,i), cache) <- get
    let (val, cache') = cacheAwareReadLRU var σ
    put ((globalσ,tlσ,i), cache')
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
cacheAwareWriteLRU var val σ@((globalσ,tlσ,i), cache) = case var of
    Global      _ -> let (globalσ', cache') = write globalσ in ((globalσ',tlσ ,i), cache')
    ThreadLocal _ -> let (    tlσ', cache') = write     tlσ in ((globalσ ,tlσ',i), cache')
  where write someσ = 
          require (consistent σ) $
          case OMap.lookup var cache of
            Nothing  ->  (Map.insert var val someσ, OMap.fromList $ (var, val) : (take (cacheSize - 1) $ OMap.assocs                   cache) )
            Just val ->  (Map.insert var val someσ, OMap.fromList $ (var, val) : (                       OMap.assocs $ OMap.delete var cache) )


cacheAwareWriteLRUState :: Monad m => Var -> Val -> StateT FullState m ()
cacheAwareWriteLRUState var val = do
    σ <- get
    put $ cacheAwareWriteLRU var val σ
    return ()

initialCacheState :: CacheState
initialCacheState = OMap.fromList [(Global undef, undefinedCacheValue) | undef <- undefinedCache]
initialFullState = ((Map.empty, Map.empty, Map.empty), initialCacheState)

exampleSurvey1 :: FullState
exampleSurvey1 = ((  Map.fromList [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4), (Global "x", 42)], Map.empty, ()),
                    OMap.fromList [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4)]
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
        σ' <- get
        return σ'
cacheStepForState (Read  _ _) = undefined
cacheStepForState (Print _ _) = undefined
cacheStepForState (Spawn    ) = undefined
cacheStepForState (Call     ) = undefined
cacheStepForState (Return   ) = undefined

cacheStepFor ::  AbstractSemantic FullState
cacheStepFor e σ = evalStateT (cacheStepForState e) σ







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

cacheExecutionGraph :: (Graph gr) => gr CFGNode CFGEdge -> FullState -> Node -> gr (Node, FullState) CFGEdge
cacheExecutionGraph = stateGraph cacheStepFor


cacheStateGraph :: (Graph gr) => gr CFGNode CFGEdge -> CacheState -> Node -> gr (Node, CacheState) CFGEdge
cacheStateGraph = stateGraph cacheOnlyStepFor








type CacheGraphNode = Node

cscdOfLfp graph n0 = (∐) [ Map.fromList [ (n, Set.fromList [ csNodeToNode ! m' | csdom <- csdoms,  m' <- Set.toList csdom, let m = csNodeToNode ! m', let cs' = cacheState  m m',
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


-- fCacheDomNaive :: Graph gr => gr CFGNode CFGEdge -> gr (Node, CacheState) CFGEdge -> Map Node [CacheGraphNode] -> (Map CacheGraphNode (Set Node) ->  Map CacheGraphNode (Set Node))
-- fCacheDomNaive graph csGraph nodeToCsNodes  = f 
--   where f cachedomOf = -- traceShow nodeToCsNodes $ 
--                       Map.fromList [ (y, Set.fromList [n])                                                                     | (y, (n, csy)) <- labNodes csGraph]
--                     ⊔ Map.fromList [ (y, Set.fromList [ n | n <- Set.toList $ (∏) [ cachedomOf ! x | x <- suc csGraph y ],
--                                                             let canonical           = head $ nodeToCsNodes ! n,
--                                                             let canonicalCacheState = cacheState n canonical,
--                                                             -- traceShow (n, canonical) $
--                                                             -- traceShow canonicalCacheState $
--                                                             (∀) (nodeToCsNodes ! n) (\y' ->cacheState n y' == canonicalCacheState)
--                                                                                                                             ]) | (y, (n, csy)) <- labNodes csGraph, suc csGraph y /= []]
--         cacheState n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e ]
--            where cs = assert (n == n') $ cs'
--                  Just (n', cs') = lab csGraph y'

-- cacheDomNaiveLfp graph n0 = (㎲⊒) init f
--   where init = Map.fromList [ (y, Set.empty) | y <- nodes csGraph]
--         f = fCacheDomNaive graph csGraph nodesToCsNodes
--         csGraph = cacheStateGraph graph initialCacheState n0
--         nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

-- cacheDomNodes graph n0 = Map.fromList [ (n, (∏) [ cachedomOf ! y| y <-nodesToCsNodes ! n ]) | n <- nodes graph]
--   where cachedomOf = cacheDomNaiveLfp graph n0
--         csGraph = cacheStateGraph graph initialCacheState n0
--         nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
