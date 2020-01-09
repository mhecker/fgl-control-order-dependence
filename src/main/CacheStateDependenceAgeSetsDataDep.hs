{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheStateDependenceAgeSetsDataDep where

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

import Data.Graph.Inductive.Util (delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (idomToDFFast, isinkDFTwoFinger)

import MicroArchitecturalDependence (
    Costs,
    CsGraph, csGraphSize,
    MergeMode(..),
    MergedMicroState(..),
    MicroArchitecturalAbstraction(..),
    stateGraphForSets, stateSets,
    merged, mergeFromSlow,
    edgeCostsFor,
    muMergeDirectOf
  )

import CacheExecution (
    CacheSize,
    CachedObject(..), isCachable
  )

import CacheExecution (
    toAlignedIndex, alignedIndicesFor, alignedIndices
  )

import qualified CacheStateDependence as CSD (sameArrayAs, cachedObjectsFor, writtenCachedObjectsFor)


import CacheStateDependenceAgeSets(Age(..), Ages, infTime, inf, fresh, toAge)
import qualified CacheStateDependenceAgeSets as AgeSets

import Data.Graph.Inductive.Query.PostDominance (mdomOfLfp, sinkdomOfGfp, sinkdomsOf, isinkdomOfTwoFinger8)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (isinkDFTwoFinger)
import Data.Graph.Inductive.Query.Slices.PostDominance (wodTEILSliceViaISinkDom)
import Data.Graph.Inductive.Query.Slices.PostDominanceFrontiers (nticdNTIODSlice)


type AbstractCacheState          = AgeSets.AbstractCacheState

initialAbstractCacheState        = AgeSets.initialAbstractCacheState

cacheDataDep :: CacheSize -> CsGraph AbstractCacheState CFGEdge -> Map (Node, AbstractCacheState, CachedObject) (Set (Node, AbstractCacheState))
cacheDataDep cacheSize (cs, es)  =  (∐) [ Map.fromList [ ((m, cache, co), Set.fromList [ (n, cache') ]) ] | ((m, cache), deps) <- Map.assocs seesDef, ((n, cache'), co) <- Map.keys deps ]
  where seesDef :: Map (Node, AbstractCacheState) (Map ((Node, AbstractCacheState), CachedObject) (MinAge, MaxAge))
        seesDef = (㎲⊒) (Map.fromList [ ((m,cache), Map.empty) | (m, caches) <- IntMap.toList cs, cache <- Set.toList caches ]) f
          where f sees =  (∐) [ Map.fromList [ ((m, cache'), (killedFor cacheSize e cache cache' $ transDefs cacheSize n e cache cache' (sees ! (n, cache))) ⊔ (defs (n, e, cache, cache')) ) ]
                                      | (n, caches) <- IntMap.toList cs, cache <- Set.toList caches, (cache_, e, (m, cache' )) <- Set.toList $ es !! n, cache == cache_ ]

        defs = defsFor cacheSize id

        (!!) = (IntMap.!)


killedFor ::  forall n. (Show n, Ord n) => CacheSize -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) (MinAge, MaxAge) -> Map (n, CachedObject) (MinAge, MaxAge)
killedFor cacheSize e cache cache' sees'  = result
  where minUses = minUsesOf e cache
        maxUses = maxUsesOf e cache
        result = Map.mapMaybeWithKey (newMinAge cacheSize cache cache' minUses maxUses) sees'

newMinAge :: CacheSize -> AbstractCacheState -> AbstractCacheState -> [Age] -> [Age] -> (n, CachedObject) -> (MinAge, MaxAge) -> Maybe (MinAge, MaxAge)
newMinAge cacheSize cache cache' minUses maxUses (_, co) (minAge, maxAge) =
                                                                let agesCo = (Map.findWithDefault inf co    cache)
                                                                    maxCo = mmaximum agesCo
                                                                    minCo = mminimum agesCo

                                                                    minAge'0 = if (∃) minUses (\minUse -> case minUse of
                                                                                   Age Nothing       -> True
                                                                                   Age (Just minUse) -> (MaxAge minUse) > maxAge
                                                                                 ) then minAge + 1 else minAge

                                                                    maxAge'0
                                                                     | maxAge >= (MaxAge cacheSize) = maxAge
                                                                     | otherwise =
                                                                              if (∃) maxUses (\maxUse -> case maxUse of
                                                                                   Age Nothing       -> True
                                                                                   Age (Just maxUse) -> (MaxAge maxUse) > maxAge
                                                                                 ) then maxAge + 1 else maxAge
{-
                                                                    minAge'Slow = if (∃) (makesUses e) (\uses -> (∀) uses (\coUse ->
                                                                                   (∀) (Map.findWithDefault inf coUse cache) (\aU -> 
                                                                                   (∀) (Map.findWithDefault inf co    cache) (\a  ->
                                                                                     aU == infTime ∨ a < aU
                                                                                   ))
                                                                                  )) then minAge + 1 else minAge
-}

                                                                    agesCo' = (Map.findWithDefault inf co    cache')
                                                                    maxCo' = mmaximum agesCo'
                                                                    minCo' = mminimum agesCo'
                                                                    minAge' = case minCo' of
                                                                      Age Nothing       -> minAge'0
                                                                      Age (Just minCo') -> minAge'0 ⊓ (MinAge minCo')
                                                                    maxAge' = case maxCo' of
                                                                      Age Nothing       -> maxAge'0
                                                                      Age (Just maxCo') -> maxAge'0 ⊓ (MaxAge maxCo')

                                                                    stillValid = minAge' < MinAge cacheSize

                                                                    singular = case Map.lookup co cache' of
                                                                      Nothing -> True
                                                                      Just ages' -> Set.size ages' == 1
                                                                in if (not $ singular) ∧ stillValid then Just (minAge', maxAge') else Nothing

minUsesOf e cache = [ minUse  | uses <- Set.toList $ makesUses e, let mins = [ mminimum $ Map.findWithDefault inf coUse cache | coUse <- uses ], let minUse = List.minimum mins ]
maxUsesOf e cache = [ maxUse  | uses <- Set.toList $ makesUses e, let maxs = [ mmaximum $ Map.findWithDefault inf coUse cache | coUse <- uses ], let maxUse = List.maximum maxs ]


defsFor :: forall n. (Show n, Ord n) => CacheSize -> ((Node, AbstractCacheState) -> n) -> (Node, CFGEdge, AbstractCacheState, AbstractCacheState) -> Map (n, CachedObject) (MinAge, MaxAge)
defsFor = defsForFast

defsForSlowDef cacheSize nodeFor (n, e, cache, cache') =
     require ((∀) (AgeSets.cacheOnlyStepFor cacheSize e cache) (\(e_, cache'_) -> e_ == e ∧ cache'_ ⊑ cache'))
   $ assert ((List.null choices) → (Set.null result))
   $ result 
  where result = Set.fromList [ (nodeFor (n, cache), co) | cacheSelected  <- concrete cacheSize cache, co <- Set.toList $ differing cacheSelected ]
        differing selectedCache = result
          where unjoined             = Set.fromList [ cacheU | (_, cacheU) <- AgeSets.cacheOnlyStepsFor cacheSize e selectedCache]
                [(_,selectedCache')] =                                        AgeSets.cacheOnlyStepFor  cacheSize e selectedCache
                result = Set.fromList [ co | cacheU <- Set.toList unjoined, (co, ages) <- Map.assocs cacheU,                                         Just ages /= Map.lookup co selectedCache' ]
                       ∪ Set.fromList [ co |                                (co, ages) <- Map.assocs selectedCache', cacheU <- Set.toList unjoined,  Just ages /= Map.lookup co cacheU         ]

        choices = makesChoice e
        trace = False ∧ n == 52



defsForSlowPsuedoDef cacheSize nodeFor (n, e, cache, cache') =
     require ((∀) (AgeSets.cacheOnlyStepFor cacheSize e cache) (\(e_, cache'_) -> e_ == e ∧ cache'_ ⊑ cache'))
   $ assert ((List.null choices) → (Set.null result))
   $ result 
  where result = Set.fromList [ (nodeFor (n, cache), co) | cacheSelected  <- pseudoConcrete cache, co <- Set.toList $ differing cacheSelected ]
        differing selectedCache = result
          where unjoined             = Set.fromList [ cacheU | (_, cacheU) <- AgeSets.cacheOnlyStepsFor cacheSize e selectedCache]
                [(_,selectedCache')] =                                        AgeSets.cacheOnlyStepFor  cacheSize e selectedCache
                result = Set.fromList [ co | cacheU <- Set.toList unjoined, (co, ages) <- Map.assocs cacheU,                                         Just ages /= Map.lookup co selectedCache' ]
                       ∪ Set.fromList [ co |                                (co, ages) <- Map.assocs selectedCache', cacheU <- Set.toList unjoined,  Just ages /= Map.lookup co cacheU         ]

        choices = makesChoice e
        trace = False ∧ n == 52


defsForSlowPsuedoDef2 cacheSize nodeFor (n, e, cache, cache') =
     require ((∀) (AgeSets.cacheOnlyStepFor cacheSize e cache) (\(e_, cache'_) -> e_ == e ∧ cache'_ ⊑ cache'))
   $ assert ((List.null $ makesChoice e) → (Set.null result))
   $ result 
  where result = Set.fromList [ (nodeFor (n, cache), co) |
                                      cacheA  <- pseudoConcrete cache,
                                      (selected1, cacheA'1) <- AgeSets.cacheOnlyStepsFor cacheSize e cacheA,
                                      (selected2, cacheA'2) <- AgeSets.cacheOnlyStepsFor cacheSize e cacheA,
                                      (co, ages1') <- Map.assocs cacheA'1,
                                      Map.lookup co cacheA'2 /= Just ages1'
                              ]


-- cacheDepsSlowDef :: CacheSize -> CFGEdge -> AbstractCacheState -> Map CachedObject (Set CachedObject)
-- cacheDepsSlowDef cacheSize e cache =
--      id
--    $ result 
--           where result = (∐) [ Map.fromList [ (co', Set.fromList [ co ]) ] |
--                                    uses <- Set.toList $ makesUses e,
--                                    co' <- uses,

--                                    cacheA  <- pseudoConcrete cache,
--                                    let cacheA's = Map.fromList $ AgeSets.cacheOnlyStepsFor cacheSize e cacheA,
--                                    cacheC  <- pseudoConcrete cache,
--                                    let cacheC's = Map.fromList $ AgeSets.cacheOnlyStepsFor cacheSize e cacheC,

--                                    Map.lookup co' cacheA /= Map.lookup co' cacheC,
--                                    (∀) (Map.keys cache) (\co -> (co == co') ∨ (Map.lookup co cacheA  == Map.lookup co cacheC)),

--                                    (assumed, cacheA') <- Map.assocs          cacheA's,
--                                    let Just  cacheC'  =  Map.lookup assumed  cacheC's,
--                                    co <- Set.toList $ Map.keysSet cache ∪ Map.keysSet cacheA' ∪ Map.keysSet cacheC',

--                                    Map.lookup co cacheA /= Map.lookup co' cacheA,
--                                    Map.lookup co cacheC /= Map.lookup co' cacheC,

--                                    Map.lookup co cacheA' /= Map.lookup co cacheC'
--                                ]


defsForFast :: forall n. (Show n, Ord n) => CacheSize -> ((Node, AbstractCacheState) -> n) -> (Node, CFGEdge, AbstractCacheState, AbstractCacheState) -> Map (n, CachedObject) (MinAge, MaxAge)
defsForFast cacheSize nodeFor (n, e, cache, cache') =
     require ((∀) (AgeSets.cacheOnlyStepFor cacheSize e cache) (\(e_, cache'_) -> e_ == e ∧ cache'_ ⊑ cache'))
   $ require (Set.size (makesUses e) <= 1) -- up to one indetermined (e.g.: array) access
   $ let result' = defsForSlowDef        cacheSize nodeFor (n, e, cache, cache') in assert (Map.keysSet result ⊇ result')
   -- $ (let result'= defsForSlowPsuedoDef  cacheSize nodeFor (n, e, cache, cache') in if not (Map.keysSet result == result') then error $ show $ ("Def ", e, cache, Map.keysSet result, result') else id)
   -- $ (let result'= defsForSlowPsuedoDef2 cacheSize nodeFor (n, e, cache, cache') in if not (Map.keysSet result == result') then error $ show $ ("Def2", e, cache, Map.keysSet result, result') else id)
   $ assert ((∀) (Map.elems result) (\(MinAge min, MaxAge max) -> max <= min))
   $ result
  where
                second (_,aU,_  ) = aU
                third  (_,_ ,aU') = aU'

                result = (∐) [ Map.fromList [ ((nodeFor (n, cache), co), (MinAge minAge, MaxAge maxAge)) ] | uses  <- Set.toList $ makesUses e,
                                                      let withMinMax = fmap (\coUse -> let agesUse = Map.findWithDefault inf coUse  cache in (coUse, mminimum agesUse, mmaximum agesUse)) uses,
                                                      let byMin = List.sortBy (comparing second) withMinMax,
                                                      (coUse', _ ,  aU') <- byMin,
                                                      (coUse , aU,  _  ) <- takeWhile ( (< aU') . second) byMin,
                                                      coUse' /= coUse,
                                                      assert (aU < aU') True,
                                                      (co, ages) <- Map.assocs cache,
                                                      let as = [ a  | a  <- Set.toList ages, aU < a ∧ a < aU' ],
                                                      not $ List.null as,
                                                      let (Age (Just minAge)) = List.minimum as,
                                                      let maxAge = case List.maximum as of
                                                            Age Nothing       -> cacheSize
                                                            Age (Just maxAge) -> maxAge + 1
                            ]
                       ⊔ Map.fromList [ ((nodeFor (n, cache), coChoice), (MinAge 0, MaxAge maxAge)) |
                                                      choices <- Set.toList $ makesUses e,
                                                      not $ List.length choices == 1,
                                                      coChoice <- choices,
                                                      let max = mmaximum $ Map.findWithDefault inf coChoice cache,
                                                      let maxAge = case max of
                                                            Age Nothing       -> cacheSize
                                                            Age (Just maxAge) -> maxAge + 1 -- TODO: precision, by considering cachet status of other choices
                         ]


type ModsFor gr =
        CacheSize
     -> gr (Node, AbstractCacheState) CFGEdge
     -> CachedObject
     -> Set Node
modsForFast :: DynGraph gr => ModsFor gr
modsForFast cacheSize csGraphG' co =
      id
    $ let result' = modsForSlowDef cacheSize csGraphG' co in assert (result == result')
    $ result
  where
                second (_,aU,_  ) = aU
                third  (_,_ ,aU') = aU'

                result = Set.fromList [ yN | (yN, (n, cache)) <- labNodes csGraphG',
                                                (yN', e) <- lsuc csGraphG' yN, let Just (n', cache') = lab csGraphG' yN,
                                                let maxUses = maxUsesOf e cache,
                                                Just agesCo <- [ Map.lookup co cache ],
                                                let minCo = mminimum agesCo,
                                                (∃) maxUses (\maxUse ->   minCo < maxUse)
                         ]
                       ⊔ Set.fromList [ yN | (yN, (n, cache)) <- labNodes csGraphG',
                                             not $ Map.findWithDefault inf co cache == fresh,
                                             (yN', e) <- lsuc csGraphG' yN, let Just (n', cache') = lab csGraphG' yN,
                                             uses <- Set.toList $ makesUses e,
                                             co `elem` uses
                         ]

modsForSlowDef :: DynGraph gr => ModsFor gr
modsForSlowDef cacheSize csGraphG' co =
      id
    $ result
  where
                second (_,aU,_  ) = aU
                third  (_,_ ,aU') = aU'

                result = Set.fromList [ yN | (yN, (n, cache)) <- labNodes csGraphG',
                                                (yN', e) <- lsuc csGraphG' yN,
                                                uses <- Set.toList $ makesUses e,
                                                co' <- uses,
                                                (∃) (Map.findWithDefault inf co  cache) (\a -> 
                                                  (∃) (Map.findWithDefault inf co' cache) (\a' ->
                                                    a < a'
                                                ))
                         ]
                       ⊔ Set.fromList [ yN | (yN, (n, cache)) <- labNodes csGraphG',
                                             not $ Map.findWithDefault inf co cache == fresh,
                                             (yN', e) <- lsuc csGraphG' yN,
                                             uses <- Set.toList $ makesUses e,
                                             co `elem` uses
                         ]



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
          let result = (Map.fromList $ AgeSets.cacheOnlyStepsFor cacheSize e concreteCache) ! (e,assumed)
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
                idom   = IntMap.fromAscList [ (n,m) | (n, ms) <- Map.toAscList $ isinkdomOfTwoFinger8 reached, not $ Set.null ms, let [m] = Set.toList ms]
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



transDefs :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) (MinAge, MaxAge) ->   Map (n, CachedObject) (MinAge, MaxAge)
transDefs = transDefsFast

transDefsSlowPseudoDef :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) (MinAge, MaxAge) -> Set (n, CachedObject)
transDefsSlowPseudoDef cacheSize n e cache cache' seesN =
     require ([(e, cache')] == AgeSets.cacheOnlyStepFor cacheSize e cache)
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
                                                                                   let cacheA's = Map.fromList $ AgeSets.cacheOnlyStepsFor cacheSize e cacheA,
                                                                                   let cacheC's = Map.fromList $ AgeSets.cacheOnlyStepsFor cacheSize e cacheC
                                      ]
                  where ins co' ma cachePC =  case ma of
                          (Age Nothing ) ->                                   cachePC
                          (Age (Just _)) -> Map.insert co' (Set.singleton ma) cachePC




transDefsMegaSlowPseudoDef :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Set (n, CachedObject) -> Set (n, CachedObject)
transDefsMegaSlowPseudoDef cacheSize n e cache cache' seesN = (if cacheCombNr > 20 then traceShow (n, List.length $ assumeds, Map.size cache, Set.size cos, cacheCombNr) else id) $ 
     require ([(e, cache')] == AgeSets.cacheOnlyStepFor cacheSize e cache)
   $ result 
          where cacheCombNr = Map.foldr (\s k -> Set.size s * k) 1 cache
                result   = seesN ∪ fromSeen
                assumeds :: [[CachedObject]]
                assumeds = fmap second $ AgeSets.cacheOnlyStepsFor cacheSize e cache
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

instance MeetSemiLattice MinAge where
  meet = max


newtype MaxAge = MaxAge Int deriving (Show, Eq, Ord, Num, Enum, Real, Integral)
instance JoinSemiLattice MaxAge where
  join = max

instance MeetSemiLattice MaxAge where
  meet = min


{-
instance BoundedJoinSemiLattice MyInteger where
  bottom = 0
-}

transDefsFast :: forall n. (Show n, Ord n) => CacheSize -> Node -> CFGEdge -> AbstractCacheState -> AbstractCacheState -> Map (n, CachedObject) (MinAge, MaxAge) -> Map (n, CachedObject) (MinAge, MaxAge)
transDefsFast cacheSize n e cache cache' seesN =
     require ([(e, cache')] == AgeSets.cacheOnlyStepFor cacheSize e cache)
   $ let result' = transDefsSlowPseudoDef cacheSize n e cache cache' seesN in
     assert ((∀) (result' ∖ (Map.keysSet result)) (\(n'Missing, coMissing) ->
                (∃) (Map.assocs seesN) (\((n', coUse), (minAge, maxAge)) -> n' == n'Missing ∧
                   (∃) (Map.findWithDefault Set.empty coUse ddeps) (\(co, min, max) -> co == coMissing ∧ (MinAge max < minAge) ∧ (MaxAge min > maxAge))
                )
            ))
   $ result 
          where result = seesN ⊔ fromSeen

                fromSeen = (∐) [ Map.fromList [ ((n', co), (MinAge min, MaxAge max)) ] | ((n', coUse), (minAge, maxAge)) <- Map.assocs seesN,
                                                      Just cos <- [Map.lookup coUse ddeps],
                                                      (co, min, max) <- Set.toList cos,
                                                      not $ (MinAge max) < minAge,
                                                      not $ (MaxAge min) > maxAge
                           ]

                ddeps = cacheDepsFast cacheSize e cache


cacheDepsFast :: CacheSize -> CFGEdge -> AbstractCacheState -> Map CachedObject (Set (CachedObject, Int, Int))
cacheDepsFast cacheSize e cache =
     id
   -- $ (let { resultSlow = cacheDepsSlowDef cacheSize e cache ;
   --         resultNoMinMax = Map.filter (not . Set.null) $ Map.mapWithKey (\coUse cos -> Set.delete coUse $ Set.map first $ cos) result ;
   --         first (co,_,_) = co ;
   --       } in if (resultNoMinMax /= resultSlow ) then error $ show $ (cacheSize, e, cache, resultNoMinMax, resultSlow) else id)
   $ result 
          where 
                result = Map.fromList [ (coUse, Set.fromList [ (co, mmin, mmax) | (co, ages) <- Map.assocs cache,
                                                      let amin = mminimum ages,
                                                      let amax = mmaximum ages,


                                       let as = [ aa | a@(Age (Just aa)) <- Set.toList ages,
                                                      let lt = aUmax <= a    ,
                                                      let gt =    a  <= aUmin,
                                                      not $ lt ∨ gt
                                                ],
                                                      let left = (not $ (aUmax <= amin) ∨ (amax <= aUmin))
                                                               ∧ (not $ List.null $ as),
                                                      let right = not $ List.null $ [ a | a <- Set.toList ages, aUmin < a  ∧  a < aUmax ],

                                                      assert (left == right) True,

                                                      left,
                                                      let mmin = foldl1 min as,
                                                      let mmax = foldl1 max as
                                                ]
                                         )
                           | coUseWithMinMax <- coUseWithMinMaxs, (coUse, aUmin, aUmax) <- coUseWithMinMax ]


                coUseWithMinMaxs = [fmap (\coUse -> let agesUse = Map.findWithDefault inf coUse cache in (coUse,       mminimum agesUse, mmaximum agesUse))              uses | uses <- Set.toList $ makesUses e]



cacheDepsSlowDef :: CacheSize -> CFGEdge -> AbstractCacheState -> Map CachedObject (Set CachedObject)
cacheDepsSlowDef cacheSize e cache =
     id
   $ result 
          where result = (∐) [ Map.fromList [ (co', Set.fromList [ co ]) ] |
                                   uses <- Set.toList $ makesUses e,
                                   co' <- uses,

                                   cacheA  <- pseudoConcrete cache,
                                   let cacheA's = Map.fromList $ AgeSets.cacheOnlyStepsFor cacheSize e cacheA,
                                   cacheC  <- pseudoConcrete cache,
                                   let cacheC's = Map.fromList $ AgeSets.cacheOnlyStepsFor cacheSize e cacheC,

                                   Map.lookup co' cacheA /= Map.lookup co' cacheC,
                                   (∀) (Map.keys cache) (\co -> (co == co') ∨ (Map.lookup co cacheA  == Map.lookup co cacheC)),

                                   (assumed, cacheA') <- Map.assocs          cacheA's,
                                   let Just  cacheC'  =  Map.lookup assumed  cacheC's,
                                   co <- Set.toList $ Map.keysSet cache ∪ Map.keysSet cacheA' ∪ Map.keysSet cacheC',

                                   Map.lookup co cacheA /= Map.lookup co' cacheA,
                                   Map.lookup co cacheC /= Map.lookup co' cacheC,

                                   Map.lookup co cacheA' /= Map.lookup co cacheC'
                               ]



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
  where seesDef :: Map Node (Map (Node, CachedObject) (MinAge, MaxAge))
        seesDef = (㎲⊒) (Map.fromList [ (y, Map.empty) | y <- nodes csGraphG ]) f
          where f sees =  (∐) [ Map.fromList [ (yM, (killedFor cacheSize e cache cache' $ transDefs cacheSize yN e cache cache' (sees ! yN)) ⊔ (defs yN (n, e, cache, cache'))) ]
                                      | (yN, (n, cache)) <- labNodes csGraphG, (yM, e) <- lsuc csGraphG yN, let Just (m, cache') = lab csGraphG yM]

        defs yN = defsFor cacheSize (const yN)


cacheDataDepGWork :: Graph gr => CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, CachedObject) IntSet
cacheDataDepGWork cacheSize csGraphG  = (∐) [ Map.fromList [ ((yM, co), IntSet.fromList [ yN ]) ] | (yM, deps) <- Map.assocs seesDef, ((yN, co), (MinAge minAge, MaxAge maxAge)) <- Map.assocs deps, maxAge >= cacheSize ]
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


cacheDataDepGWork2 :: Graph gr => CacheSize -> gr (Node, AbstractCacheState) CFGEdge -> Map (Node, CachedObject) IntSet
cacheDataDepGWork2 cacheSize csGraphG = reaches
  where defs yN = defsFor cacheSize (const yN)

        reaches :: Map (Node, CachedObject) IntSet
        reaches = foldr reachesFor Map.empty (labNodes csGraphG)

        succsM = Map.fromList [ (yN, [(e, yM, cache', minUsesOf e cache, maxUsesOf e cache, cacheDepsFast cacheSize e cache) | (yM, e) <- lsuc csGraphG yN, let Just (m, cache') = lab csGraphG yM]) | (yN, (n, cache)) <- labNodes csGraphG ]

        reachesFor :: (Node, (Node, AbstractCacheState)) -> Map (Node, CachedObject) IntSet -> Map (Node, CachedObject) IntSet
        reachesFor (yN, (n, cache)) reaches = foldr ins reaches (Map.assocs $ go2 reached reached)

          where reached = Map.fromList [ ((yM, co), minAge) | (yM, e) <- lsuc csGraphG yN, let Just (m, cache') = lab csGraphG yM, ((_, co), minAge) <- Map.assocs $ defs yN (n, e, cache, cache') ]

                ins ((yM, co), (MinAge minAge, MaxAge maxAge)) reaches
                    | maxAge >= cacheSize = Map.alter f (yM, co) reaches
                    | otherwise           =                      reaches
                  where f  Nothing   = Just $ IntSet.singleton yN
                        f (Just set) = Just $ IntSet.insert    yN set

                go2 :: Map (Node, CachedObject) (MinAge, MaxAge) -> Map (Node, CachedObject) (MinAge, MaxAge) -> Map (Node, CachedObject) (MinAge, MaxAge)
                go2 workset reached
                    | Map.null workset =                 reached
                    | otherwise        =  go2  workset0' reached'
                  where (((yN, co), minMax), workset0) = Map.deleteFindMin workset
                        (minAge, maxAge) = minMax
                        Just (n,cache) = lab csGraphG yN
                        succs = succsM ! yN

                        flow  = [ ((yM, co ), minMax'Joined) | (e, yM, cache', minUses, maxUses, _        ) <- succs,
                                                                               Just minMax' <- [newMinAge cacheSize cache cache' minUses maxUses (undefined, co) minMax],
                                                                               Just minMax'Joined <- isNew yM co minMax'
                              ]
                        trans = [ ((yM, co'), minMax'Joined) | (e, yM, cache', minUses, maxUses, cacheDeps) <- succs,
                                                                               Just cos <- [Map.lookup co cacheDeps ],
                                                                               (co', min, max) <- Set.toList cos,
                                                                               not $ (MinAge max) < minAge,
                                                                               not $ (MaxAge min) > maxAge,
                                                                               Just minMax' <- [newMinAge cacheSize cache cache' minUses maxUses (undefined, co') (MinAge min, MaxAge max)],
                                                                               Just minMax'Joined <- isNew yM co' minMax'
                              ]
                        reached'  = fold ins flow $ fold ins trans $ reached
                        workset0' = fold ins flow $ fold ins trans $ workset0

                        fold f xs y0 = foldr f y0 xs

                        ins (k, v) = Map.insertWith (⊔) k v

                        isNew yM co minMax'@(minAge', maxAge') = case Map.lookup (yM, co) reached of
                          Nothing       -> [Just minMax']
                          Just minMax'0@(minAge'0, maxAge'0) -> if minAge' < minAge'0 ∨ maxAge' > maxAge'0 then [Just $ minMax' ⊔ minMax'0 ] else []


cacheStateGraph'ForVarsAtMForGraph33 :: forall gr. (DynGraph gr) => Set CachedObject -> CsGraph AbstractCacheState CFGEdge ->  Node -> gr (Node, MergedMicroState AbstractCacheState AbstractCacheState) CFGEdge
cacheStateGraph'ForVarsAtMForGraph33 vars (css, es) mm = result
  where result = subgraph (rdfs [ m | (m, (m',_)) <- labNodes merged, m' == mm ] merged) merged

        merged :: gr (Node,  MergedMicroState AbstractCacheState AbstractCacheState) CFGEdge
        merged = mkGraph nodes' edges'

        nodes' = zip [0..] [           a                   | (m,σs)  <- IntMap.toList css,            c                  <- Set.toList σs,  let cs = (m,c), a <- α cs             ]
        edges' =           [(toNode' ! a, toNode' ! a', e) | (m,σes) <- IntMap.toList es,  m /= mm,  (c, e, cs'@(m',c')) <- Set.toList σes, let cs = (m,c), a <- α cs, a' <- α cs']
        toNode' = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes'

        α :: (Node, AbstractCacheState) -> [ (Node,  MergedMicroState AbstractCacheState AbstractCacheState) ]
        α cs@(n, cache)
            | n == mm ∧ (∀) vars (isConst cache) = [ (n, Merged   $ fmap (Set.map (       const 0 )) $ restrict cache vars) ]
            | n == mm                            = [ (n, Merged   $                                             cache     ) ]
            | otherwise = [ (n, Unmerged cache) ]

cacheStateGraph'ForVarsAtMForGraph3 :: forall gr. (DynGraph gr) => Set CachedObject -> CsGraph AbstractCacheState CFGEdge ->  Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraph'ForVarsAtMForGraph3 vars (css, es) mm = nmap strip result
  where result = cacheStateGraph'ForVarsAtMForGraph33 vars (css, es) mm
        strip (n, Unmerged cache) = (n, cache)
        strip (n, Merged   cache) = (n, cache)


allFromDataDepFor :: forall gr. DynGraph gr => MicroArchitecturalAbstraction AbstractCacheState AbstractCacheState CFGEdge -> ModsFor gr ->  CacheSize -> gr CFGNode CFGEdge -> Node -> (Map Node (Set Node), Costs, CsGraph AbstractCacheState CFGEdge)
allFromDataDepFor mu modsFor cacheSize graph n0 = result
  where result = (
          invert'' $ Map.fromList [ (m, slice) | m <- nodes graph, mayBeCSDependent m, let slice = Set.delete m $ cacheDataDepSlice modsFor cacheSize csGraph csGraphG ddeps m],
          edgeCosts,
          csGraph
         )
          
        (csd, edgeCosts, csGraph) = muMergeDirectOf mu graph n0 
        csGraphG = stateGraphForSets csGraph :: gr (Node, AbstractCacheState) CFGEdge
        
        mayBeCSDependent m = (∃) (lsuc graph m) (\(n,l) -> Set.size (edgeCosts ! (m,n,l)) > 1)

        ddeps = cacheDataDepGWork2 cacheSize csGraphG


allFromDataDepSimpleFor :: forall gr. DynGraph gr => MicroArchitecturalAbstraction AbstractCacheState AbstractCacheState CFGEdge -> ModsFor gr ->  CacheSize -> gr CFGNode CFGEdge -> Node -> (Map Node (Set Node), Costs, CsGraph AbstractCacheState CFGEdge)
allFromDataDepSimpleFor mu modsFor cacheSize graph n0 = result
  where result = (
          invert'' $ Map.fromList [ (m, slice) | m <- nodes graph, mayBeCSDependent m, let slice  = Set.delete m $ cacheDataDepSliceSimple modsFor cacheSize graph csGraph csGraphG ddeps m,
                                                                                       let slice' = Set.delete m $ cacheDataDepSlice       modsFor cacheSize       csGraph csGraphG ddeps m,
                                                                                       assert (slice == slice) True
                                  ],
          edgeCosts,
          csGraph
         )
          
        (csd, edgeCosts, csGraph) = muMergeDirectOf mu graph n0 
        csGraphG = stateGraphForSets csGraph :: gr (Node, AbstractCacheState) CFGEdge
        
        mayBeCSDependent m = (∃) (lsuc graph m) (\(n,l) -> Set.size (edgeCosts ! (m,n,l)) > 1)

        ddeps = cacheDataDepGWork2 cacheSize csGraphG



allFromDataDep :: forall gr. DynGraph gr =>  CacheSize -> gr CFGNode CFGEdge -> Node -> (Map Node (Set Node), Costs, CsGraph AbstractCacheState CFGEdge)
allFromDataDep       cacheSize graph n0 = result
  where none _ _ _ = Set.empty
        mu = cacheAbstraction       cacheSize
        result = allFromDataDepFor mu none        cacheSize graph n0

allFromDataDepJoined :: forall gr. DynGraph gr =>  CacheSize -> gr CFGNode CFGEdge -> Node -> (Map Node (Set Node), Costs, CsGraph AbstractCacheState CFGEdge)
allFromDataDepJoined cacheSize graph n0 = result
  where
        mu = cacheAbstractionJoined cacheSize
        result = allFromDataDepSimpleFor mu modsForFast cacheSize graph n0

csdFromDataDep :: DynGraph gr =>  CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdFromDataDep        cacheSize g n0 = first $ allFromDataDep       cacheSize g n0
  where first (x, _, _) = x

csdFromDataDepJoined :: DynGraph gr => CacheSize -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdFromDataDepJoined  cacheSize g n0 = first $ allFromDataDepJoined cacheSize g n0
  where first (x, _, _) = x

ageSetsJoin a b = AgeSets.cleanConsecutiveCache $ (Map.intersectionWith (∪) a b) `Map.union` (fmap (Set.insert infTime) a `Map.union` fmap (Set.insert infTime) b)
ageSetsLeq  a b = (∀) (Map.intersectionWith (⊆) a b) (== True)
                ∧ (∀) (Map.difference b a) (infTime ∈)
                ∧ (∀) (Map.difference a b) (== inf)



cacheDataDepSliceSimple :: forall gr. DynGraph gr => ModsFor gr -> CacheSize -> gr CFGNode CFGEdge -> CsGraph AbstractCacheState CFGEdge ->  gr (Node, AbstractCacheState) CFGEdge ->  Map (Node, CachedObject) (IntSet) -> Node -> Set Node
cacheDataDepSliceSimple modsFor cacheSize graph0 csGraph csGraphG ddeps m =
     assert ((List.sort nnodes) == (Set.toList $ Set.fromList $ nnodes))
   $ assert ((List.sort nnodes) == (List.sort $ nodes $ graph0))
   $ result
  where
        result = slice
        nnodes = [ n | (y, (n, _)) <- labNodes csGraphG ]

        yFor = Map.fromList [ (n, y)   | (y, (n, _ )) <- labNodes csGraphG ]
        nFor = Map.fromList [ (y, n)   | (y, (n, _ )) <- labNodes csGraphG ]

        graph = mkGraph [ (n, (n, cs)) | (y, (n, cs)) <- labNodes csGraphG ] (labEdges graph0) :: gr (CFGNode, AbstractCacheState) CFGEdge

        graph' = delSuccessorEdges (subgraph (rdfs [m] graph) graph) m

        edges = Set.fromList [ e | (_,e) <- lsuc graph m ]
        relevantCos = Set.fromList [ co | e <- Set.toList edges, co <- Set.toList $ CSD.cachedObjectsFor e]

        isinkdom' = isinkdomOfTwoFinger8 graph'
        df'       = idomToDFFast         graph' isinkdom'

        mods = (∐) [ modsFor cacheSize graph' co | co <- Set.toList relevantCos, not $ isConst cacheM co]

        Just (_, cacheM) = lab graph m

        viaDDep = Set.fromList [ n | co <- Set.toList relevantCos,
                                     not $ isConst cacheM co,
                                     let deps = Map.findWithDefault IntSet.empty (yFor ! m, co) ddeps,
                                     yN <- IntSet.toList $ deps, let n = nFor ! yN
                     ]

        slice =
                 ((go Set.empty                 viaDDep))
              ∪ ((go Set.empty                 mods) ∖ mods)
        go s workset
                    | Set.null workset =    s
                    | otherwise        = go s' (workset0 ∪ new)
                 where (y, workset0) = Set.deleteFindMin workset
                       s' =  Set.insert y s
                       new = fromDF ∖ s'
                       fromDF = Map.findWithDefault Set.empty y df'


cacheDataDepSlice :: DynGraph gr => ModsFor gr -> CacheSize -> CsGraph AbstractCacheState CFGEdge ->  gr (Node, AbstractCacheState) CFGEdge ->  Map (Node, CachedObject) (IntSet) -> Node -> Set Node
cacheDataDepSlice modsFor cacheSize csGraph csGraphG ddeps m =
      id
    $ result
  where result = Set.fromList [ n | y <- Set.toList slice, let Just (n,_) = lab csGraphG' y ]

        msCsGraph  = [ y | (y, (m_, _)) <- labNodes csGraphG , m_ == m ]
        msCsGraph' = [ y | (y, (m_, _)) <- labNodes csGraphG', m_ == m ]

        csGraphG' = cacheStateGraph'ForVarsAtMForGraph3 relevantCos csGraph m :: Gr (Node, AbstractCacheState) CFGEdge

        edges = Set.fromList [ e | y <- msCsGraph, (_,e) <- lsuc csGraphG y ]
        relevantCos = Set.fromList [ co | e <- Set.toList edges, co <- Set.toList $ CSD.cachedObjectsFor e]

        isinkdom' = isinkdomOfTwoFinger8 csGraphG'
        df'       = idomToDFFast         csGraphG' isinkdom'

{-
        phis = Set.fromList [ yN | (yN, yNNs) <- Map.assocs df, not $ Set.null yNNs,
                                         let Just (n, cache') = lab csGraphG' yN,
                                         let cache'0 = restrict cache' relevantCos,
                                         not $ (∀) (pre csGraphG' yN) (\yN0 ->
                                           let Just (_, cache) = lab csGraphG' yN0
                                               cache0 = restrict cache relevantCos
                                           in cache0 == cache'0
                                         )
                                    ]
           where 
                 df = invert'' $ isinkDFTwoFinger (grev csGraphG')
        phiPres = Set.fromList [ yN0 | yN <- Set.toList phis, yN0 <- pre csGraphG' yN ]
-}
        mods = (∐) [ modsFor cacheSize csGraphG' co | co <- Set.toList relevantCos, not $ (∀) msCsGraph (\y -> let Just (_, cacheM) = lab csGraphG y in isConst cacheM co) ]
         where csGraphG' = subgraph (rdfs msCsGraph csGraphG) csGraphG

        viaDDep = Set.fromList [ y' | (y', (n, cache)) <- labNodes csGraphG', (n,cache) ∈ ns ]
          where ns = Set.fromList [ (n, cacheN) | y <- msCsGraph, 
                                     co <- Set.toList relevantCos,
                                     let Just (m, cacheM) = lab csGraphG y,
                                     not $ isConst cacheM co,
                                     let deps = Map.findWithDefault IntSet.empty (y,co) ddeps,
                                     yN <- IntSet.toList $ deps, let Just (n, cacheN) = lab csGraphG yN
                     ]

        slice =
                   go Set.empty (Set.fromList msCsGraph')
              ∪ ((go Set.empty                 viaDDep))
           -- ∪ ((go Set.empty                 phiPres) ∖ phiPres)
              ∪ ((go Set.empty                 mods) ∖ mods)
        go s workset
                    | Set.null workset =    s
                    | otherwise        = go s' (workset0 ∪ new)
                 where (y, workset0) = Set.deleteFindMin workset
                       s' =  Set.insert y s
                       new = fromDF ∖ s'
                       fromDF = Map.findWithDefault Set.empty y df'



cacheAbstraction :: CacheSize -> MicroArchitecturalAbstraction AbstractCacheState AbstractCacheState CFGEdge
cacheAbstraction cacheSize = MicroArchitecturalAbstraction {
      muIsDependent = muIsDependent,
      muMerge = True,
      muGraph'For = muGraph'For,
      muInitialState = initialAbstractCacheState,
      muStepFor     = AgeSets.cacheOnlyStepFor cacheSize,
      muTimeStepFor = AgeSets.cacheTimeStepFor cacheSize,
      muToCFGEdge = id,
      muLeq = Nothing
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph33 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = CSD.cachedObjectsFor e, not $ Set.null vars] ]
        muIsDependent graph roots idom y n (Merged _) = undefined
        muIsDependent graph roots idom y n (Unmerged _) = IntMap.lookup y idom == Nothing

cacheAbstractionJoined :: CacheSize -> MicroArchitecturalAbstraction AbstractCacheState AbstractCacheState CFGEdge
cacheAbstractionJoined cacheSize = (cacheAbstraction cacheSize) { muLeq = Just $ JoinNode ageSetsJoin ageSetsLeq }

