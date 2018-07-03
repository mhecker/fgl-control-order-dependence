{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert
module Data.Graph.Inductive.Query.MyWodSlice where

import Data.Ord (comparing)
import Data.Maybe(fromJust)
import Control.Monad (liftM, foldM, forM, forM_)

import Control.Monad.ST
import Data.STRef

import Data.Functor.Identity (runIdentity)
import qualified Control.Monad.Logic as Logic
import Data.List(foldl', intersect,foldr1, partition)

import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)

import Util(the, invert', invert'', foldM1, reachableFrom, treeDfs, toSet, fromSet)
import Unicode



import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic hiding (postorder)
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.NTICD
import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs)

import Debug.Trace
import Control.Exception.Base (assert)



type MyWodSliceState = (Set Node, Map Node (Map Node (Set Node), Map Node (Set Node)))

myWodFromSliceStep graph m1 m2 =
    assert (Set.null new1) $
    assert (fst s1 == Set.fromList [m1]) $
    assert (fst s2 == Set.fromList [m1, m2]) $
    -- traceShow (Map.keys $ snd s2) $ 
    new2
  where s0 = (Set.empty, Map.empty)
        (new1, s1) = myWodSliceStep graph s0 m1
        (new2, s2) = myWodSliceStep graph s1 m2


-- myWodSlice graph m1 m2 = forM (Set.toList ms) (\m -> do
--     s <- get
--     (new
--     assert (Set.null new1) $
--     assert (fst s1 == Set.fromList [m1]) $
--     assert (fst s2 == Set.fromList [m1, m2]) $
--     traceShow (Map.keys $ snd s2) $ 
--     new2
--   where s0 = (Set.empty, Map.empty)
--         (new1, s1) = myWodSliceStep graph s0 m1
--         (new2, s2) = myWodSliceStep graph s1 m2

myWodSliceStep :: DynGraph gr => gr a b ->  MyWodSliceState -> Node -> (Set Node, MyWodSliceState)
myWodSliceStep graph (ms, ndoms) m = if m ∈ ms then (Set.empty, (ms, ndoms)) else
    require ((∀) ms (\m -> (∀) unknownCond0 (\c -> (∀) (suc graph c) (\x -> (∃) (Map.assocs ndoms) (\(n, (pdom, dom)) ->   x ∈ dom ! m    ∨    m ∈ pdom ! x   ))))) $
    let ((unknownCond1, wod1, notwod1), (must1, notmust1)) = foldr (fromPdomM2 m) ((unknownCond0, Set.empty, Set.empty), (Map.empty, Map.empty)) (Map.keys ndoms)
        -- wod1FromMust    = Set.fromList [ c | c <- Set.toList unknownCond1pre,
        --                       (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> Map.member xl    must1  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust1  ∧  m ∈    must1 ! xl  ∧  m ∈ notmust1 ! xr)))]
        -- notwod1FromMust = Set.fromList [ c | c <- Set.toList unknownCond1pre,
        --                       (∀) ms (\m1 -> (∀) (suc graph c) (\xl -> (Map.member xl    must1 ∧ (∀) (suc graph c) (\xr -> Map.member xr    must1  ∧  m ∈    must1 ! xl  ∧  m ∈    must1 ! xr))
        --                                                               ∨ (Map.member  xl notmust1 ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust1  ∧  m ∈ notmust1 ! xl  ∧  m ∈ notmust1 ! xr))))]
        -- wod1           = (   wod1pre ∪    wod1FromMust)
        -- notwod1        = (notwod1pre ∪ notwod1FromMust)
        -- unknownCond1   = unknownCond1pre ∖ (wod1 ∪ notwod1)

        ((unknownCond2, wod2, notwod2), (must2, notmust2)) = foldr (fromDomM2 m) ((unknownCond1, wod1, notwod1), (must1, notmust1)) (Map.keys ndoms)
        -- wod2FromMust    = Set.fromList [ c | c <- Set.toList unknownCond2pre,
        --                       (∃) ms (\m2 -> (∃) (suc graph c) (\xl -> Map.member xl    must2  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m ∈    must2 ! xl  ∧  m ∈ notmust2 ! xr)))]
        -- notwod2FromMust = Set.fromList [ c | c <- Set.toList unknownCond2pre,
        --                       (∀) ms (\m2 -> (∀) (suc graph c) (\xl -> (Map.member xl    must2 ∧ (∀) (suc graph c) (\xr -> Map.member xr    must2  ∧  m ∈    must2 ! xl  ∧  m ∈    must2 ! xr))
        --                                                               ∨ (Map.member xl notmust2 ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m ∈ notmust2 ! xl  ∧  m ∈ notmust2 ! xr))))]
        -- wod2           = (   wod2pre ∪    wod2FromMust)
        -- notwod2        = (notwod2pre ∪ notwod2FromMust)
        -- unknownCond2   = unknownCond2pre ∖ (wod2 ∪ notwod2)



        
        wodFromMust    = Set.fromList [ c | c <- Set.toList unknownCond2,
                              (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> Map.member xl    must2  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m1 ∈    must2 ! xl  ∧  m1 ∈ notmust2 ! xr)))]
        notwodFromMust = Set.fromList [ c | c <- Set.toList unknownCond2,
                              (∀) ms (\m1 -> (∀) (suc graph c) (\xl -> (Map.member xl    must2 ∧ (∀) (suc graph c) (\xr -> Map.member xr    must2  ∧  m1 ∈    must2 ! xl  ∧  m1 ∈    must2 ! xr))
                                                                      ∨ (Map.member xl notmust2 ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m1 ∈ notmust2 ! xl  ∧  m1 ∈ notmust2 ! xr))))]
        wod           = (   wod2 ∪    wodFromMust)
        notwod        = (notwod2 ∪ notwodFromMust)
        unknownCond   = unknownCond2 ∖ (wod2 ∪ notwod2)
        
        (newWods, ndoms') = if covered then
           (wod,
            ndoms
           )
         else
           let (pdom, dom)  = ( sinkdomOfGfp $ delSuccessorEdges graph m, sinkdomOfGfp $ delSuccessorEdges (grev graph) m)
           in (Set.fromList [ c | c <- Set.toList unknownCond0, (∃) ms (\m1 -> (∃) (suc graph c) (\xl ->  m1 ∈ pdom ! xl)  ∧ (∃) (suc graph c) (\xr -> not $ m1 ∈ pdom ! xr)) ],
               Map.insert m (pdom, dom) ndoms
              )

    in
       -- traceShow ((ms, ndoms), m, unknownCond0) $ 
       -- traceShow (wod1,  notwod1, unknownCond1) $ 
       -- traceShow ("1", must1, notmust1) $ 
       -- traceShow (wod2, notwod2, unknownCond2) $ 
       -- traceShow ("2", must2, notmust2) $ 
       -- traceShow (wod        , notwod        ) $ 
       -- traceShow (wodFromMust, notwodFromMust) $ 
       -- traceShow (covered                    ) $ 
       assert (unknownCond0 ⊇ unknownCond1  ∧  unknownCond1  ⊇ unknownCond2) $
       assert (                                        wod1  ⊆         wod2) $
       assert (                                     notwod1  ⊆      notwod2) $
       assert (                                       must1  ⊑        must2) $
       assert (                                    notmust1  ⊑     notmust2) $
       (Set.delete m $ newWods, (Set.insert m ms, ndoms'))
  where condNodes    = Set.fromList [ c | c <- nodes graph, length (suc graph c) > 1, not $ c ∈ ms, c /= m ]
        unknownCond0 = Set.filter  (\c -> (not $ c ∈ ms) ∧ (c /= m)) condNodes
        covered      = (∀) unknownCond0 (\c -> c == m ∨  (∀) (suc graph c) (\x -> (∃) (Map.assocs ndoms) (\(n, (pdom, dom)) ->   x ∈ dom ! m    ∨    m ∈ pdom ! x   )))
        fromDomM2 m2 n ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where (_, dom) = ndoms ! n 
                unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                                  (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                            not $ (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms, m1 ∈ dom ! m2,       x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c, x ∈ dom ! m2]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms, m1 ∈ dom ! m2, not $ x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c, x ∈ dom ! m2]
        fromPdomM2 m2 n ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where (pdom, _) = ndoms ! n 
                unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond, (∀) (suc graph c) (\x -> m2 ∈ pdom ! x), (∃) ms (\m1 -> not $ m1 ∈ (∏) [ pdom ! x |  x <- suc graph c ]) ]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond, (∀) (suc graph c) (\x -> m2 ∈ pdom ! x), (∀) ms (\m1 ->       m1 ∈ (∏) [ pdom ! x |  x <- suc graph c ]) ]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList $ pdom ! x, not $ m1 ∈ pdom ! m2, m1 ∈ ms ])  | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]
                notmustNew   = Map.fromList [ (x, notmusts)                                                                           | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]
                  where notmusts = pdom ! m2  ∩  ms
        -- fromPdomM1 m1 n ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
        --   where (pdom, _) = ndoms ! n 
        --         unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
        --         wodNew       = Set.fromList [ c | c <- Set.toList unknownCond, m2 <- Set.toList ms, (∀) (suc graph c) (\x -> m2 ∈ pdom ! x), not $ m1 ∈ (∏) [ pdom ! x |  x <- suc graph c ] ]
        --         notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond, m2 <- Set.toList ms, (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),       m1 ∈ (∏) [ pdom ! x |  x <- suc graph c ] ]
        --         mustNew      = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList $ pdom ! m1, m2 ∈ ms          ])  | c <- Set.toList unknownCond', x <- suc graph c,       m1 ∈ pdom ! x]
        --         notmustNew   = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList $ pdom !  x, m2 ∈ ms          ])  | c <- Set.toList unknownCond', x <- suc graph c, not $ m1 ∈ pdom ! x ]
