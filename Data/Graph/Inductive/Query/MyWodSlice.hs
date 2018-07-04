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


myWodSlice graph m1 m2 = slice s0 ms0
  where s0  = (Set.empty, Map.empty)
        ms0 = Set.fromList [m1, m2]
        step = myWodSliceStep graph 
        slice s@(sliceNodes, ndoms) ms
          | Set.null ms = -- traceShow (length $ nodes graph, Set.size sliceNodes, Map.size ndoms ) $
                          sliceNodes
          | otherwise   = slice s' ms'
              where (m, ms0)  = Set.deleteFindMin ms
                    (new, s') = step s m
                    ms' = ms0 ∪ new 


myWodSliceStep :: DynGraph gr => gr a b ->  MyWodSliceState -> Node -> (Set Node, MyWodSliceState)
myWodSliceStep graph (ms, ndoms) m = if m ∈ ms then (Set.empty, (ms, ndoms)) else
    require ((∀) ms (\m -> (∀) unknownCond0 (\c -> (∀) (suc graph c) (\x -> (∃) (Map.assocs ndoms) (\(n, (pdom, dom)) ->   x ∈ dom ! m    ∨    m ∈ pdom ! x   ))))) $
    let covered      = (∀) unknownCond0 (\c -> c == m ∨  (∀) (suc graph c) (\x -> (∃) (Map.assocs ndoms) (\(n, (pdom, dom)) ->   x ∈ dom ! m    ∨    m ∈ pdom ! x   )))

        (unknownCondM2, wodM2, ndomsM2) = if covered then
              let wod    =    wod2 ∪    wodFromMust
                  notwod = notwod2 ∪ notwodFromMust
                  ((unknownCond1, wod1, notwod1), (must1, notmust1)) = foldr (fromPdomM2 m) ((unknownCond0, Set.empty, Set.empty), (Map.empty, Map.empty)) (Map.assocs ndoms)
                  ((unknownCond2, wod2, notwod2), (must2, notmust2)) = foldr (fromDomM2  m) ((unknownCond1, wod1,      notwod1),   (must1,     notmust1))  (Map.assocs ndoms)
                  wodFromMust    = Set.fromList [ c | c <- Set.toList unknownCond2,
                              (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> Map.member xl    must2  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m1 ∈    must2 ! xl  ∧  m1 ∈ notmust2 ! xr)))]
                  notwodFromMust = Set.fromList [ c | c <- Set.toList unknownCond2,
                              (∀) ms (\m1 -> (∀) (suc graph c) (\xl -> (Map.member xl    must2 ∧ (∀) (suc graph c) (\xr -> Map.member xr    must2  ∧  m1 ∈    must2 ! xl  ∧  m1 ∈    must2 ! xr))
                                                                      ∨ (Map.member xl notmust2 ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m1 ∈ notmust2 ! xl  ∧  m1 ∈ notmust2 ! xr))))]
              in
                 -- traceShow (wod1, must1, notmust1) $
                 -- traceShow (wod2, must2, notmust2) $ 
                 assert (unknownCond0 ⊇ unknownCond1  ∧  unknownCond1  ⊇ unknownCond2) $
                 assert (                                        wod1  ⊆         wod2) $
                 assert (                                     notwod1  ⊆      notwod2) $
                 assert (                                       must1  ⊑        must2) $
                 assert (                                    notmust1  ⊑     notmust2) $
                 (unknownCond2 ∖ (wod ∪ notwod), wod, ndoms)
            else
              let (wod, notwod)   = Set.partition (\c -> (∃) ms (\m1 -> (∃) (suc graph c) (\xl ->  m1 ∈ pdom ! xl)  ∧ (∃) (suc graph c) (\xr -> not $ m1 ∈ pdom ! xr))) unknownCond0
                  ndoms' = Map.insert m (pdom, dom) ndoms
                  (pdom, dom)  = ( sinkdomOfGfp $ delSuccessorEdges graph m, sinkdomOfGfp $ delSuccessorEdges (grev graph) m)
              in (unknownCond0 ∖ (wod ∪ notwod), wod, ndoms')

        (unknownCondM1, wodM1) =
              let unknownCond0' = unknownCond0 ∖ wodM2
                  wod    =    wod2 ∪    wodFromMust
                  notwod = notwod2 ∪ notwodFromMust
                  ((unknownCond1, wod1, notwod1), (must1, notmust1)) = foldr (fromPdomM1 m) ((unknownCond0', Set.empty, Set.empty), (Map.empty, Map.empty)) (Map.assocs ndomsM2)
                  ((unknownCond2, wod2, notwod2), (must2, notmust2)) = foldr (fromDomM1  m) ((unknownCond1,  wod1,      notwod1),   (must1,     notmust1))  (Map.assocs ndomsM2)
                  wodFromMust    = Set.fromList [ c | c <- Set.toList unknownCond2,
                              (∃) ms (\m2 -> (∃) (suc graph c) (\xl -> Map.member xl    must2  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m2 ∈    must2 ! xl  ∧  m2 ∈ notmust2 ! xr)))]
                  notwodFromMust = Set.fromList [ c | c <- Set.toList unknownCond2,
                              (∀) ms (\m2 -> (∀) (suc graph c) (\xl -> (Map.member xl    must2 ∧ (∀) (suc graph c) (\xr -> Map.member xr    must2  ∧  m2 ∈    must2 ! xl  ∧  m2 ∈    must2 ! xr))
                                                                      ∨ (Map.member xl notmust2 ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust2  ∧  m2 ∈ notmust2 ! xl  ∧  m2 ∈ notmust2 ! xr))))]
              in
                 -- traceShow (wod1, must1, notmust1) $
                 -- traceShow (wod2, must2, notmust2) $ 
                 assert (unknownCond0' ⊇ unknownCond1  ∧  unknownCond1  ⊇ unknownCond2) $
                 assert (                                         wod1  ⊆         wod2) $
                 assert (                                      notwod1  ⊆      notwod2) $
                 assert (                                        must1  ⊑        must2) $
                 assert (                                     notmust1  ⊑     notmust2) $
                 (unknownCond2 ∖ (wod ∪ notwod), wod)

    in
       -- traceShow ((ms, ndoms), m, unknownCond0) $ 
       -- traceShow (wod1,  notwod1, unknownCond1) $ 
       -- traceShow ("1", must1, notmust1) $ 
       -- traceShow (wod2, notwod2, unknownCond2) $ 
       -- traceShow ("2", must2, notmust2) $ 
       -- traceShow (wod        , notwod        ) $ 
       -- traceShow (wodFromMust, notwodFromMust) $ 
       -- traceShow (covered                    ) $
       -- traceShow ("m2", m, unknownCondM2, wodM2) $
       -- traceShow ("m1", m, unknownCondM1, wodM1) $
       (Set.delete m $ wodM2 ∪ wodM1, (Set.insert m ms, ndomsM2))
  where condNodes    = Set.fromList [ c | c <- nodes graph, length (suc graph c) > 1, not $ c ∈ ms, c /= m ]
        unknownCond0 = Set.filter  (\c -> (not $ c ∈ ms) ∧ (c /= m)) condNodes
        fromDomM2 m2 (n,(_,dom)) ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                                  (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                            not $ (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms, m1 ∈ dom ! m2,       x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c, x ∈ dom ! m2]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms, m1 ∈ dom ! m2, not $ x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c, x ∈ dom ! m2]
        fromDomM1 m1 (n,(_,dom)) ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  m2 <- Set.toList ms,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                                  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) )]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  m2 <- Set.toList ms,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                            not $ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) )]
                mustNew      = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList ms, x ∈ dom ! m2, m1 ∈ dom ! m2,       x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList ms, x ∈ dom ! m2, m1 ∈ dom ! m2, not $ x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c]
        fromPdomM2 m2 (n,(pdom,_)) ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                                  (∃) ms (\m1 -> (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)  ∧   (not $ m1 ∈ pdom ! xr))))
                               ]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                            not $ (∃) ms (\m1 -> (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m2 ∈ pdom ! xr))))
                               ]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList $ pdom ! x, not $ m1 ∈ pdom ! m2, m1 ∈ ms ])  | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]
                notmustNew   = Map.fromList [ (x, notmusts)                                                                           | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]
                  where notmusts = pdom ! m2  ∩  ms
        fromPdomM1 m1  (n,(pdom,_)) ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  m2 <- Set.toList ms,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                                  (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)  ∧   (not $ m1 ∈ pdom ! xr)))
                               ]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  m2 <- Set.toList ms,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                            not $ (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m2 ∈ pdom ! xr)))
                               ]
                mustNew      = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList $ pdom ! m1, m2 ∈ ms          ])  | c <- Set.toList unknownCond', x <- suc graph c,       m1 ∈ pdom ! x]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList $ pdom !  x, m2 ∈ ms          ])  | c <- Set.toList unknownCond', x <- suc graph c, not $ m1 ∈ pdom ! x ]
