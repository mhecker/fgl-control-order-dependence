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

import Util(the, invert', invert'', foldM1, reachableFrom, treeDfs, toSet, fromSet, isReachableFromTree, isReachableBeforeFromTree, allReachableFromTree, findMs, findNoMs, findBoth)
import Unicode



import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic hiding (postorder)
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.NTICD
import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs)

import Debug.Trace
import Control.Exception.Base (assert)



type MyWodSliceState = (Set Node, (Map Node ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)))))

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
          | Set.null ms = -- traceShow ( (-1) + ceiling ( (100 * fromIntegral (Map.size ndoms) / fromIntegral (Set.size sliceNodes) :: Double)), Set.size sliceNodes, Map.size ndoms, length $ nodes graph ) $
                          sliceNodes
          | otherwise   = -- traceShow (sliceNodes, Map.keys ndoms) $
                          slice s' ms'
              where (m, ms0)  = Set.deleteFindMin ms
                    (new, s') = step s m
                    ms' = ms0 ∪ new 


myWodSliceStep :: forall gr a b. (Show (gr a b), DynGraph gr) => gr a b ->  MyWodSliceState -> Node -> (Set Node, MyWodSliceState)
myWodSliceStep graph (ms, ndoms) m = if m ∈ ms then (Set.empty, (ms, ndoms)) else
    require ((∀) ms (\m -> (∀) unknownCond0 (\c ->           (∀) (suc graph c) (\x -> (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->   x ∈ dom ! m  ∨  m ∈ pdom ! x  ∨  (not $ m ∈ pmay ! x) ))) )) $
    let covered           = (∀) unknownCond0 (\c -> c == m ∨ (∀) (suc graph c) (\x -> (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->   x ∈ dom ! m  ∨  m ∈ pdom ! x   ∨  (not $ m ∈ pmay ! x ))) )

        (unknownCondM2, wodM2, ndomsM2) = if covered then
              let wod    =    wod3 ∪    wodFromMust
                  notwod = notwod3 ∪ notwodFromMust
                  ((unknownCond1, wod1, notwod1), (must1, notmust1)) = foldr (fromPdomM2  m) ((unknownCond0, Set.empty, Set.empty), (Map.empty, Map.empty)) (Map.assocs ndoms)
                  ((unknownCond2, wod2, notwod2), (must2, notmust2)) = foldr (fromDomM2   m) ((unknownCond1, wod1,      notwod1),   (must1,     notmust1))  (Map.assocs ndoms)
                  ((unknownCond3, wod3, notwod3), (must3, notmust3)) = foldr (fromPmayM2  m) ((unknownCond2, wod2,      notwod2),   (must2,     notmust2))  (Map.assocs ndoms)
                  wodFromMust    = Set.fromList [ c | c <- Set.toList unknownCond3,
                              (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> Map.member xl    must3  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust3  ∧  m1 ∈    must3 ! xl  ∧  m1 ∈ notmust3 ! xr)))]
                  notwodFromMust = Set.fromList [ c | c <- Set.toList unknownCond3,
                              (∀) ms (\m1 -> (∀) (suc graph c) (\xl -> (Map.member xl    must3 ∧ (∀) (suc graph c) (\xr -> Map.member xr    must3  ∧  m1 ∈    must3 ! xl  ∧  m1 ∈    must3 ! xr))
                                                                      ∨ (Map.member xl notmust3 ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust3  ∧  m1 ∈ notmust3 ! xl  ∧  m1 ∈ notmust3 ! xr))))]
              in
                 -- traceShow (wod1, must1, notmust1) $
                 -- traceShow (wod2, must2, notmust2) $ 
                 assert (unknownCond0 ⊇ unknownCond1  ∧  unknownCond1 ⊇ unknownCond2  ∧  unknownCond2 ⊇ unknownCond3) $
                 assert (                                        wod1 ⊆         wod2  ∧          wod2 ⊆    wod3) $
                 assert (                                     notwod1 ⊆      notwod2  ∧       notwod2 ⊆ notwod3) $
                 assert (                                       must1 ⊑        must2  ∧         must2 ⊑    must3) $
                 assert (                                    notmust1 ⊑     notmust2  ∧      notmust2 ⊑ notmust3) $
                 (unknownCond2 ∖ (wod ∪ notwod), wod, ndoms)
            else
              let (wod, notwod)   = Set.partition (\c -> (∃) ms (\m1 -> (∃) (suc graph c) (\xl ->  m1 ∈ pdom ! xl)  ∧ (∃) (suc graph c) (\xr -> not $ m1 ∈ pdom ! xr))) unknownCond0
                  ndoms' = Map.insert m ((pdom, dom, pmay), (ipdom, idom, ipmay)) ndoms
                  ( pdom,  dom,  pmay)  = ( sinkdomOfGfp         $ delSuccessorEdges graph m, sinkdomOfGfp         $ delSuccessorEdges (grev graph) m,                           mayNaiveGfp $ delSuccessorEdges graph m)
                  (ipdom, idom, ipmay)  = ( isinkdomOfTwoFinger8 $ delSuccessorEdges graph m, isinkdomOfTwoFinger8 $ delSuccessorEdges (grev graph) m, toSuccMap (immediateOf $ mayNaiveGfp $ delSuccessorEdges graph m :: gr ()()))
              in (unknownCond0 ∖ (wod ∪ notwod), wod, ndoms')

        (unknownCondM1, wodM1) =
              let unknownCond0' = unknownCond0 ∖ wodM2
                  wod    =    wod3 ∪    wodFromMust
                  notwod = notwod3 ∪ notwodFromMust
                  ((unknownCond1, wod1, notwod1), (must1, notmust1)) = foldr (fromPdomM1 m) ((unknownCond0', Set.empty, Set.empty), (Map.empty, Map.empty)) (Map.assocs ndomsM2)
                  ((unknownCond2, wod2, notwod2), (must2, notmust2)) = foldr (fromDomM1  m) ((unknownCond1,  wod1,      notwod1),   (must1,     notmust1))  (Map.assocs ndomsM2)
                  ((unknownCond3, wod3, notwod3), (must3, notmust3)) = foldr (fromPmayM1 m) ((unknownCond2,  wod2,      notwod2),   (must2,     notmust2))  (Map.assocs ndomsM2)
                  wodFromMust    = Set.fromList [ c | c <- Set.toList unknownCond3,
                              (∃) ms (\m2 -> (∃) (suc graph c) (\xl -> Map.member xl    must3  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust3  ∧  m2 ∈    must3 ! xl  ∧  m2 ∈ notmust3 ! xr)))]
                  notwodFromMust = Set.fromList [ c | c <- Set.toList unknownCond3,
                              (∀) ms (\m2 -> (∀) (suc graph c) (\xl -> (Map.member xl    must3 ∧ (∀) (suc graph c) (\xr -> Map.member xr    must3  ∧  m2 ∈    must3 ! xl  ∧  m2 ∈    must3 ! xr))
                                                                      ∨ (Map.member xl notmust3 ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust3  ∧  m2 ∈ notmust3 ! xl  ∧  m2 ∈ notmust3 ! xr))))]
              in
                 assert (unknownCond0' ⊇ unknownCond1  ∧  unknownCond1 ⊇ unknownCond2  ∧  unknownCond2 ⊇ unknownCond3) $
                 assert (                                         wod1 ⊆         wod2  ∧          wod2 ⊆    wod3) $
                 assert (                                      notwod1 ⊆      notwod2  ∧       notwod2 ⊆ notwod3) $
                 assert (                                        must1 ⊑        must2  ∧         must2 ⊑    must3) $
                 assert (                                     notmust1 ⊑     notmust2  ∧      notmust2 ⊑ notmust3) $
                 (unknownCond3 ∖ (wod ∪ notwod), wod)

    in
       (Set.delete m $ wodM2 ∪ wodM1, (Set.insert m ms, ndomsM2))
  where condNodes    = Set.fromList [ c | c <- nodes graph, length (suc graph c) > 1, not $ c ∈ ms, c /= m ]
        unknownCond0 = Set.filter  (\c -> (not $ c ∈ ms) ∧ (c /= m)) condNodes
        fromDomM2 m2 (n,((_,dom,_),(_,idom,_))) ((unknownCond, wod, notwod), (must, notmust))  =
                   (if wodNew == wodNewFast then id else traceShow (graph, m2, ms, idom, ".....", wodNew, "--------", wodNewFast)) $ 
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
                   -- assert (   mustNew ==    mustNewFast ) $
                   -- assert (notmustNew == notmustNewFast ) $
                   ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                                  (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                            not $ (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms, m1 ∈ dom ! m2,       x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c, x ∈ dom ! m2]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms, m1 ∈ dom ! m2, not $ x ∈ dom ! m1])  | c <- Set.toList unknownCond', x <- suc graph c, x ∈ dom ! m2]

                allReachableIDomFrom = allReachableFromTree idom
                isReachableIDomFrom = isReachableFromTree idom
                isReachableIDomBefore = isReachableBeforeFromTree idom
                cWithM1s = [ (c, findBoth idom ms (Set.fromList $ suc graph c) m2) | c <- Set.toList unknownCond ]
                wodNewFast    = Set.fromList [ c | (c,(foundMs,_        )) <- cWithM1s, foundMs   ]
                notwodNewFast = Set.fromList [ c | (c,(_      ,foundNoMs)) <- cWithM1s, foundNoMs ]

        fromDomM1 m1 (n,((_,dom,_),_)) ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
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
        fromPdomM2 m2 (n,((pdom,_,_),(ipdom,_,_))) ((unknownCond, wod, notwod), (must, notmust))  =
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
                   assert (   mustNew ==    mustNewFast ) $
                   assert (notmustNew == notmustNewFast ) $
                   ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                                  (∃) ms (\m1 -> (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)  ∧   (not $ m1 ∈ pdom ! xr))))
                               ]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                            not $ (∃) ms (\m1 -> (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m1 ∈ pdom ! xr))))
                               ]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms,       m1 ∈ pdom ! x ∧ m2 ∈ pdom ! m1]) | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList ms, not $ m1 ∈ pdom ! x ∧ m2 ∈ pdom ! m1]) | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]

                isReachableIPDomFrom = isReachableFromTree ipdom
                isReachableIPDomBefore = isReachableBeforeFromTree ipdom
                withJoin     = [ (c,z,relevant) | c <- Set.toList unknownCond, let (z,relevant) = lcaRKnown ipdom c (suc graph c) ]
                wodNewFast   = Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  m2 `isReachableIPDomFrom` z,
                                                  (∃) ms (\m1 -> (m1 ∈ relevant)  ∧  (m1 /= z))
                               ]
                notwodNewFast= Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  m2 `isReachableIPDomFrom` z,
                                            not $ (∃) ms (\m1 -> (m1 ∈ relevant)  ∧  (m1 /= z))
                               ]
                mustNewFast     = Map.fromList [ (x, Set.fromList [ m1 | m1 <- Set.toList ms, isReachableIPDomBefore m1 m2 x ]) | c <- Set.toList unknownCond', x <- suc graph c, m2 `isReachableIPDomFrom` x]
                notmustNewFast  = Map.fromList [ (x, Set.fromList [ m1 | m1 <- Set.toList ms, isReachableIPDomBefore m2 m1 x ]) | c <- Set.toList unknownCond', x <- suc graph c, m2 `isReachableIPDomFrom` x]



        fromPdomM1 m1  (n,((pdom,_,_),(ipdom,_,_))) ((unknownCond, wod, notwod), (must, notmust))  =
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
                   assert (   mustNew ==    mustNewFast ) $
                   assert (notmustNew == notmustNewFast ) $
                   ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∃) ms (\m2 -> 
                                                    (∀) (suc graph c) (\x -> m2 ∈ pdom ! x) ∧
                                                    (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)  ∧   (not $ m1 ∈ pdom ! xr)))
                                                  )
                               ]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) ms (\m2 -> 
                                                    ((∀) (suc graph c) (\x -> m2 ∈ pdom ! x)) ∧
                                             (not $ (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m1 ∈ pdom ! xr))))
                                                  )
                               ]
                mustNew      = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList $ pdom ! m1, m2 ∈ ms          ])  | c <- Set.toList unknownCond', x <- suc graph c,       m1 ∈ pdom ! x]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList $ pdom !  x, m2 ∈ ms, (not $ m1 ∈ pdom ! x)  ∨  (not $ m2 ∈ pdom ! m1)       ])  | c <- Set.toList unknownCond', x <- suc graph c ]

                isReachableIPDomFrom = isReachableFromTree ipdom
                isReachableIPDomBefore = isReachableBeforeFromTree ipdom
                withJoin     = [ (c,z,relevant) | c <- Set.toList unknownCond, let (z,relevant) = lcaRKnown ipdom c (suc graph c) ]
                wodNewFast   = Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  (m1 ∈ relevant)  ∧  (m1 /= z),
                                                  (∃) ms (\m2 -> m2 `isReachableIPDomFrom` m1)
                               ]
                notwodNewFast= Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  (m1 == z)  ∨  (not $ m1 ∈ relevant),
                                                  (∀) ms (\m2 -> m2 `isReachableIPDomFrom` z)
                               ]
                mustNewFast     = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList ms,       m2 `isReachableIPDomFrom` m1]) | c <- Set.toList unknownCond', x <- suc graph c, m1 `isReachableIPDomFrom` x]
                notmustNewFast  = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList ms, isReachableIPDomBefore m2 m1 x ])    | c <- Set.toList unknownCond', x <- suc graph c]

        fromPmayM2 m2 (n,((pdom, dom, pmay),_)) ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  not $ m2 ∈ pmay ! c,
                                                  (∃) ms (\m1 -> (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl )   ∧  (not $ m1 ∈ pdom ! xr))))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  not $ m2 ∈ pmay ! c,
                                            not $ (∃) ms (\m1 -> (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl )   ∧  (not $ m1 ∈ pdom ! xr))))]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 | m1 <- Set.toList ms,       m1 ∈ pdom ! x  ∨       m1 ∈ dom ! m2])  | c <- Set.toList unknownCond', x <- suc graph c, not $ m2 ∈ pmay ! x]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m1 | m1 <- Set.toList ms, not $ m1 ∈ pdom ! x,   not $ m1 ∈ dom ! m2])  | c <- Set.toList unknownCond', x <- suc graph c, not $ m2 ∈ pmay ! x]
        fromPmayM1 m1 (n,((pdom, dom, pmay),_)) ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  m2 <- Set.toList ms,
                                                  not $ m2 ∈ pmay ! c,
                                                  (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m1 ∈ pdom ! xr )))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  m2 <- Set.toList ms,
                                                  not $ m2 ∈ pmay ! c,
                                            not $ (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m1 ∈ pdom ! xr )))]
                mustNew      = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList ms, not $ m2 ∈ pmay ! x,       m1 ∈ pdom ! x  ∨       m1 ∈ dom ! m2])  | c <- Set.toList unknownCond', x <- suc graph c]
                notmustNew   = Map.fromList [ (x, Set.fromList [ m2 | m2 <- Set.toList ms, not $ m2 ∈ pmay ! x, not $ m1 ∈ pdom ! x,   not $ m1 ∈ dom ! m2])  | c <- Set.toList unknownCond', x <- suc graph c]




lcaRKnown :: Map Node (Set Node) -> Node -> [Node] -> (Node, Set Node)
lcaRKnown dom c successors = case Set.toList $ dom ! c of
                     []  -> assert (successors == []) $
                                (c, Set.fromList [c])
                     [z] -> assert (successors /= []) $ 
                                (z, foldr relevant (Set.fromList successors) successors)
                       where relevant :: Node -> Set Node -> Set Node
                             relevant n ns
                               | n == z = ns
                               | otherwise = relevant n' (Set.insert n' ns)
                                   where [n'] = Set.toList $ dom ! n
                     _   -> error "no tree"
