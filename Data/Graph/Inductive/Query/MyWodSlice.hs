{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE StandaloneDeriving #-}
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

import qualified Data.Sequence as Seq
import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive.Query.DFS (reachable)
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)

import Util(restrict, without, the, invert', invert'', foldM1, reachableFrom, treeDfs, toSet, fromSet, isReachableFromTree, isReachableFromTreeM, isReachableBeforeFromTreeM, allReachableFromTreeM, findMs, findNoMs, findBoth, reachableFromTree)
import Unicode



import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic hiding (postorder)
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs)

import Data.Graph.Inductive.Query.NTICD
import Data.Graph.Inductive.Query.LCA


import Debug.Trace
import Control.Exception.Base (assert)



type MyWodSliceState = (Set Node, (Map Node ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Maybe Node), Map Node (Maybe Node)))))

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
    require (assertionsDisabled ∨  
      ((∀) ms (\m -> (∀) unknownCond0 (\c ->          (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->
            (∀) (suc graph c) (\x ->       x ∈ dom  ! m)
          ∨ (∀) (suc graph c) (\x ->       m ∈ pdom ! x)
          ∨ (∀) (suc graph c) (\x -> not $ m ∈ pmay ! x)
      ))))) $
    let covered    = (∀) unknownCond0 (\c -> c == m ∨ 
            (∃) (Map.assocs ndoms) (\(n, (_,(ipdom, _   ))) -> let Just z = ipdom ! c in isReachableFromTreeM ipdom m z)
          ∨ (∃) (Map.assocs ndoms) (\(n, (_,(_,     idom))) -> (∀) (suc graph c) (\x ->  isReachableFromTreeM idom  x m))
          ∨ (∃) (Map.assocs ndoms) (\(n, _                ) -> (n /= m) ∧ (n /= c) ∧ (not $ m `elem` reachable c (delSuccessorEdges graph n)))
          )
        coveredPDom = Set.filter (\c ->  (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->       (∀) (suc graph c) (\x ->        m ∈ pdom ! x ))) unknownCond0
        coveredDom  = Set.filter (\c ->  (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->       (∀) (suc graph c) (\x ->        x ∈  dom ! m ))) unknownCond0
        coveredPMay = Set.filter (\c ->  (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->       (∀) (suc graph c) (\x ->  not $ m ∈ pmay ! x ))) unknownCond0

        (unknownCondM2, wodM2, ndomsM2) = if covered then
              let wod    =    wod3
                  notwod = notwod3
                  (unknownCond1, wod1, notwod1) = foldr (fromPdomM2  m) (unknownCond0, Set.empty, Set.empty) (Map.assocs ndoms)
                  (unknownCond2, wod2, notwod2) = foldr (fromDomM2   m) (unknownCond1, wod1,      notwod1  ) (Map.assocs ndoms)
                  (unknownCond3, wod3, notwod3) = foldr (fromPmayM2  m) (unknownCond2, wod2,      notwod2  ) (Map.assocs ndoms)
              in
                 -- traceShow ("M2 1", (unknownCond1, wod1, notwod1)) $ 
                 -- traceShow ("M2 2", (unknownCond2, wod2, notwod2)) $ 
                 -- traceShow ("M2 3", (unknownCond3, wod3, notwod3)) $ 
                 assert ( assertionsDisabled ∨  unknownCond0 ⊇ unknownCond1  ∧  unknownCond1 ⊇ unknownCond2  ∧  unknownCond2 ⊇ unknownCond3) $
                 assert ( assertionsDisabled ∨                                          wod1 ⊆         wod2  ∧          wod2 ⊆    wod3) $
                 assert ( assertionsDisabled ∨                                       notwod1 ⊆      notwod2  ∧       notwod2 ⊆ notwod3) $
                 (unknownCond2 ∖ (wod ∪ notwod), wod, ndoms)
            else
              let (wod, notwod)        = Set.partition (\c -> (∃) ms (\m1 -> (∃) (suc graph c) (\xl ->  m1 ∈ pdom ! xl)  ∧ (∃) (suc graph c) (\xr -> not $ m1 ∈ pdom ! xr))) unknownCond0
                  (wodFast,notwodFast) = Set.partition (\c ->  let (z, relevant) = lcaRKnownM ipdom c (suc graph c) in (∃) ms (\m1 -> m1 /= z ∧ m1 ∈ relevant))               unknownCond0
                  ndoms' = Map.insert m ((pdom, dom, pmay), (ipdom, idom)) ndoms
                  ( pdom,  dom,  pmay)  = ( sinkdomOfGfp         $ delSuccessorEdges       graph  m,
                                            sinkdomOfGfp         $ delSuccessorEdges (grev graph) m,
                                            mayNaiveGfp $ delSuccessorEdges graph m
                                          )
                  (ipdom, idom       )  = ( fromIdom m $ iDom (grev $ delSuccessorEdges   graph m) m,
                                            fromIdom m $ iDom (       delPredecessorEdges graph m) m
                                          )
                    where fromIdom m idom = Map.insert m Nothing $ Map.fromList [ (n, Just m) | (n,m) <- idom ]
              in
                 assert ( assertionsDisabled ∨    wod ==    wodFast) $
                 assert ( assertionsDisabled ∨ notwod == notwodFast) $
                 (unknownCond0 ∖ (wodFast ∪ notwodFast), wodFast, ndoms')

        (unknownCondM1, wodM1) =
              let unknownCond0' = unknownCond0 ∖ wodM2
                  wod    =    wod3
                  notwod = notwod3
                  (unknownCond1, wod1, notwod1) = foldr (fromPdomM1 m) (unknownCond0', Set.empty, Set.empty) (Map.assocs ndomsM2)
                  (unknownCond2, wod2, notwod2) = foldr (fromDomM1  m) (unknownCond1,  wod1,      notwod1  ) (Map.assocs ndomsM2)
                  (unknownCond3, wod3, notwod3) = foldr (fromPmayM1 m) (unknownCond2,  wod2,      notwod2  ) (Map.assocs ndomsM2)
              in
                 -- traceShow ("M1 1", (unknownCond1, wod1, notwod1)) $ 
                 -- traceShow ("M1 2", (unknownCond2, wod2, notwod2)) $ 
                 -- traceShow ("M1 3", (unknownCond3, wod3, notwod3)) $ 
                 assert ( assertionsDisabled ∨  unknownCond0' ⊇ unknownCond1  ∧  unknownCond1 ⊇ unknownCond2  ∧  unknownCond2 ⊇ unknownCond3) $
                 assert ( assertionsDisabled ∨                                           wod1 ⊆         wod2  ∧          wod2 ⊆    wod3) $
                 assert ( assertionsDisabled ∨                                        notwod1 ⊆      notwod2  ∧       notwod2 ⊆ notwod3) $
                 (unknownCond3 ∖ (wod ∪ notwod), wod)

    in
       -- traceShow (m,ms, covered, coveredPDom, coveredDom, coveredPMay) $
       assert ( assertionsDisabled ∨  (covered ↔  (∀) unknownCond0 (\c ->  c == m  ∨ (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->
            (∀) (suc graph c) (\x ->       x ∈ dom  ! m)
          ∨ (∀) (suc graph c) (\x ->       m ∈ pdom ! x)
          ∨ (∀) (suc graph c) (\x -> not $ m ∈ pmay ! x)
       )))) $ 
       (Set.delete m $ wodM2 ∪ wodM1, (Set.insert m ms, ndomsM2))
  where assertionsDisabled = True
        condNodes    = Set.fromList [ c | c <- nodes graph, length (suc graph c) > 1, not $ c ∈ ms, c /= m ]
        unknownCond0 = Set.filter  (\c -> (not $ c ∈ ms) ∧ (c /= m)) condNodes

        fromDomM2 :: Node -> (Node, ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Maybe Node), Map Node (Maybe Node)))) -> (Set Node, Set Node, Set Node) -> (Set Node, Set Node, Set Node)
        fromDomM2 m2 (n,((_,dom,_),(_,idom))) (unknownCond, wod, notwod)  =
                   assert ( assertionsDisabled ∨    wodNew ==     wodNewFast ) $
                   assert ( assertionsDisabled ∨ notwodNew ==  notwodNewFast ) $
                   (unknownCond', wod ∪ wodNewFast, notwod ∪ notwodNewFast)
          where unknownCond' = unknownCond ∖ (wodNewFast ∪ notwodNewFast)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                                  (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> x ∈ dom ! m2),
                                            not $ (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))]

                cWithM1s = [ (c, findBoth idom ms (Set.fromList $ suc graph c) m2) | c <- Set.toList unknownCond ]
                wodNewFast    = Set.fromList [ c | (c,(foundMs,_        )) <- cWithM1s, foundMs   ]
                notwodNewFast = Set.fromList [ c | (c,(_      ,foundNoMs)) <- cWithM1s, foundNoMs ]


        fromDomM1 :: Node -> (Node, ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Maybe Node), Map Node (Maybe Node)))) -> (Set Node, Set Node, Set Node) -> (Set Node, Set Node, Set Node)
        fromDomM1 m1 (n,((_,dom,_),(_,idom))) (unknownCond, wod, notwod)  =
                   assert ( assertionsDisabled ∨     wodNew ==     wodNewFast ) $
                   assert ( assertionsDisabled ∨  notwodNew ==  notwodNewFast ) $
                   (unknownCond', wod ∪ wodNewFast, notwod ∪ notwodNewFast)
          where unknownCond' = unknownCond ∖ (wodNewFast ∪ notwodNewFast)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∃) ms (\m2 -> 
                                                    (∀) (suc graph c) (\x -> x ∈ dom ! m2) ∧
                                                    (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) )
                                                  )]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) ms (\m2 -> 
                                                    ((∀) (suc graph c) (\x -> x ∈ dom ! m2)) ∧
                                             (not $ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ dom ! xl ∧ m1 /= xl)   ∧  (not $ m1 ∈ dom ! xr ∧ m1 /= xr)     ) ))
                                                  )]

                wodNewFast    = Set.fromList [ c | c <- Set.toList unknownCond, findM2sFast idom ms (Set.fromList $ suc graph c) m1  ]
                notwodNewFast = Set.fromList [ c | c <- Set.toList unknownCond, not $ c ∈ wodNewFast, (∀) ms (\m2 -> findNoMs idom (Set.fromList [m1]) (Set.fromList $ suc graph c) m2)  ]
                
        fromPdomM2 :: Node -> (Node, ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Maybe Node), Map Node (Maybe Node)))) -> (Set Node, Set Node, Set Node) -> (Set Node, Set Node, Set Node)
        fromPdomM2 m2 (n,((pdom,_,_),(ipdom,_))) ((unknownCond, wod, notwod){-, (must, notmust)-})  =
                   assert ( assertionsDisabled ∨     wodNew ==     wodNewFast ) $
                   assert ( assertionsDisabled ∨  notwodNew ==  notwodNewFast ) $
                   (unknownCond', wod ∪ wodNewFast, notwod ∪ notwodNewFast)
          where unknownCond' = unknownCond ∖ (wodNewFast ∪ notwodNewFast)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                                  (∃) ms (\m1 -> (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)  ∧   (not $ m1 ∈ pdom ! xr))))
                               ]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> m2 ∈ pdom ! x),
                                            not $ (∃) ms (\m1 -> (m2 ∈ pdom ! m1)  ∧  (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m1 ∈ pdom ! xr))))
                               ]

                isReachableIPDomFrom = isReachableFromTreeM ipdom
                withJoin     = [ (c,z,relevant) | c <- Set.toList unknownCond, let (z,relevant) = lcaRKnownM ipdom c (suc graph c), m2 `isReachableIPDomFrom` z ]
                wodNewFast   = Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  (∃) ms (\m1 -> (m1 ∈ relevant)  ∧  (m1 /= z))
                               ]
                notwodNewFast= Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  not $ c ∈ wodNewFast
                                            -- not $ (∃) ms (\m1 -> (m1 ∈ relevant)  ∧  (m1 /= z))
                               ]



        fromPdomM1 :: Node -> (Node, ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Maybe Node), Map Node (Maybe Node)))) -> (Set Node, Set Node, Set Node) -> (Set Node, Set Node, Set Node)
        fromPdomM1 m1  (n,((pdom,_,_),(ipdom,_))) (unknownCond, wod, notwod)  =
                   assert ( assertionsDisabled ∨     wodNew ==     wodNewFast ) $
                   assert ( assertionsDisabled ∨  notwodNew ==  notwodNewFast ) $
                   (unknownCond', wod ∪ wodNewFast, notwod ∪ notwodNewFast)
          where unknownCond' = unknownCond ∖ (wodNewFast ∪ notwodNewFast)
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

                isReachableIPDomFrom = isReachableFromTreeM ipdom
                withJoin     = [ (c,z,relevant) | c <- Set.toList unknownCond, let (z,relevant) = lcaRKnownM ipdom c (suc graph c) ]
                wodNewFast   = Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  (m1 /= z)  ∧  (       m1 ∈ relevant),
                                                  (∃) ms (\m2 -> m2 `isReachableIPDomFrom` m1)
                               ]
                notwodNewFast= Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  not $ c ∈ wodNewFast,
                                                  (m1 == z)  ∨  (not $ m1 ∈ relevant),
                                                  allReachableFromTreeM ipdom ms z
                               ]

        fromPmayM2 :: Node -> (Node, ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Maybe Node), Map Node (Maybe Node)))) -> (Set Node, Set Node, Set Node) -> (Set Node, Set Node, Set Node)
        fromPmayM2 m2 (n,((pdom, dom, pmay),(ipdom,idom))) (unknownCond, wod, notwod) =
                   assert ( assertionsDisabled ∨     wodNew ==     wodNewFast ) $
                   assert ( assertionsDisabled ∨  notwodNew ==  notwodNewFast ) $
                  (unknownCond', wod ∪ wodNewFast, notwod ∪ notwodNewFast)
          where unknownCond' = unknownCond ∖ (wodNewFast ∪ notwodNewFast)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> not $ m2 ∈ pmay ! x),
                                                  (∃) ms (\m1 -> (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl )   ∧  (not $ m1 ∈ pdom ! xr))))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> not $ m2 ∈ pmay ! x),
                                            not $ (∃) ms (\m1 -> (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl )   ∧  (not $ m1 ∈ pdom ! xr))))]

                isReachableIDomFrom  = isReachableFromTreeM idom
                gn = delSuccessorEdges graph n
                wodNewFast   = Set.fromList [ c | (n /= m2),
                                                  c <- Set.toList unknownCond, 
                                                  assert (m2 /= c) True,
                                                  (n /= c) ∧ (not $ m2 `elem` reachable c gn),
                                                  let (z, relevant) = lcaRKnownM ipdom c (suc graph c),
                                                  (∃) ms (\m1 -> m1 ∈ relevant  ∧  m1 /= z  ∧  (not $ m1 `isReachableIDomFrom` m2))
                              ]
                notwodNewFast   = Set.fromList [ c | (n /= m2),
                                                  c <- Set.toList unknownCond, 
                                                  not $ c ∈ wodNewFast,
                                                  assert (m2 /= c) True,
                                                  (n /= c) ∧ (not $ m2 `elem` reachable c gn),
                                                  let (z, relevant) = lcaRKnownM ipdom c (suc graph c),
                                            not $ (∃) ms (\m1 -> m1 ∈ relevant  ∧  m1 /= z  ∧  (not $ m1 `isReachableIDomFrom` m2))
                              ]



        fromPmayM1 :: Node -> (Node, ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Maybe Node), Map Node (Maybe Node)))) -> (Set Node, Set Node, Set Node) -> (Set Node, Set Node, Set Node)

        fromPmayM1 m1 (n,((pdom, dom, pmay),(ipdom, idom))) (unknownCond, wod, notwod) =
                   assert ( Set.null wodNewFast) $ 
                   assert ( assertionsDisabled ∨     wodNew ==     wodNewFast ) $
                   -- assert ( notwodNew ==  notwodNewFast ) $
                   (unknownCond', wod ∪ wodNewFast, notwod) -- do not use notwodNewFast at all
          where unknownCond' = unknownCond ∖ wodNewFast
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∃) ms (\m2 ->
                                                    (∀) (suc graph c) (\x -> not $ m2 ∈ pmay ! x) ∧ 
                                                    (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m1 ∈ pdom ! xr )))
                                                  )
                               ]
                -- notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                --                                   (∀) ms (\m2 -> 
                --                                     (∀) (suc graph c) (\x -> not $ m2 ∈ pmay ! x) ∧ 
                --                              (not $ (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl)   ∧  (not $ m1 ∈ pdom ! xr ))))
                --                                   )
                --                ]

                isReachableIDomFrom  = isReachableFromTreeM idom
                withReachRelevant = [ (c, reachable c gn, lcaRKnownM ipdom c (suc graph c)) | c <- Set.toList unknownCond ]
                  where gn = delSuccessorEdges graph n
                wodNewFast   = Set.fromList [ c | (c, reach, (z,relevant)) <- withReachRelevant,
                                                  (∃) ms (\m2 -> assert (m2 /= c) $ 
                                                    (n /= m2) ∧ 
                                                    (n /= c) ∧
                                                    m1 /= z  ∧
                                                    m1 ∈ relevant ∧
                                                    (not $ isReachableBeforeFromTreeM idom m1 z m2) ∧
                                                    (not $ m2 `elem` reach)
                                                  )
                              ]
                -- notwodNewFast= Set.fromList [ c | (c, reach, (z,relevant)) <- withReachRelevant,
                --                                   not $ c ∈ wodNewFast,
                --                                   (∀) ms (\m2 -> assert (m2 /= c) $ 
                --                                     (n /= m2) ∧ 
                --                                     (n /= c) ∧
                --                              (not $ m1 /= z ∧ (not $ m1 `isReachableIDomFrom` m2) ∧ m1 ∈ relevant  ) ∧
                --                                     (not $ m2 `elem` reach)
                --                                   )
                --               ]



findMustNotMust dom ms xs n = find found0 notfound0 must0 notmust0 n
  where found0    = Set.empty
        notfound0 = ms
        
        must0     = Map.empty
        notmust0  = Map.empty
        
        find found notfound must notmust n = case Set.toList $ dom ! n of
                             []  -> (must', notmust')
                             [z] -> find found' notfound' must' notmust' z
                             _   -> error "no tree"
          where  nInMs     = n ∈ ms
                 nInXs     = n ∈ xs
                 found'    = if nInMs then Set.insert n    found else    found
                 notfound' = if nInMs then Set.delete n notfound else notfound
                 must'     = if nInXs then
                                 Map.insert n     found'  must
                               else                       must
                 notmust'  = if nInXs then
                                 Map.insert n  notfound'  notmust
                               else                       notmust



findM2s :: Ord a => Map a (Maybe a) -> Set a -> Set a -> a -> Bool
findM2s dom ms xs n
    | List.null topmost = False
    | otherwise         = find n
  where topmost = [ x |  x <- Set.toList xs, allReachableFromTreeM dom xs' x]
          where xs' = Set.insert n xs
        [x0]    = topmost
        find n
            | n == x0 = False
            | n ∈ xs  = (∃) ms (\m2 -> isReachableFromTreeM dom x0 m2)
            | otherwise = case dom ! n of
                            Nothing -> False
                            Just z  -> find z

findM2sFast :: Ord a => Map a (Maybe a) -> Set a -> Set a -> a -> Bool
findM2sFast dom ms xs n = assert (result == findM2s dom ms xs n) $
                          result
  where result = case findTop xs (Set.insert n xs) of
          Nothing -> False
          Just x0 -> find n
            where find n
                    | n == x0 = False
                    | n ∈ xs  = (∃) ms (\m2 -> isReachableFromTreeM dom x0 m2)
                    | otherwise = case dom ! n of
                                    Nothing -> False
                                    Just z  -> find z

        findTop candidates toFind
            | Set.null candidates = Nothing
            | Set.null toFind'    = Just x
            | otherwise           = findTop candidates' (Set.insert x toFind')
          where (x,candidates') = Set.deleteFindMin candidates
                toFind' = find x (Set.delete x toFind)
                  where find x toFind = case dom ! x of
                                          Nothing -> toFind
                                          Just z  -> find z (Set.delete z toFind)










data MyWodSimpleSliceState gr a b = MyWodSimpleSliceState {
   ms :: Set Node,
   condNodes ::  Map Node [Node],
   nAndIpdomForSink  :: Map Node (Node, Map Node (Maybe Node)),
   ready :: Map Node (Set Node),
   isinkdom :: Map Node (Maybe Node),
   sinks :: [[Node]],
   sinkOf :: Map Node Node,
   entryIntoSink :: Map Node Node,
   gTowardsSink :: Map Node (gr a b, Map Node [Node])
}

deriving instance (Show (gr a b)) => Show (MyWodSimpleSliceState gr a b)


initialMyWodSimpleSliceState :: DynGraph gr => gr a b -> MyWodSimpleSliceState gr a b
initialMyWodSimpleSliceState graph = MyWodSimpleSliceState {
      ms               = Set.empty,
      condNodes        = restrict condNodes (entryNodes ∪ sinkNodes),
      -- nAndIpdomForSink = nAndIpdomForSink,
      nAndIpdomForSink = Map.empty,
      ready            = Map.empty,
      isinkdom         = isinkdom,
      sinks            = sinks,
      sinkOf           = sinkOf,
      entryIntoSink    = entryIntoSink,
      gTowardsSink     = gTowardsSink
    }
  where sinks         = controlSinks graph
        sinkOf        = Map.fromList [ (s, s0)  | sink@(s0:_) <- sinks, s <- sink ]
        sinkNodes     = (∐) [ Set.fromList sink | sink <- sinks ]

        isinkdom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes (without condNodes sinkNodes) graph
        entryIntoSink = Map.fromList [ (n, sinkOf ! m) | (n, Just m) <-  Map.assocs $ isinkdom, m ∈ sinkNodes, not $ n ∈ sinkNodes ]
        entryNodes    = Map.keysSet entryIntoSink
        condNodes     = Map.fromList [ (c, succs) | c <- nodes graph, let succs = suc graph c, length succs  > 1]

        gTowardsSink  = Map.fromList [ (s0, (subgraph (towards ++ sink) graph, restrict condNodes (towardsS ∪ sinkS)))
                                         | sink@(s0:_) <- sinks,
                                           let sinkS = Set.fromList sink,
                                           let towards  = [ m | (n, s0') <- Map.assocs entryIntoSink, s0 == s0', m <- towardsCycle graph sinkS n],
                                           let towardsS = Set.fromList towards
                        ]
        nAndIpdomForSink = Map.fromList [ (s0, (s0, recompute graphWithConds Nothing s0)) | (s0, graphWithConds) <- Map.assocs gTowardsSink ]


myWodFromSimpleSliceStep :: (DynGraph gr, Show (gr a b)) => ((gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)) -> gr a b -> Node -> Node -> Set Node
myWodFromSimpleSliceStep newIPDomFor graph = \m1 m2 ->
    let (new1, s1) = myWodSliceSimpleStep graph newIPDomFor s0 m1
        (new2, s2) = myWodSliceSimpleStep graph newIPDomFor s1 m2
    in  assert (Set.null new1) $
        assert (ms s1 == Set.fromList [m1]) $
        assert (ms s2 == Set.fromList [m1, m2]) $
        new2
  where s0 = initialMyWodSimpleSliceState graph
        


nticdMyWodSliceSimple :: (Show (gr a b), DynGraph gr) => ((gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)) -> gr a b -> Set Node -> Set Node
nticdMyWodSliceSimple newIPDomFor graph = \ms ->
           nticdslicer $ slice s0 ms
  where nticdslicer = combinedBackwardSlice graph nticd Map.empty
        s0@(MyWodSimpleSliceState { sinks, isinkdom }) = initialMyWodSimpleSliceState graph
        nticd = xDFcd (\graph -> idomToDFFastForRoots roots graph isinkdom) graph
          where roots = go (Map.assocs isinkdom) sinks
                  where go []     roots = roots
                        go ((n, m):as) roots = case m of
                          Nothing -> go as ([n]:roots)
                          _       -> go as      roots

        step = myWodSliceSimpleStep graph newIPDomFor
        slice s@(MyWodSimpleSliceState { ms }) ns
          | Set.null ns = -- traceShow (Set.size sliceNodes, length $ nodes graph ) $
                          ms
          | otherwise   = -- traceShow (sliceNodes, Map.keys ndoms) $
                          slice s' ns'
              where (n, ns0)  = Set.deleteFindMin ns
                    (new, s') = step s n
                    ns' = ns0 ∪ new 


myWodSliceSimple :: (Show (gr a b), DynGraph gr) => ((gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)) -> gr a b -> Set Node -> Set Node
myWodSliceSimple newIPDomFor graph = \ms -> slice s0 ms
  where s0 = initialMyWodSimpleSliceState graph
        step = myWodSliceSimpleStep graph newIPDomFor
        slice s@(MyWodSimpleSliceState { ms }) ns
          | Set.null ns = -- traceShow (Set.size sliceNodes, length $ nodes graph ) $
                          ms
          | otherwise   = -- traceShow (sliceNodes, Map.keys ndoms) $
                          slice s' ns'
              where (n, ns0)  = Set.deleteFindMin ns
                    (new, s') = step s n
                    ns' = ns0 ∪ new 

myWodSliceSimpleStep :: forall gr a b. (DynGraph gr) =>
  gr a b ->
  ((gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)) ->
  MyWodSimpleSliceState gr a b->
  Node ->
  (Set Node, MyWodSimpleSliceState gr a b)
myWodSliceSimpleStep graph newIPDom s@(MyWodSimpleSliceState { ms, condNodes, nAndIpdomForSink, ready, sinkOf, entryIntoSink, gTowardsSink}) m
    | m ∈ ms                         = (Set.empty,                     s)
    | Map.lookup m sinkOf == Nothing = (Set.empty,                     s { ms = ms' })
    | otherwise                      = assert (ready' == ready'Fast) $
                                       ((fromReady ∪ fromIpdom) ∖ ms', s { ms = ms', condNodes = condNodes', nAndIpdomForSink = nAndIpdomForSink', ready = Map.delete m ready'Fast })
  where ms' = Set.insert m ms
        nAndIpdomForSink' = Map.insert sinkM (m, ipdom') nAndIpdomForSink
        Just sinkM = Map.lookup m sinkOf
        condNodes' =  Map.delete m condNodes
        fromReady  = Map.findWithDefault (Set.empty) m ready
        
        cWithRelevant = [ (c, lcaRKnownM ipdom' c succs) |  (c, succs) <- Map.assocs condNodes', Just sinkM == Map.lookup c sinkOf    ∨  Just sinkM == Map.lookup c entryIntoSink ]
        fromIpdom = Set.fromList [ c | (c, (z,relevant)) <- cWithRelevant,
                                       (∃) (ms) (\m1 -> m1 /= z ∧ m1 ∈ relevant ∧ (Map.lookup m1 sinkOf  == Just sinkM ))
                    ]
        ready' = ready
               ⊔ (∐) [ Map.fromList [ (m1, Set.fromList [ c ]) ] | (c, (z,relevant)) <- cWithRelevant,
                                                                    m1 <- Set.toList relevant, m1 /= z, Map.lookup m sinkOf == Just sinkM
                 ]
        ready'Fast = foldr (\(c,m1) ready -> Map.alter (f c) m1 ready) ready [ (c,m1) | (c, (z,relevant)) <- cWithRelevant, m1 <- Set.toList relevant, m1 /= z, Map.lookup m sinkOf == Just sinkM ]
          where f c Nothing   = Just $ Set.singleton c
                f c (Just cs) = Just $ Set.insert c cs
        ipdom' = case ipdomN of
                   Nothing         -> newIPDom (gTowardsSink ! sinkM) ipdomN m
                   Just (n, ipdom) -> if n == m then ipdom else
                                      newIPDom (gTowardsSink ! sinkM) ipdomN m
          where ipdomN = Map.lookup sinkM nAndIpdomForSink

cutNPasteIfPossible :: DynGraph gr =>  (gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)
cutNPasteIfPossible graphWithConds                     Nothing           m = recompute graphWithConds undefined m
cutNPasteIfPossible graphWithConds@(graph, condNodes)  (Just (n, ipdom)) m
    | List.null succs = isinkdomOfTwoFinger8DownUniqueExitNode graphm m condNodesM ipdomM''''
    | otherwise       = isinkdomOfTwoFinger8DownUniqueExitNode graphm m condNodesM ipdomM'''

  where -- ipdomM'   = Map.union (Map.fromList [(n', Set.fromList [m]) | n' <- pre g m ]) ipdom
        ipdomM''  = Map.insert m Nothing ipdom
        succs     = [ x | x <- suc graph n, isReachableFromTreeM ipdomM'' m x]

        ipdomM''' = assert (z /= Nothing) $ 
                    Map.insert n z ipdomM''
          where z = foldM1 (lca ipdomM'') succs


        ipdomM'''' = isinkdomOftwoFinger8Up graphm condNodesM worklist0 processed0 imdom0
          where nIsCond    = Map.member n condNodes
                [nx]       = suc graphm n
                processed0 = Set.fromList [ x            | x <- nodes graphm, m ∈ reachableFromTree (fmap toSet ipdomM'') x]
                imdom0     = (if nIsCond then id else Map.insert n (Just nx)) $
                             Map.fromList [ (x, Nothing) | x <- nodes graphm, not $ x ∈ processed0, Map.member x condNodesM] `Map.union` ipdomM''
                worklist0  = Seq.fromList [ x            | x <- nodes graphm, not $ x ∈ processed0, Map.member x condNodesM]

        graphm = delSuccessorEdges graph m
        condNodesM = Map.delete m condNodes

-- recompute :: DynGraph gr =>  (gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)
-- recompute (graph, condNodes) _ m = fmap fromSet $ isinkdomOfTwoFinger8ForSinks [[m]] (Set.fromList [m]) (fmap Set.fromList condNodesM) graphM
--   where condNodesM = Map.delete m condNodes
--         graphM = delSuccessorEdges graph m

recompute :: DynGraph gr =>  (gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)
recompute (graph,_) _ m = ipdom
  where ipdom = fromIdom m $ iDom (grev $ delSuccessorEdges   graph m) m
          where fromIdom m idom = Map.insert m Nothing $ Map.fromList [ (n, Just m) | (n,m) <- idom ]



wccSliceViaNticdMyWodSliceSimple :: (Show (gr a b), DynGraph gr) =>  ((gr a b, Map Node [Node]) -> Maybe (Node, Map Node (Maybe Node)) -> Node -> Map Node (Maybe Node)) -> gr a b ->  Set Node -> Set Node
wccSliceViaNticdMyWodSliceSimple newIPDomFor g ms = s ∩ fromMs
  where gRev = grev g
        g'   = subgraph (Set.toList toMs) g
        s    = nticdMyWodSliceSimple newIPDomFor g' ms
        toMs   = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m gRev ]
        fromMs = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m g    ]
