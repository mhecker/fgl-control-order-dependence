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
import Data.Graph.Inductive.Query.DFS (reachable)
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)

import Util(the, invert', invert'', foldM1, reachableFrom, treeDfs, toSet, fromSet, isReachableFromTree, isReachableBeforeFromTree, allReachableFromTree, findMs, findNoMs, findBoth, reachableFromTree)
import Unicode



import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic hiding (postorder)
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.NTICD
import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs)

import Debug.Trace
import Control.Exception.Base (assert)



type MyWodSliceState = (Set Node, (Map Node ((Map Node (Set Node), Map Node (Set Node), Map Node (Set Node)),(Map Node (Set Node), Map Node (Set Node)))))

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
          | Set.null ms = traceShow ( (-1) + ceiling ( (100 * fromIntegral (Map.size ndoms) / fromIntegral (Set.size sliceNodes) :: Double)), Set.size sliceNodes, Map.size ndoms, length $ nodes graph ) $
                          sliceNodes
          | otherwise   = -- traceShow (sliceNodes, Map.keys ndoms) $
                          slice s' ms'
              where (m, ms0)  = Set.deleteFindMin ms
                    (new, s') = step s m
                    ms' = ms0 ∪ new 


myWodSliceStep :: forall gr a b. (Show (gr a b), DynGraph gr) => gr a b ->  MyWodSliceState -> Node -> (Set Node, MyWodSliceState)
myWodSliceStep graph (ms, ndoms) m = if m ∈ ms then (Set.empty, (ms, ndoms)) else
    require
      ((∀) ms (\m -> (∀) unknownCond0 (\c ->          (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->
            (∀) (suc graph c) (\x ->       x ∈ dom  ! m)
          ∨ (∀) (suc graph c) (\x ->       m ∈ pdom ! x)
          ∨ (∀) (suc graph c) (\x -> not $ m ∈ pmay ! x)
      )))) $
    let covered    = (∀) unknownCond0 (\c -> c == m ∨ 
            (∃) (Map.assocs ndoms) (\(n, ((_,_,pmay),(ipdom, idom))) -> (∀) (suc graph c) (\x ->  isReachableFromTree idom  x m))
          ∨ (∃) (Map.assocs ndoms) (\(n, ((_,_,pmay),(ipdom, idom))) -> (∀) (suc graph c) (\x ->  isReachableFromTree ipdom m x))
          ∨ (∃) (Map.assocs ndoms) (\(n, ((_,_,pmay),(ipdom, idom))) -> (∀) (suc graph c) (\x ->  not $ m `elem` reachable x (delSuccessorEdges graph n)))
          )
        coveredDom  = Set.filter (\c ->  (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->       (∀) (suc graph c) (\x ->        x ∈  dom ! m ))) unknownCond0
        coveredPDom = Set.filter (\c ->  (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->       (∀) (suc graph c) (\x ->        m ∈ pdom ! x ))) unknownCond0
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
                 assert (unknownCond0 ⊇ unknownCond1  ∧  unknownCond1 ⊇ unknownCond2  ∧  unknownCond2 ⊇ unknownCond3) $
                 assert (                                        wod1 ⊆         wod2  ∧          wod2 ⊆    wod3) $
                 assert (                                     notwod1 ⊆      notwod2  ∧       notwod2 ⊆ notwod3) $
                 (unknownCond2 ∖ (wod ∪ notwod), wod, ndoms)
            else
              let (wod, notwod)        = Set.partition (\c -> (∃) ms (\m1 -> (∃) (suc graph c) (\xl ->  m1 ∈ pdom ! xl)  ∧ (∃) (suc graph c) (\xr -> not $ m1 ∈ pdom ! xr))) unknownCond0
                  (wodFast,notwodFast) = Set.partition (\c ->  let (z, relevant) = lcaRKnown ipdom c (suc graph c) in (∃) ms (\m1 -> m1 /= z ∧ m1 ∈ relevant))               unknownCond0
                  ndoms' = Map.insert m ((pdom, dom, pmay), (ipdom, idom)) ndoms
                  ( pdom,  dom,  pmay)  = ( sinkdomOfGfp         $ delSuccessorEdges       graph  m,
                                            sinkdomOfGfp         $ delSuccessorEdges (grev graph) m,
                                            mayNaiveGfp $ delSuccessorEdges graph m
                                          )
                  (ipdom, idom       )  = ( fromIdom m $ iDom (grev $ delSuccessorEdges   graph m) m,
                                            fromIdom m $ iDom (       delPredecessorEdges graph m) m
                                          )
                    where fromIdom m idom = Map.insert m Set.empty $ Map.fromList [ (n, Set.fromList [m]) | (n,m) <- idom ]
              in
                 assert (   wod ==    wodFast) $
                 assert (notwod == notwodFast) $
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
                 assert (unknownCond0' ⊇ unknownCond1  ∧  unknownCond1 ⊇ unknownCond2  ∧  unknownCond2 ⊇ unknownCond3) $
                 assert (                                         wod1 ⊆         wod2  ∧          wod2 ⊆    wod3) $
                 assert (                                      notwod1 ⊆      notwod2  ∧       notwod2 ⊆ notwod3) $
                 (unknownCond3 ∖ (wod ∪ notwod), wod)

    in
       -- traceShow (m,ms, covered, coveredPDom, coveredDom, coveredPMay) $
       assert ( covered ↔  (∀) unknownCond0 (\c ->  c == m  ∨ (∃) (Map.assocs ndoms) (\(n, ((pdom, dom, pmay),_)) ->
            (∀) (suc graph c) (\x ->       x ∈ dom  ! m)
          ∨ (∀) (suc graph c) (\x ->       m ∈ pdom ! x)
          ∨ (∀) (suc graph c) (\x -> not $ m ∈ pmay ! x)
       ))) $ 
       (Set.delete m $ wodM2 ∪ wodM1, (Set.insert m ms, ndomsM2))
  where condNodes    = Set.fromList [ c | c <- nodes graph, length (suc graph c) > 1, not $ c ∈ ms, c /= m ]
        unknownCond0 = Set.filter  (\c -> (not $ c ∈ ms) ∧ (c /= m)) condNodes
        
        fromDomM2 m2 (n,((_,dom,_),(_,idom))) (unknownCond, wod, notwod)  =
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
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


        fromDomM1 m1 (n,((_,dom,_),(_,idom))) (unknownCond, wod, notwod)  =
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
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

                wodNewFast    = Set.fromList [ c | c <- Set.toList unknownCond, findM2s idom ms (Set.fromList $ suc graph c) m1  ]
                notwodNewFast = Set.fromList [ c | c <- Set.toList unknownCond, not $ c ∈ wodNewFast, (∀) ms (\m2 -> findNoMs idom (Set.fromList [m1]) (Set.fromList $ suc graph c) m2)  ]
                
        fromPdomM2 m2 (n,((pdom,_,_),(ipdom,_))) ((unknownCond, wod, notwod){-, (must, notmust)-})  =
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
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

                isReachableIPDomFrom = isReachableFromTree ipdom
                withJoin     = [ (c,z,relevant) | c <- Set.toList unknownCond, let (z,relevant) = lcaRKnown ipdom c (suc graph c), m2 `isReachableIPDomFrom` z ]
                wodNewFast   = Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  (∃) ms (\m1 -> (m1 ∈ relevant)  ∧  (m1 /= z))
                               ]
                notwodNewFast= Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  not $ c ∈ wodNewFast
                                            -- not $ (∃) ms (\m1 -> (m1 ∈ relevant)  ∧  (m1 /= z))
                               ]



        fromPdomM1 m1  (n,((pdom,_,_),(ipdom,_))) (unknownCond, wod, notwod)  =
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
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

                isReachableIPDomFrom = isReachableFromTree ipdom
                withJoin     = [ (c,z,relevant) | c <- Set.toList unknownCond, let (z,relevant) = lcaRKnown ipdom c (suc graph c) ]
                wodNewFast   = Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  (m1 /= z)  ∧  (       m1 ∈ relevant),
                                                  (∃) ms (\m2 -> m2 `isReachableIPDomFrom` m1)
                               ]
                notwodNewFast= Set.fromList [ c | (c,z,relevant) <- withJoin,
                                                  not $ c ∈ wodNewFast,
                                                  (m1 == z)  ∨  (not $ m1 ∈ relevant),
                                                  allReachableFromTree ipdom ms z
                               ]

        fromPmayM2 m2 (n,((pdom, dom, pmay),(ipdom,idom))) (unknownCond, wod, notwod) =
                   assert (    wodNew ==     wodNewFast ) $
                   assert ( notwodNew ==  notwodNewFast ) $
                  (unknownCond', wod ∪ wodNewFast, notwod ∪ notwodNewFast)
          where unknownCond' = unknownCond ∖ (wodNewFast ∪ notwodNewFast)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> not $ m2 ∈ pmay ! x),
                                                  (∃) ms (\m1 -> (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl )   ∧  (not $ m1 ∈ pdom ! xr))))]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond,
                                                  (∀) (suc graph c) (\x -> not $ m2 ∈ pmay ! x),
                                            not $ (∃) ms (\m1 -> (not $ m1 ∈ dom ! m2) ∧ (∃) (suc graph c) (\xl -> (∃) (suc graph c) (\xr -> (m1 ∈ pdom ! xl )   ∧  (not $ m1 ∈ pdom ! xr))))]

                isReachableIDomFrom  = isReachableFromTree idom
                gn = delSuccessorEdges graph n
                wodNewFast   = Set.fromList [ c | (n /= m2),
                                                  c <- Set.toList unknownCond, 
                                                  assert (m2 /= c) True,
                                                  (n /= c) ∧ (not $ m2 `elem` reachable c gn),
                                                  let (z, relevant) = lcaRKnown ipdom c (suc graph c),
                                                  (∃) ms (\m1 -> m1 ∈ relevant  ∧  m1 /= z  ∧  (not $ m1 `isReachableIDomFrom` m2))
                              ]
                notwodNewFast   = Set.fromList [ c | (n /= m2),
                                                  c <- Set.toList unknownCond, 
                                                  not $ c ∈ wodNewFast,
                                                  assert (m2 /= c) True,
                                                  (n /= c) ∧ (not $ m2 `elem` reachable c gn),
                                                  let (z, relevant) = lcaRKnown ipdom c (suc graph c),
                                            not $ (∃) ms (\m1 -> m1 ∈ relevant  ∧  m1 /= z  ∧  (not $ m1 `isReachableIDomFrom` m2))
                              ]




        fromPmayM1 m1 (n,((pdom, dom, pmay),(ipdom, idom))) (unknownCond, wod, notwod) =
                   assert (Set.null    wodNew) $ 
                   assert (    wodNew ==     wodNewFast ) $
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

                isReachableIDomFrom  = isReachableFromTree idom
                withReachRelevant = [ (c, reachable c gn, lcaRKnown ipdom c (suc graph c)) | c <- Set.toList unknownCond ]
                  where gn = delSuccessorEdges graph n
                wodNewFast   = Set.fromList [ c | (c, reach, (z,relevant)) <- withReachRelevant,
                                                  (∃) ms (\m2 -> assert (m2 /= c) $ 
                                                    (n /= m2) ∧ 
                                                    (n /= c) ∧
                                                    m1 /= z  ∧
                                                    m1 ∈ relevant ∧
                                                    (not $ isReachableBeforeFromTree idom m1 z m2) ∧
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




findM2s dom ms xs n
    | List.null topmost = False
    | otherwise         = find n
  where topmost = [ x |  x <- Set.toList xs, allReachableFromTree dom xs' x]
          where xs' = Set.insert n xs
        [x0]    = topmost
        find n
            | n == x0 = False
            | n ∈ xs  = (∃) ms (\m2 -> isReachableFromTree dom x0 m2)
            | otherwise = case Set.toList $ dom ! n of
                            []  -> False
                            [z] -> find z
                            _   -> error "no tree"
                 
