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
    traceShow (Map.keys $ snd s2) $ 
    new2
  where s0 = (Set.empty, Map.empty)
        (new1, s1) = myWodSliceStep graph s0 m1
        (new2, s2) = myWodSliceStep graph s1 m2
        
myWodSliceStep :: DynGraph gr => gr a b ->  MyWodSliceState -> Node -> (Set Node, MyWodSliceState)
myWodSliceStep graph (ms, ndoms) m = if m ∈ ms then (Set.empty, (ms, ndoms)) else
    let ((unknownCond, wod, notwod), (must, notmust)) = foldr (fromPdom m) ((condNodes0, Set.empty, Set.empty), (Map.empty, Map.empty)) (Map.keys ndoms)
        wodFromMust    = Set.fromList [ c | c <- Set.toList unknownCond,
                              (∃) ms (\m1 -> (∃) (suc graph c) (\xl -> Map.member xl    must  ∧ (∃) (suc graph c) (\xr -> Map.member xr notmust  ∧  m ∈    must ! xl  ∧  m ∈ notmust ! xr)))]
        notwodFromMust = Set.fromList [ c | c <- Set.toList unknownCond,
                              (∀) ms (\m1 -> (∀) (suc graph c) (\xl -> (Map.member xl    must ∧ (∀) (suc graph c) (\xr -> Map.member xr    must  ∧  m ∈    must ! xl  ∧  m ∈    must ! xr))
                                                                      ∨ (Map.member  xl notmust ∧ (∀) (suc graph c) (\xr -> Map.member xr notmust  ∧  m ∈ notmust ! xl  ∧  m ∈ notmust ! xr))))]
        unknownCond'   = unknownCond ∖ (wod ∪ wodFromMust)
    in assert (unknownCond' ⊆ condNodes0) $
       if Set.null unknownCond' then
         (wod ∪ wodFromMust, (Set.insert m ms, ndoms))
       else
         let (pdom, dom)  = ( sinkdomOfGfp $ delSuccessorEdges graph m, sinkdomOfGfp $ delSuccessorEdges (grev graph) m)
             wod = Set.fromList [ c | c <- Set.toList condNodes0, (∃) ms (\m1 -> (∃) (suc graph c) (\xl ->  m1 ∈ pdom ! xl)  ∧ (∃) (suc graph c) (\xr -> not $ m1 ∈ pdom ! xr)) ]
         in (wod, (Set.insert m ms, Map.insert m (pdom, dom) ndoms))
  where condNodes0 = Set.fromList [ c | c <- nodes graph, length (suc graph c) > 1, not $ c ∈ ms ]
        fromPdom m2 n ((unknownCond, wod, notwod), (must, notmust))  = ((unknownCond', wod ∪ wodNew, notwod ∪ notwodNew), ( must ⊔ mustNew, notmust ⊔ notmustNew))
          where (pdom, dom) = ndoms ! n 
                unknownCond' = unknownCond ∖ (wodNew ∪ notwodNew)
                wodNew       = Set.fromList [ c | c <- Set.toList unknownCond, (∀) (suc graph c) (\x -> m2 ∈ pdom ! x), (∃) ms (\m1 -> not $ m1 ∈ (∏) [ pdom ! x |  x <- suc graph c ]) ]
                notwodNew    = Set.fromList [ c | c <- Set.toList unknownCond, (∀) (suc graph c) (\x -> m2 ∈ pdom ! x), (∀) ms (\m1 ->       m1 ∈ (∏) [ pdom ! x |  x <- suc graph c ]) ]
                mustNew      = Map.fromList [ (x, Set.fromList [ m1 |  m1 <- Set.toList $ pdom ! x, not $ m1 ∈ pdom ! m2, m1 ∈ ms ])  | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]
                notmustNew   = Map.fromList [ (x, notmusts)                                                                           | c <- Set.toList unknownCond', x <- suc graph c, m2 ∈ pdom ! x]
                  where notmusts = pdom ! m2  ∩  ms
