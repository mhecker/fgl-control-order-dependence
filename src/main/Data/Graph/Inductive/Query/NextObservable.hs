{-# LANGUAGE CPP #-}
module Data.Graph.Inductive.Query.NextObservable where

#define require assert

import Control.Exception.Base (assert)


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS (scc, dfs)
import Data.Graph.Inductive.Query.Dominators (dom)

import Unicode
import Data.Graph.Inductive.Util (delSuccessorEdges)


nextObservableFor :: Graph gr => gr a b -> Set Node -> Node -> Set Node
nextObservableFor g' s n = Set.fromList (dfs [n] g') ∩ s


nextObservable :: DynGraph gr => gr a b -> Set Node -> Node -> Set Node
nextObservable g s n = nextObservableFor g' s n 
  where g' = Set.fold (flip delSuccessorEdges) g s



retainsNextObservableFor :: Graph gr => gr a b -> Set Node -> Node -> [Node] -> Bool
retainsNextObservableFor g' s n n's =
    require (not $ n ∈ s) $ (∀) (n's) (\n' -> let obsN' = nextObservableFor g' s n' in obsN == obsN')
  where obsN = nextObservableFor g' s n 

retainsNextObservable :: DynGraph gr => gr a b -> Set Node -> Node -> Bool
retainsNextObservable g s n = retainsNextObservableFor g' s n (suc g n)
  where g' = Set.fold (flip delSuccessorEdges) g s
        obsN = nextObservableFor g' s n 


retainsNextObservableOutside :: DynGraph gr => gr a b -> Set Node -> Bool
retainsNextObservableOutside g s = (∀) (Set.fromList (nodes g) ∖ s) (\n -> retainsNextObservableFor g' s n (suc g n))
  where g' = Set.fold (flip delSuccessorEdges) g s




weaklyControlClosedFor :: Graph gr => gr a b -> Set Node -> Node -> Bool
weaklyControlClosedFor g' s n =
    require (not $ n ∈ s) $ Set.size obsN <= 1
  where obsN = nextObservableFor g' s n 

weaklyControlClosed :: DynGraph gr => gr a b -> Set Node -> Bool
weaklyControlClosed g s = (∀) (Set.fromList (nodes g) ∖ s) (\n -> weaklyControlClosedFor g' s n)
  where g' = Set.fold (flip delSuccessorEdges) g s
