module Data.Graph.Inductive.Query.Slices.NTICD where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive


import Unicode
import Util(fromSet, invert'')

import Data.Graph.Inductive.Util (delSuccessorEdges)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import Data.Graph.Inductive.Query.NTICD (nticdViaSinkDom, ntscdViaMDom)

nticdSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = invert''  $ nticdViaSinkDom graph
        w     = Map.empty

ntscdSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdSlice graph =  combinedBackwardSlice graph ntscd w
  where ntscd = invert''  $ ntscdViaMDom graph
        w     = Map.empty


nticdMyWodSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSlice graph msS = combinedBackwardSlice graph nticd' empty msS
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        nticd' = invert'' $ nticdViaSinkDom graph'
        empty = Map.empty
