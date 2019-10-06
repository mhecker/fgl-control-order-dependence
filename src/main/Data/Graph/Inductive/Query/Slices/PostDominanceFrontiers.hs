module Data.Graph.Inductive.Query.Slices.PostDominanceFrontiers where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive


import Unicode
import Util(fromSet)

import Data.Graph.Inductive.Util (delSuccessorEdges)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (isinkDFTwoFinger, idomToDFFastForRoots, mDFTwoFinger)

nticdSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdSlice graph = combinedBackwardSlice nticd w
  where nticd = isinkDFTwoFinger graph
        w     = Map.empty

nticdSliceFor :: DynGraph gr => [[Node]] -> gr a b -> Map Node (Maybe Node) ->  Set Node -> Set Node
nticdSliceFor roots graph idom = {- traceShow (Map.fold (\ns sum -> sum + Set.size ns) 0 nticd') $ -} combinedBackwardSlice nticd' w
  where nticd' = idomToDFFastForRoots roots graph idom
        w      = Map.empty


ntscdSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdSlice graph = combinedBackwardSlice ntscd w
  where ntscd = mDFTwoFinger graph
        w     = Map.empty


nticdNTIODSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODSlice graph msS = combinedBackwardSlice nticd' empty msS
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        nticd' = isinkDFTwoFinger graph'
        empty = Map.empty

ntscdNTSODSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdNTSODSlice graph msS = combinedBackwardSlice ntscd' empty msS
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        ntscd' = mDFTwoFinger graph'
        empty = Map.empty

wodTEILSliceViaNticd :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSliceViaNticd g msS = combinedBackwardSlice nticd'' empty msS
  where ms = Set.toList msS
        g''   = foldr (flip delSuccessorEdges) g' ms
          where  toMs   = rdfs ms g
                 g' = subgraph toMs g
        nticd'' = isinkDFTwoFinger g''
        empty = Map.empty

