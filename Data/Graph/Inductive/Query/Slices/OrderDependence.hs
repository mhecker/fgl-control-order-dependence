module Data.Graph.Inductive.Query.Slices.OrderDependence where

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
import Data.Graph.Inductive.Query.OrderDependence (
    myDod, myDodFastPDom, dod,
    ntiod, ntiodFastPDom, ntiodFast, ntiodFastPDomSimpleHeuristic,
    wodTEIL'PDom, wodTEIL',
  )


ntscdMyDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdViaMDom graph
        d     = myDod graph

ntscdMyDodFastPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodFastPDomSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdViaMDom graph
        d     = myDodFastPDom graph


ntscdDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdViaMDom graph
        d     = dod graph


nticdMyWodSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiod graph


nticdMyWodFastSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodFastSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiodFast graph

nticdMyWodPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodPDomSimpleHeuristic graph =  combinedBackwardSlice graph nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiodFastPDomSimpleHeuristic graph

nticdMyWodPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodPDom graph =  combinedBackwardSlice graph nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiodFastPDom graph


wccSliceViaWodTEILPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaWodTEILPDom graph = \ms -> let fromMs = (Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m graph ]) in combinedBackwardSlice graph empty w ms ∩ fromMs
  where empty = Map.empty
        w     = wodTEIL'PDom graph

wccSliceViaNticdMyWodPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaNticdMyWodPDomSimpleHeuristic g ms = s ∩ fromMs
  where gRev = grev g
        g'   = subgraph (Set.toList toMs) g
        s    = nticdMyWodPDomSimpleHeuristic g' ms
        toMs   = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m gRev ]
        fromMs = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m g    ]

ntiodFastSlice :: ( DynGraph gr) => gr a b ->  Set Node  -> Set Node
ntiodFastSlice graph =  combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = ntiodFast graph


ntiodFastPDomSimpleHeuristicSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntiodFastPDomSimpleHeuristicSlice graph =  combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = ntiodFastPDomSimpleHeuristic graph

wodTEILSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSlice graph = combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = wodTEIL' graph

wodTEILPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILPDomSlice graph = combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = wodTEIL'PDom graph
