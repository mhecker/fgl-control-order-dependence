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
    ntsod, ntsodFastPDom, dod,
    ntiod, ntiodFastPDom, ntiodFast, ntiodFastPDomSimpleHeuristic,
    wodTEIL'PDom, wodTEIL',
  )


ntscdNTSODSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdNTSODSlice graph = combinedBackwardSlice ntscd d
  where ntscd = invert'' $ ntscdViaMDom graph
        d     = ntsod graph

ntscdNTSODFastPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdNTSODFastPDomSlice graph = combinedBackwardSlice ntscd d
  where ntscd = invert'' $ ntscdViaMDom graph
        d     = ntsodFastPDom graph


ntscdDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdDodSlice graph = combinedBackwardSlice ntscd d
  where ntscd = invert'' $ ntscdViaMDom graph
        d     = dod graph


nticdNTIODSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODSlice graph = combinedBackwardSlice nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiod graph


nticdNTIODFastSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODFastSlice graph = combinedBackwardSlice nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiodFast graph

nticdNTIODPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODPDomSimpleHeuristic graph = combinedBackwardSlice nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiodFastPDomSimpleHeuristic graph

nticdNTIODPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODPDom graph = combinedBackwardSlice nticd w
  where nticd = invert'' $ nticdViaSinkDom graph
        w     = ntiodFastPDom graph


wccSliceViaWodTEILPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaWodTEILPDom graph = \ms -> let fromMs = (Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m graph ]) in combinedBackwardSlice empty w ms ∩ fromMs
  where empty = Map.empty
        w     = wodTEIL'PDom graph

wccSliceViaNticdNTIODPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaNticdNTIODPDomSimpleHeuristic g ms = s ∩ fromMs
  where gRev = grev g
        g'   = subgraph (Set.toList toMs) g
        s    = nticdNTIODPDomSimpleHeuristic g' ms
        toMs   = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m gRev ]
        fromMs = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m g    ]

ntiodFastSlice :: ( DynGraph gr) => gr a b ->  Set Node  -> Set Node
ntiodFastSlice graph = combinedBackwardSlice empty w
  where empty = Map.empty
        w     = ntiodFast graph


ntiodFastPDomSimpleHeuristicSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntiodFastPDomSimpleHeuristicSlice graph = combinedBackwardSlice empty w
  where empty = Map.empty
        w     = ntiodFastPDomSimpleHeuristic graph

wodTEILSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSlice graph = combinedBackwardSlice empty w
  where empty = Map.empty
        w     = wodTEIL' graph

wodTEILPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILPDomSlice graph = combinedBackwardSlice empty w
  where empty = Map.empty
        w     = wodTEIL'PDom graph
