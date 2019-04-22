{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
module Data.Graph.Inductive.Query.NTICD.Util where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic (efilter)


import Unicode
import IRLSOD(CFGNode, CFGEdge(..), isIntraCFGEdge, false)
import Program (Program (..))

import Data.Graph.Inductive.Util (mergeTwoGraphs)
import Data.Graph.Inductive.Query.Dependence (Dependence(..))




{- Generic utility functions -}
cdepGraphP :: DynGraph gr => (gr CFGNode CFGEdge -> gr CFGNode Dependence) -> Program gr -> gr CFGNode Dependence 
cdepGraphP graphGen  p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    foldr mergeTwoGraphs callDependenceGraph
                               [ insEdge (entry, exit, ControlDependence) $ 
                                 graphGen (insEdge (entry, exit, false) $ nfilter (\node -> staticProcedureOf node == procedure)
                                                                        $ efilter (\(_,_,l) -> isIntraCFGEdge l)
                                                                        $ tcfg
                                          )
                               | procedure <- Set.toList staticProcedures,  let entry = entryOf procedure, let exit = exitOf procedure ]
  where callDependenceGraph = mkGraph (labNodes tcfg) [ (call, entry, CallDependence) | (call, entry, Call) <- labEdges tcfg]
        
cdepGraph :: DynGraph gr => (gr a b -> Map Node (Set Node)) -> gr a b -> gr a Dependence
cdepGraph cdGen graph  = mkGraph (labNodes graph) [ (n,n',ControlDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = cdGen graph



combinedBackwardSliceSlow :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map (Node, Node) (Set Node) -> Set Node -> Set Node
combinedBackwardSliceSlow graph cd od = \ms -> (㎲⊒) ms f
  where f slice = slice
                ⊔ Set.fromList [ n | m <- Set.toList slice, n <- Set.toList $ cd ! m ]
                ⊔ Set.fromList [ n | m1 <- Set.toList slice, m2 <- Set.toList slice, m1 /= m2, n <- Set.toList $ Map.findWithDefault Set.empty (m1,m2) od ]

combinedBackwardSlice :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map (Node, Node) (Set Node) -> Set Node -> Set Node
combinedBackwardSlice graph cd od = \ms ->
     let result = slice Set.empty ms 
         slice s workset
             | Set.null workset = s
             | otherwise        = slice s' workset'
           where (m, workset0) = Set.deleteFindMin workset
                 s'  = Set.insert m s
                 new = (fromOD ∪ fromCD) ∖ s'
                 workset' = workset0 ∪ new

                 fromCD = Map.findWithDefault Set.empty m cd
                 fromOD
                   | Map.null od  = Set.empty
                   | otherwise    = (∐) [ (Map.findWithDefault Set.empty (m,m') od ) ∪ (Map.findWithDefault Set.empty (m', m) od) | m' <- Set.toList s ]
     in result
