{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
module Data.Graph.Inductive.Query.NTICD.Util where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic (efilter)


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

