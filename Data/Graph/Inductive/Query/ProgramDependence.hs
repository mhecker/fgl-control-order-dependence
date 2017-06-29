{-# LANGUAGE NamedFieldPuns #-}

module Data.Graph.Inductive.Query.ProgramDependence where



import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.InterThreadDependence

import Data.Set (Set)
import qualified Data.Set as Set


import IRLSOD
import Program


programDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
programDependenceGraphP p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
    foldr mergeTwoGraphs empty $ [ ddeps ] ++ 
                                 [ insEdge (entry,exit, ControlDependence) $
                                   controlDependenceGraph (insEdge (entry, exit, false) $ cfg p thread)
                                                          exit
                                 | thread <- Set.toList staticThreads, let entry = entryOf thread, let exit = exitOf thread ]
  where ddeps = dataDependenceGraphP p

concurrentProgramDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
concurrentProgramDependenceGraphP p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
    foldr mergeTwoGraphs empty $ [ tdeps, ddeps] ++
                                 [ insEdge (entry,exit, ControlDependence) $
                                   controlDependenceGraph (insEdge (entry, exit, false) $ cfg p thread)
                                                          exit
                                 | thread <- Set.toList staticThreads, let entry = entryOf thread, let exit = exitOf thread ]
  where tdeps = interThreadDependenceGraphP p
        ddeps = dataDependenceGraphP p
