{-# LANGUAGE NamedFieldPuns #-}

module Data.Graph.Inductive.Query.ProgramDependence where



import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.Dependence

import Data.Set (Set)
import qualified Data.Set as Set


import IRLSOD
import Program

programDependenceGraph :: DynGraph gr => gr CFGNode CFGEdge -> Set Var -> Node -> CFGEdge -> Node -> gr CFGNode Dependence
programDependenceGraph graph vars entry label exit = mergeTwoGraphs cdeps ddeps
  where cdeps = controlDependenceGraph graph entry label exit
        ddeps = dataDependenceGraph    graph vars entry


programDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
programDependenceGraphP p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    foldr mergeTwoGraphs empty [ programDependenceGraph (nfilter (\node -> staticThreadOf node == thread) tcfg)
                                                        (vars p)
                                                        (entryOf thread)
                                                        (false)
                                                        (exitOf thread)
                                 | thread <- Set.toList staticThreads ]
