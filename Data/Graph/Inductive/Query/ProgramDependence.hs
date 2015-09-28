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
                                 [ controlDependenceGraph (cfg p thread)
                                                          (entryOf thread)
                                                          (false)
                                                          (exitOf thread)
                                 | thread <- Set.toList staticThreads ]
  where ddeps = dataDependenceGraphP p

concurrentProgramDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
concurrentProgramDependenceGraphP p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
    foldr mergeTwoGraphs empty $ [ tdeps, ddeps] ++
                                 [ controlDependenceGraph (cfg p thread)
                                                          (entryOf thread)
                                                          (false)
                                                          (exitOf thread)
                                 | thread <- Set.toList staticThreads ]
  where tdeps = interThreadDependenceGraphP p
        ddeps = dataDependenceGraphP p
