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

import Data.Map ( Map, (!) )
import qualified Data.Map as Map


import IRLSOD
import Program

programDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
programDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    addParameterEdges  parameterMaps $
    insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
    foldr mergeTwoGraphs empty $ [ ddeps ] ++ 
                                 [ lift $
                                   insEdge (entry,exit, ControlDependence) $
                                   controlDependenceGraph (insEdge (entry, exit, false) $ cfgOfProcedure p procedure)
                                                          exit
                                 | procedure <- Set.toList staticProcedures, let entry = entryOf procedure, let exit = exitOf procedure ]
  where (ddeps, parameterMaps) = dataDependenceGraphP p
        lift = nmap CFGNode

concurrentProgramDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
concurrentProgramDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    addParameterEdges  parameterMaps $
    insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
    foldr mergeTwoGraphs empty $ [ ddeps] ++
                                 [ lift tdeps ] ++
                                 [ lift $ 
                                   insEdge (entry,exit, ControlDependence) $
                                   controlDependenceGraph (insEdge (entry, exit, false) $ cfgOfProcedure p procedure)
                                                          exit
                                 | procedure <- Set.toList staticProcedures, let entry = entryOf procedure, let exit = exitOf procedure ]
  where tdeps = interThreadDependenceGraphP p
        (ddeps, parameterMaps) = dataDependenceGraphP p
        lift = nmap CFGNode


addParameterEdges :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> gr SDGNode Dependence
addParameterEdges (ParameterMaps { formalInFor, formalOutFor, actualInsFor, actualOutsFor }) graph =
      insEdges [ (actualIn, formalIn,   ParameterInDependence)  | (actualIn, formalIn)   <- Map.assocs formalInFor ]
    $ insEdges [ (formalOut, actualOut, ParameterOutDependence) | (actualOut, formalOut) <- Map.assocs formalOutFor ]
    $ graph

-- systemDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
-- systemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
--     insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
--     foldr mergeTwoGraphs empty $ [ ddeps ] ++ 
--                                  [ lift $
--                                    insEdge (entry,exit, ControlDependence) $
--                                    controlDependenceGraph (insEdge (entry, exit, false) $ cfgOfProcedure p procedure)
--                                                           exit
--                                  | procedure <- Set.toList staticProcedures, let entry = entryOf procedure, let exit = exitOf procedure ]
--   where pdg = programDependenceGraphP p
--         formalInFor (n, ActualIN v) = find pdg n
--           where follow (_, Use _) = True
--                 follow (_, Call ) = True
--         lift = nmap CFGNode






-- systemDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
-- systemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
--     insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
--     foldr mergeTwoGraphs empty $ [ pdg ] ++ 
--                                  [ insEdge (entry,exit, ControlDependence) $
--                                    insNode (
--                                    controlDependenceGraph (insEdge (entry, exit, false) $ cfgOfProcedure p procedure)
--                                                           exit
--                                  | procedure <- Set.toList staticProcedures, let entry = entryOf procedure, let exit = exitOf procedure
--                                    var <- vars p
--                                  ]
--   where pdg = nmap CFGNode (programDependenceGraph p)

-- concurrentSystemDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
-- concurrentSystemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
--     insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
--     foldr mergeTwoGraphs empty $ [ tdeps, ddeps] ++
--                                  [ insEdge (entry,exit, ControlDependence) $
--                                    controlDependenceGraph (insEdge (entry, exit, false) $ cfgOfProcedure p procedure)
--                                                           exit
--                                  | procedure <- Set.toList staticProcedures, let entry = entryOf procedure, let exit = exitOf procedure ]
--   where tdeps = interThreadDependenceGraphP p
--         ddeps = dataDependenceGraphP p
