{-# LANGUAGE NamedFieldPuns #-}

module Data.Graph.Inductive.Query.ProgramDependence where



import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.InterThreadDependence

import Debug.Trace
import Control.Exception.Base (assert)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map ( Map, (!) )
import qualified Data.Map as Map

import Unicode
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


systemDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
systemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    addSummaryEdges parameterMaps $ 
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


concurrentSystemDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
concurrentSystemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    addSummaryEdges parameterMaps $ 
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


nonTrivialsystemDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
nonTrivialsystemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    addSummaryEdges parameterMaps $ 
    addParameterEdges  parameterMaps $
    insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
    foldr mergeTwoGraphs empty $ [ ddeps ] ++ 
                                 [ lift $
                                   insEdge (entry,exit, ControlDependence) $
                                   controlDependenceGraph (insEdge (entry, exit, false) $ cfgOfProcedure p procedure)
                                                          exit
                                 | procedure <- Set.toList staticProcedures, let entry = entryOf procedure, let exit = exitOf procedure ]
  where (ddeps, parameterMaps) = nonTrivialDataDependenceGraphP p
        lift = nmap CFGNode


concurrentNonTrivialSystemDependenceGraphP :: DynGraph gr => Program gr -> gr SDGNode Dependence
concurrentNonTrivialSystemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) =
    addSummaryEdges parameterMaps $ 
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
        (ddeps, parameterMaps) = nonTrivialDataDependenceGraphP p
        lift = nmap CFGNode





isIntra ControlDependence      = True
isIntra DataDependence         = True
isIntra SummaryDependence      = False
isIntra SpawnDependence        = False
isIntra InterThreadDependence  = False
isIntra ParameterInDependence  = False
isIntra ParameterOutDependence = False

addSummaryEdges :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> gr SDGNode Dependence
addSummaryEdges parameterMaps graph =
      insEdges [ (actualIn, actualOut,  SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries]
    $ graph
  where summaries = summaryComputation parameterMaps graph initialWorkSet initialReached initialAoPaths initialSummaries
        initialWorkSet   = Set.fromList [ (source, formalOut, edge)             | formalOut <- formalOuts, (source, edge) <- lpre graph formalOut, isIntra edge]
        initialReached   = Map.fromList [ (formalOut, Set.fromList [formalOut]) | formalOut <- formalOuts ]
        initialAoPaths   = Map.empty
        initialSummaries = Set.empty
        formalOuts = [ formalOut | formalOut <- nodes graph, Just (FormalOut _) <- [lab graph formalOut]]


type SummaryEdge = (Node, Node)
summaryComputation :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> Set (Node, Node, Dependence) -> Map Node (Set Node) -> Map Node (Set Node) -> Set SummaryEdge -> Set SummaryEdge
summaryComputation parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor })
                   graph
                   workSet
                   reached
                   aoPaths
                   summaries
    | Set.null workSet = summaries
    | otherwise = traceShow (workSet, summaries) $
                  assert (isIntra edge) $
        if (source ∈ (reached ! formalOut)) then
          summaryComputation parameterMaps graph  workSet'             reached aoPaths summaries
        else
          summaryComputation parameterMaps graph (workSet' ∪ newEdges) (reached ⊔ newReached) (aoPaths ⊔ newAoPaths) (summaries ∪ newSummaries)
  where ((source, formalOut, edge), workSet') = Set.deleteFindMin workSet
        newEdges   = Set.fromList [ (source', formalOut, edge') | (source', edge') <- lpre graph source, isIntra edge']
        newReached = Map.fromList [ (formalOut, Set.fromList [source])]
        newAoPaths = case lab graph source of
          Just (ActualOut _ _) -> Map.fromList [ (source, Set.fromList [formalOut]) ]
          _                    -> Map.empty
        newSummaries = case lab graph source of
          Just (FormalIn _) -> Set.fromList [ (actualIn, actualOut) | actualIn  <- Set.toList $ actualInsFor  ! formalIn,  Just (ActualIn  _ call ) <- [lab graph actualIn],
                                                                      actualOut <- Set.toList $ actualOutsFor ! formalOut, Just (ActualOut _ call') <- [lab graph actualOut],
                                                                      call == call' -- TODO: performance
                                         ]
          _                 -> Set.empty
          where formalIn = source


addNonTrivialSummaryEdges :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> gr SDGNode Dependence
addNonTrivialSummaryEdges parameterMaps graph =
      insEdges [ (actualIn, actualOut,  SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries]
    $ graph
  where summaries = summaryComputation parameterMaps graph initialWorkSet initialReached initialAoPaths initialSummaries
        initialWorkSet   = Set.fromList [ (source, formalOut, edge)             | formalOut <- formalOuts, (source, edge) <- lpre graph formalOut, isIntra edge]
        initialReached   = Map.fromList [ (formalOut, Set.fromList [formalOut]) | formalOut <- formalOuts ]
        initialAoPaths   = Map.empty
        initialSummaries = Set.empty
        formalOuts = [ formalOut | formalOut <- nodes graph, Just (FormalOut _) <- [lab graph formalOut]]

summaryComputationForIndependencies :: DynGraph gr =>
  ParameterMaps ->
  gr SDGNode Dependence ->
  gr SDGNode Independence -> 
  Set (Node, Node, Dependence) ->
  Map Node (Set Node) ->
  Map Node (Set Node) ->
  Set SummaryEdge ->
  Set SummaryEdge
summaryComputationForIndependencies parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor })
                   nonTrivialSystemDependenceGraph
                   trivialDataIndependenceGraph
                   workSet
                   reached
                   aoPaths
                   summaries
    | Set.null workSet = summaries
    | otherwise = traceShow (workSet, summaries) $
                  assert (isIntra edge) $
        if (source ∈ (reached ! formalOut)) then
          summaryComputation parameterMaps nonTrivialSystemDependenceGraph  workSet'             reached aoPaths summaries
        else
          summaryComputation parameterMaps nonTrivialSystemDependenceGraph (workSet' ∪ newEdges) (reached ⊔ newReached) (aoPaths ⊔ newAoPaths) (summaries ∪ newSummaries)
  where ((source, formalOut, edge), workSet') = Set.deleteFindMin workSet
        newEdges   = Set.fromList [ (source', formalOut, edge') | (source', edge') <- lpre nonTrivialSystemDependenceGraph source, isIntra edge']
        newReached = Map.fromList [ (formalOut, Set.fromList [source])]
        newAoPaths = case lab nonTrivialSystemDependenceGraph source of
          Just (ActualOut _ _) -> Map.fromList [ (source, Set.fromList [formalOut]) ]
          _                    -> Map.empty
        newSummaries = case lab nonTrivialSystemDependenceGraph source of
          Just (FormalIn _) -> Set.fromList [ (actualIn, actualOut) | actualIn  <- Set.toList $ actualInsFor  ! formalIn,  Just (ActualIn  _ call ) <- [lab nonTrivialSystemDependenceGraph actualIn],
                                                                      actualOut <- Set.toList $ actualOutsFor ! formalOut, Just (ActualOut _ call') <- [lab nonTrivialSystemDependenceGraph actualOut],
                                                                      call == call' -- TODO: performance
                                         ]
          _                 -> Set.empty
          where formalIn = source






slice :: Graph gr => gr SDGNode Dependence -> (Dependence -> Bool) -> Set Node -> Set Node
slice graph follow nodes = (㎲⊒) nodes f
  where f nodes = nodes ∪ (Set.fromList [ m | n <- Set.toList nodes, (m,e) <- lpre graph n, follow e])

systemDependenceGraphSlice ::  Graph gr => gr SDGNode Dependence -> Set Node -> Set Node
systemDependenceGraphSlice graph s0 = s2
  where s1 = slice graph follow1 s0
        s2 = slice graph follow2 s1

        follow1 ControlDependence      = True
        follow1 DataDependence         = True
        follow1 CallDependence         = True
        follow1 SummaryDependence      = True
        follow1 SpawnDependence        = True
        follow1 InterThreadDependence  = True
        follow1 ParameterInDependence  = True
        follow1 ParameterOutDependence = False

        follow2 ControlDependence      = True
        follow2 DataDependence         = True
        follow2 CallDependence         = False
        follow2 SummaryDependence      = True
        follow2 SpawnDependence        = True
        follow2 InterThreadDependence  = True
        follow2 ParameterInDependence  = False
        follow2 ParameterOutDependence = True
