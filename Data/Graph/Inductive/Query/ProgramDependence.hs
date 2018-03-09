{-# LANGUAGE NamedFieldPuns #-}

module Data.Graph.Inductive.Query.ProgramDependence where



import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.TransClos

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

import Data.Maybe (fromJust)

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
        initialWorkSet   = Set.fromList [ (source, formalOut)                   | formalOut <- formalOuts, (source, edge) <- lpre graph formalOut, isIntra edge]
        initialReached   = Map.fromList [ (formalOut, Set.fromList [formalOut]) | formalOut <- formalOuts ]
        initialAoPaths   = Map.fromList [ (actualOut, Set.empty)                | actualOut <- actualOuts ]
        initialSummaries = Set.empty
        formalOuts = [ formalOut | formalOut <- nodes graph, Just (FormalOut _)     <- [lab graph formalOut]]
        actualOuts = [ actualOut | actualOut <- nodes graph, Just (ActualOut  _ _ ) <- [lab graph actualOut]]


type SummaryEdge = (Node, Node)
summaryComputation :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> Set (Node, Node) -> Map Node (Set Node) -> Map Node (Set Node) -> Set SummaryEdge -> Set SummaryEdge
summaryComputation parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor })
                   graph
                   workSet
                   reached
                   aoPaths
                   summaries
    | Set.null workSet = summaries
    | otherwise =
        if (source ∈ (reached ! formalOut)) then
          summaryComputation parameterMaps graph (workSet' ∪ newIntraWorklistEdgesViaSummaries                                                    ) reached                aoPaths                summaries
        else
          summaryComputation parameterMaps graph (workSet' ∪ newIntraWorklistEdgesViaSummaries ∪ newIntraWorklistEdges  ∪ newSummaryWorklistEdges) (reached ⊔ newReached) (aoPaths ⊔ newAoPaths) (summaries ∪ newSummaries)
  where ((source, formalOut), workSet') = Set.deleteFindMin workSet
        newReached = Map.fromList [ (formalOut, Set.fromList [source])]
        newAoPaths = case lab graph source of
            Just (ActualOut _ _) -> Map.fromList [ (source, Set.fromList [formalOut]) ]
            _                    -> Map.empty
        newIntraWorklistEdges             = Set.fromList [ (source', formalOut) | (source', edge) <- lpre graph source, isIntra edge]
        newIntraWorklistEdgesViaSummaries = case lab graph source of
            Just (ActualOut _ _) -> Set.fromList [ (source', formalOut) | (source', actualOut') <- Set.toList summaries, actualOut' == actualOut] -- TODO: performance
            _                    -> Set.empty
          where actualOut = source
        (newSummaries, newSummaryWorklistEdges) = case lab graph source of
            Just (FormalIn _) -> lop2sol $ 
                                 [ ((actualIn, actualOut),   [(actualIn, formalOut') | formalOut' <- Set.toList $ aoPaths ! actualOut ])
                                 | actualIn  <- Set.toList $ actualInsFor  ! formalIn,  Just (ActualIn  _ call ) <- [lab graph actualIn],
                                   actualOut <- Set.toList $ actualOutsFor ! formalOut, Just (ActualOut _ call') <- [lab graph actualOut],
                                   call == call' -- TODO: performance
                                 ]
            _                 -> (Set.empty, Set.empty)
          where formalIn = source
                lop2sol [] = (Set.empty, Set.empty)
                lop2sol ((a,b):xs) = (Set.insert a as, (Set.fromList b) ⊔ bs)
                  where (as,bs) = lop2sol xs



addSummaryEdgesLfp :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> gr SDGNode Dependence
addSummaryEdgesLfp parameterMaps graph =
      insEdges [ (actualIn, actualOut,  SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries]
    $ graph
  where summaries = (㎲⊒) (Set.empty) (summaryComputationF parameterMaps intraOnly)
        intraOnly = efilter (\(n, m, e) -> isIntra e) graph

summaryComputationF :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> Set SummaryEdge -> Set SummaryEdge
summaryComputationF parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor })
                    graph
                    summaries =
    assert ([ e | (n, m, e) <- labEdges graph, not $ isIntra e ] == []) $
    summaries
  ⊔ Set.fromList [ (actualIn, actualOut) | (formalIn, FormalIn _)  <- labNodes reachable,
                                           (formalOut, FormalOut _) <- [ (m, fromJust $ lab reachable m) | m <- suc reachable formalIn],
                                           actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab reachable actualIn],
                                           actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab reachable actualOut],
                                           call == call'
    ]
  where intraGraphWithSummaries = insEdges [ (actualIn, actualOut, SummaryDependence) | (actualIn, actualOut) <- Set.toList summaries ]
                                $ graph
        reachable = trc intraGraphWithSummaries



type SummaryIndependence = (Node, Node, ())


addSummaryEdgesGfpLfp :: DynGraph gr => Program gr -> ParameterMaps -> gr SDGNode Dependence -> gr SDGNode Dependence
addSummaryEdgesGfpLfp p
                      parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, parameterNodesFor })
                      graph
  =
      insEdges [ (actualIn, actualOut, SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries,
                                                             (ActualIn  x call ) <- [fromJust $ lab graph actualIn],  -- avoid duplicate edges
                                                             (ActualOut y call') <- [fromJust $ lab graph actualOut], --
                                                             assert (call == call') $ True,                           --
                                                             x /= y                                                   --
      ]
    $ insEdges (summaryIndependenciesToNonTrivialSummaryDependencies parameterMaps graph summaryIndependencies)
    $ graph
  where summaries = summariesGivenSummaryIndependencies summaryIndependencies
        summaryIndependencies =  (𝝂) (Set.fromList initialSummaryIndependencies) summaryIndependenciesF 
        intraOnly = efilter (\(n, m, e) -> isIntra e) graph

        summaryIndependenciesF :: Set SummaryIndependence -> Set SummaryIndependence
        summaryIndependenciesF summaryIndependencies = Set.fromList [ (actualIn, actualOut, ()) | (actualIn, actualOut, ()) <- Set.toList $ summaryIndependencies, not $ (actualIn, actualOut) ∈ summaries ]
          where summaries = summariesGivenSummaryIndependencies  summaryIndependencies

        summariesGivenSummaryIndependencies  :: Set SummaryIndependence -> Set SummaryEdge
        summariesGivenSummaryIndependencies summaryIndependencies = (㎲⊒) (Set.empty) (summaryComputationGivenSummaryIndependenciesF  parameterMaps intraOnly summaryIndependencies)
        initialSummaryIndependencies = [ (actualIn, actualOut, ()) | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                     (formalIn,  FormalIn  x ) <- [(n, fromJust $ lab graph n)],
                                                                     (formalOut, FormalOut x') <- [(m, fromJust $ lab graph m)],
                                                                     assert (x == x') $ True,
                                                                     actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab graph actualIn],
                                                                     actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab graph actualOut],
                                                                     call == call'
                                       ]
        (trivialDataIndependenceGraph, _) = trivialDataIndependenceGraphP p

summaryIndependenciesToNonTrivialSummaryDependencies  :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> Set SummaryIndependence -> [LEdge Dependence]
summaryIndependenciesToNonTrivialSummaryDependencies
          parameterMaps@(ParameterMaps { parameterNodesFor, trivialActualInFor })
          graph
          summaryIndependencies
  = [ (actualIn, actualOut, SummaryDependence) | (actualOut, actualIn) <- Map.assocs trivialActualInFor,
                                                 let (ActualIn  x  call ) = fromJust $ lab graph actualIn,
                                                 let (ActualOut x' call') = fromJust $ lab graph actualOut,
                                                 assert (call == call') $ True,
                                                 assert (x    == x'   ) $ True,
                                                 not $ (actualIn, actualOut, ()) ∈ summaryIndependencies
    ]

summaryComputationGivenSummaryIndependenciesF :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> Set SummaryIndependence -> Set SummaryEdge -> Set SummaryEdge
summaryComputationGivenSummaryIndependenciesF
                    parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, parameterNodesFor })
                    graph
                    summaryIndependencies
                    summaries =
    assert ([ e | (n, m, e) <- labEdges graph, not $ isIntra e ] == []) $
    summaries
  ⊔ Set.fromList [ (actualIn, actualOut) | (formalIn, FormalIn x)  <- labNodes reachable,
                                           (formalOut, FormalOut y) <- [ (m, fromJust $ lab reachable m) | m <- suc reachable formalIn],
                                           actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab reachable actualIn],
                                           actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab reachable actualOut],
                                           call == call'
    ]
  where intraGraphWithSummaries = insEdges [ (actualIn, actualOut, SummaryDependence) | (actualIn, actualOut) <- Set.toList summaries ]
                                $ insEdges (summaryIndependenciesToNonTrivialSummaryDependencies parameterMaps graph summaryIndependencies)
                                $ graph
        reachable = trc intraGraphWithSummaries


addSummaryEdgesGfpLfpWorkList :: DynGraph gr => Program gr -> ParameterMaps -> gr SDGNode Dependence -> gr SDGNode Dependence
addSummaryEdgesGfpLfpWorkList p
                      parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, parameterNodesFor })
                      graph
  =   insEdges [ (actualIn, actualOut,  SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries]
    $ insEdges (summaryIndependenciesToNonTrivialSummaryDependencies parameterMaps graph summaryIndependencies)
    $ graph
  where (summaries, summaryIndependencies) = summaryComputationGfpLfpWorkList parameterMaps graph initialWorkSet initialReached initialAoPaths initialSummaries initialSummaryIndependencies
        initialWorkSet   = Set.fromList [ (source, formalOut)                   | formalOut <- formalOuts, (source, edge) <- lpre graph formalOut, isIntra edge]
        initialReached   = Map.fromList [ (formalOut, Set.fromList [formalOut]) | formalOut <- formalOuts ]
        initialAoPaths   = Map.fromList [ (actualOut, Set.empty)                | actualOut <- actualOuts ]
        initialSummaries = Set.empty
        formalOuts = [ formalOut | formalOut <- nodes graph, Just (FormalOut _)     <- [lab graph formalOut]]
        actualOuts = [ actualOut | actualOut <- nodes graph, Just (ActualOut  _ _ ) <- [lab graph actualOut]]
        
        initialSummaryIndependencies = Set.fromList $ 
                                       [ (actualIn, actualOut, ()) | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                     (formalIn,  FormalIn  x ) <- [(n, fromJust $ lab graph n)],
                                                                     (formalOut, FormalOut x') <- [(m, fromJust $ lab graph m)],
                                                                     assert (x == x') $ True,
                                                                     actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab graph actualIn],
                                                                     actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab graph actualOut],
                                                                     call == call'
                                       ]
        (trivialDataIndependenceGraph, _) = trivialDataIndependenceGraphP p


summaryComputationGfpLfpWorkList :: DynGraph gr =>
                   ParameterMaps ->
                   gr SDGNode Dependence ->
                   Set (Node, Node) ->
                   Map Node (Set Node) ->
                   Map Node (Set Node) ->
                   Set SummaryEdge ->
                   Set SummaryIndependence ->
                   (Set SummaryEdge, Set SummaryIndependence)
summaryComputationGfpLfpWorkList parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, trivialActualInFor })
                   graph
                   workSet
                   reached
                   aoPaths
                   summaries
                   summaryindependencies
    | Set.null workSet = (summaries, summaryindependencies)
    | otherwise =
        if (source ∈ (reached ! formalOut)) then
          summaryComputationGfpLfpWorkList parameterMaps graph (workSet' ∪ newIntraWorklistEdgesViaSummaries                                                    ) reached                aoPaths                summaries summaryindependencies
        else
          summaryComputationGfpLfpWorkList parameterMaps graph (workSet' ∪ newIntraWorklistEdgesViaSummaries ∪ newIntraWorklistEdges  ∪ newSummaryWorklistEdges) (reached ⊔ newReached) (aoPaths ⊔ newAoPaths) (summaries ∪ newSummaries) (summaryindependencies ∖ lostIndependencies)
  where ((source, formalOut), workSet') = Set.deleteFindMin workSet
        newReached = Map.fromList [ (formalOut, Set.fromList [source])]
        newAoPaths = case lab graph source of
            Just (ActualOut _ _) -> Map.fromList [ (source, Set.fromList [formalOut]) ]
            _                    -> Map.empty
        newIntraWorklistEdges             = Set.fromList [ (source', formalOut) | (source', edge) <- lpre graph source, isIntra edge]
        newIntraWorklistEdgesViaSummaries = case lab graph source of
            Just (ActualOut _ _) ->   Set.fromList [ (actualIn, formalOut) | (actualIn, actualOut') <- Set.toList summaries, actualOut' == actualOut] -- TODO: performance
                                    ∪ Set.fromList [ (actualIn, formalOut) |  actualIn <- [ trivialActualInFor ! actualOut ], not $ (actualIn, actualOut,()) ∈ summaryindependencies ]
            _                    -> Set.empty
          where actualOut = source
        (newSummaries, lostIndependencies, newSummaryWorklistEdges) = case lab graph source of
            Just (FormalIn _) -> lop2sol $ 
                                 [ ([(actualIn, actualOut   )  | x /= x'],
                                    [(actualIn, actualOut,())  | x == x'],
                                    [(actualIn, formalOut')    | formalOut' <- Set.toList $ aoPaths ! actualOut ]
                                   )
                                 | actualIn  <- Set.toList $ actualInsFor  ! formalIn,  Just (ActualIn  x  call ) <- [lab graph actualIn],
                                   actualOut <- Set.toList $ actualOutsFor ! formalOut, Just (ActualOut x' call') <- [lab graph actualOut],
                                   call == call' -- TODO: performance
                                 ]
            _                 -> (Set.empty, Set.empty, Set.empty)
          where formalIn = source
                lop2sol [] = (Set.empty, Set.empty, Set.empty)
                lop2sol ((a,b,c):xs) = ((Set.fromList a) ⊔ as, (Set.fromList b) ⊔ bs, (Set.fromList c) ⊔ cs)
                  where (as,bs,cs) = lop2sol xs






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
