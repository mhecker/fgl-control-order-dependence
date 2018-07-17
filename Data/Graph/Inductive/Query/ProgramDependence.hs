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

import Algebra.Lattice

import Debug.Trace
import Control.Exception.Base (assert)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Map ( Map, (!) )
import qualified Data.Map as Map

import qualified Data.List as List

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

concurrentProgramDependenceGraphP :: DynGraph gr => Program gr -> Set (Node,Node) -> gr SDGNode Dependence
concurrentProgramDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) mhp =
    addParameterEdges  parameterMaps $
    insEdges [ (n,n',SpawnDependence) | (n,n',Spawn) <- labEdges tcfg ] $
    foldr mergeTwoGraphs empty $ [ ddeps] ++
                                 [ lift tdeps ] ++
                                 [ lift $ 
                                   insEdge (entry,exit, ControlDependence) $
                                   controlDependenceGraph (insEdge (entry, exit, false) $ cfgOfProcedure p procedure)
                                                          exit
                                 | procedure <- Set.toList staticProcedures, let entry = entryOf procedure, let exit = exitOf procedure ]
  where tdeps = interThreadDependenceGraphP p mhp
        (ddeps, parameterMaps) = dataDependenceGraphP p
        lift = nmap CFGNode


addParameterEdges :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> gr SDGNode Dependence
addParameterEdges (ParameterMaps { formalInFor, formalOutFor, formalInForSpawnIn }) graph =
      insEdges [ (actualIn, formalIn,   ParameterInDependence)  | (actualIn, formalIn)   <- Map.assocs formalInFor ]
    $ insEdges [ (formalOut, actualOut, ParameterOutDependence) | (actualOut, formalOut) <- Map.assocs formalOutFor ]
    $ insEdges [ (spawnIn, formalIn,    SpawnInDepdendence)     | (spawnIn, formalIn) <- Map.assocs formalInForSpawnIn ]
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


concurrentSystemDependenceGraphP :: DynGraph gr => Program gr -> Set (Node,Node) -> gr SDGNode Dependence
concurrentSystemDependenceGraphP p@(Program { tcfg, staticProcedureOf, staticProcedures, entryOf, exitOf }) mhp =
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
  where tdeps = interThreadDependenceGraphP p mhp
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
          summaryComputation parameterMaps graph (workSet'                                                                                        ) reached                aoPaths                summaries
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
type FormalInActualInIndependence = (Node, Node, (),())
type ActualOutFormalOutIndependence = (Node, Node, (),(),())


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
  where (summaries, summaryIndependencies, _, _) = summaryComputationGfpLfpWorkList parameterMaps graph initialWorkSet initialReached initialAoPaths initialSummaries initialSummaryIndependencies initialformalInActualInIndependencies actualOutFormalOutIndependencies
        initialWorkSet   = Set.fromList [ (source, formalOut)                   | formalOut <- formalOuts,
                                                                                  (source, edge) <- lpre graph formalOut,
                                                                                  isIntra edge
                           ]
                         ⊔ Set.fromList [ (source, actualIn)                    | actualIn  <- relevantActualIns,
                                                                                  (source, edge) <- lpre graph actualIn,
                                                                                  isIntra edge
                           ]

        initialReached   = Map.fromList [ (formalOut, Set.fromList [formalOut]) | formalOut <- formalOuts ]
                         ⊔ Map.fromList [ (actualIn,  Set.fromList [actualIn])  | actualIn  <- relevantActualIns ]
        initialAoPaths   = Map.fromList [ (actualOut, Set.empty)                | actualOut <- actualOuts ]
        initialSummaries = Set.empty
        formalOuts = [ formalOut | formalOut <- nodes graph, Just (FormalOut _)     <- [lab graph formalOut]]
        actualOuts = [ actualOut | actualOut <- nodes graph, Just (ActualOut  _ _ ) <- [lab graph actualOut]]
        actualIns  = [ actualIn  | actualIn  <- nodes graph, Just (ActualIn   _ _ ) <- [lab graph actualIn]]

        relevantActualIns =
                     [ actualIn  | actualIn  <- actualIns, not $ List.null $ lpre trivialDataIndependenceGraph actualIn ]
        
        initialSummaryIndependencies = Set.fromList $ 
                                       [ (actualIn, actualOut, ())        | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (formalIn,  FormalIn  x ) <- [(n, fromJust $ lab graph n)],
                                                                            (formalOut, FormalOut x') <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True,
                                                                            actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab graph actualIn],
                                                                            actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab graph actualOut],
                                                                            call == call'
                                       ]
        initialformalInActualInIndependencies = Set.fromList $ 
                                       [ (formalIn, actualIn, (),())      | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (formalIn, FormalIn  x )   <- [(n, fromJust $ lab graph n)],
                                                                            (actualIn, ActualIn  x' _) <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True
                                       ]
        actualOutFormalOutIndependencies = Set.fromList $ 
                                       [ (actualOut, formalOut, (),(),()) | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (actualOut, ActualOut  x  _) <- [(n, fromJust $ lab graph n)],
                                                                            (formalOut, FormalOut  x')   <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True
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
                   Set FormalInActualInIndependence ->
                   Set ActualOutFormalOutIndependence ->
                   (Set SummaryEdge, Set SummaryIndependence, Set FormalInActualInIndependence , Set ActualOutFormalOutIndependence)
summaryComputationGfpLfpWorkList
                   parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, trivialActualInFor })
                   graph
                   workSet
                   reached
                   aoPaths
                   summaries
                   summaryindependencies
                   formalInActualInInIndependencies
                   actualOutFormalOutIndependencies
    | Set.null workSet = (summaries, summaryindependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)
    | otherwise =
        if (source ∈ (reached ! target)) then
          summaryComputationGfpLfpWorkList parameterMaps graph (workSet' ∪ newIntraWorklistEdgesViaIndependencies                                                   )  reached                aoPaths                 summaries                  summaryindependencies                         formalInActualInInIndependencies              actualOutFormalOutIndependencies
        else
          summaryComputationGfpLfpWorkList parameterMaps graph (workSet' ∪ newIntraWorklistEdgesViaIndependencies ∪ newIntraWorklistEdges  ∪ newSummaryWorklistEdges) (reached ⊔ newReached) (aoPaths ⊔ newAoPaths) (summaries ∪ newSummaries) (summaryindependencies ∖ lostIndependencies)  (formalInActualInInIndependencies ∖ lostFiAi) (actualOutFormalOutIndependencies ∖ lostAoFo)
  where ((source, target), workSet') = Set.deleteFindMin workSet
        newReached = Map.fromList [ (target, Set.fromList [source])]
        newAoPaths = case lab graph source of
            Just (ActualOut _ _) -> Map.fromList [ (source, Set.fromList [target])]
            _                    -> Map.empty
        newIntraWorklistEdges             = Set.fromList [ (source', target) | (source', edge) <- lpre graph source, isIntra edge]
        newIntraWorklistEdgesViaIndependencies = case lab graph source of
            Just (ActualOut _ _) ->   -- Set.empty
                                      Set.fromList [ (actualIn, target) | (actualIn, actualOut') <- Set.toList summaries, actualOut' == actualOut] -- TODO: performance
                                    ∪ Set.fromList [ (actualIn, target) |  actualIn <- [ trivialActualInFor  ! actualOut ], not $ (actualIn, actualOut, ())   ∈ summaryindependencies ]
              where actualOut = source
            _                    ->   Set.empty
        lostAoFo = case (lab graph source, lab graph target) of
            (Just (ActualOut x _), Just (FormalOut x' )) -> Set.fromList [ (actualOut, formalOut, (), (), ()) | x == x']
              where actualOut = source
                    formalOut = target
            _                    -> Set.empty
        lostFiAi = case (lab graph source, lab graph target) of 
            (Just (FormalIn x), Just (ActualIn x' _))    -> Set.fromList [ (formalIn,  actualIn,  (), ()    ) | x == x']
              where formalIn  = source
                    actualIn  = target
            _                    -> Set.empty
        (newSummaries, lostIndependencies, newSummaryWorklistEdges) = case (lab graph source, lab graph target) of
            (Just (FormalIn _), Just (FormalOut _)) -> lop2sol $ 
                                 [ ([(actualIn, actualOut   )  | x /= x'],
                                    [(actualIn, actualOut,())  | x == x'],
                                    [(actualIn, formalOut')    | formalOut' <- Set.toList $ aoPaths ! actualOut]
                                   )
                                 | actualIn  <- Set.toList $ actualInsFor  ! formalIn,  Just (ActualIn  x  call ) <- [lab graph actualIn],
                                   actualOut <- Set.toList $ actualOutsFor ! formalOut, Just (ActualOut x' call') <- [lab graph actualOut],
                                   call == call' -- TODO: performance
                                 ]
            _                 -> (Set.empty, Set.empty, Set.empty)
          where formalIn = source
                formalOut = target
                lop2sol [] = (Set.empty, Set.empty, Set.empty)
                lop2sol ((a,b,c):xs) = ((Set.fromList a) ⊔ as, (Set.fromList b) ⊔ bs, (Set.fromList c) ⊔ cs)
                  where (as,bs,cs) = lop2sol xs



data CallGraphEdge = Calls | IncludesCallSite deriving (Ord, Eq, Show)
data CallGraphNode =  Procedure (Node, Node) | CallSite (Node, Node) deriving (Ord, Eq, Show)
  
callGraph :: Graph gr => Program gr ->  (gr CallGraphNode CallGraphEdge, Map CallGraphNode Node)
callGraph p@(Program { tcfg, entryOf, exitOf, staticProcedures, staticProcedureOf })  = (mkGraph nodes edges, nodeMap)
  where nodes' =
             [ CallSite (call, return)    | (call, return, CallSummary) <- labEdges tcfg ]
         ++  [ Procedure (entryOf procedure, exitOf procedure)  | procedure <- Set.toList $ staticProcedures ]
        nodeMap = Map.fromList $ zip nodes' [1..]
        nodes = [ (n, l) | (l,n) <- Map.assocs nodeMap]

        edges =    [ (nodeMap ! (CallSite (call, return))               , nodeMap ! (Procedure (entryOf proc, exitOf proc)), Calls) | (call, return, CallSummary) <- labEdges tcfg,
                                                                                                                                       (entry, Call) <- lsuc tcfg call,
                                                                                                                                       let proc = staticProcedureOf entry,
                                                                                                                                       assert (exitOf proc `elem` (pre tcfg return)) True
                   ]
                ++ [ (nodeMap ! ( Procedure (entryOf proc, exitOf proc)), nodeMap ! (CallSite (call, return)), IncludesCallSite)     | (call, return, CallSummary) <- labEdges tcfg,
                                                                                                                                        let proc = staticProcedureOf call
                   ]

callGraphGivenIndeps :: DynGraph gr => Var -> Var ->  gr CallGraphNode CallGraphEdge -> Map CallGraphNode Node -> gr SDGNode Independence ->  ParameterMaps -> gr CallGraphNode CallGraphEdge
callGraphGivenIndeps x y cg cgNodeMap trivialDataIndependenceGraph parameterMaps@(ParameterMaps { parameterNodesFor }) = efilter f cg
                                     where f (_,_, Calls) = True
                                           f (n,m, IncludesCallSite) = case (fromJust $ lab cg n, fromJust $ lab cg m) of
                                             (Procedure (entry', exit'), CallSite (call', return')) ->
                                               let formals = Set.toList $ parameterNodesFor ! (entry', exit')
                                                   actuals = Set.toList $ parameterNodesFor ! (call', return')
                                                   [formalOut'] = [ formal | formal <- Set.toList $ parameterNodesFor ! (entry', exit'),
                                                                                       FormalOut y' <- [ fromJust $ lab trivialDataIndependenceGraph formal],
                                                                                       y' == y
                                                                  ]
                                                   [formalIn']  = [ formal | formal <- Set.toList $ parameterNodesFor ! (entry', exit'),
                                                                                       FormalIn  x' <- [ fromJust $ lab trivialDataIndependenceGraph formal],
                                                                                       x' == x
                                                                  ]
                                                   [actualOut'] = [ actual | actual <- Set.toList $ parameterNodesFor ! (call', return'),
                                                                                       ActualOut y' (call'', return'') <- [ fromJust $ lab trivialDataIndependenceGraph actual],
                                                                                       assert (call'' == call'  ∧  return'' == return') True,
                                                                                       y' == y
                                                                  ]
                                                   [actualIn']  = [ actual | actual <- Set.toList $ parameterNodesFor ! (call', return'),
                                                                                       ActualIn  x' (call'', return'') <- [ fromJust $ lab trivialDataIndependenceGraph actual],
                                                                                       assert (call'' == call'  ∧  return'' == return') True,
                                                                                       x' == x
                                                                  ]
                                               in not $    (formalIn',  actualIn',  DataIndependence) `elem` labEdges trivialDataIndependenceGraph
                                                        || (actualOut', formalOut', DataIndependence) `elem` labEdges trivialDataIndependenceGraph
                                             _                                      -> undefined

-- summaryIndepsProperty :: DynGraph gr => Program gr -> Bool
summaryIndepsPropertyViolations :: DynGraph gr => Program gr -> [ ((Node, SDGNode), (Node, SDGNode)) ]
summaryIndepsPropertyViolations p = [ ((actualIn, ActualIn x (call, return)), (actualOut, ActualOut y (call, return))) | se@((actualIn, ActualIn x (call, return)), (actualOut, ActualOut y _)) <- summaries,
                            -- traceShow () $
                            -- traceShow ("SummaryEdge: ", se) $
                            let cg'Trc = trc cg'
                                cg' = callGraphGivenIndepsFor x y
                                expectedSummariesAt = [ (n, CallSite (call', return')) | n <- pre cg'Trc (cgNodeMap ! (CallSite (call, return))),   CallSite (call', return') <- [ fromJust $ lab cg'Trc n ] ]
                                possibleSummariesAt = [ (n, CallSite (call', return')) | n <- pre cgTrc  (cgNodeMap ! (CallSite (call, return))),   CallSite (call', return') <- [ fromJust $ lab cgTrc  n ] ]
                            in
                              assert ((cgNodeMap ! (CallSite (call, return)),  CallSite (call, return)) `elem` expectedSummariesAt) $
                              assert ((cgNodeMap ! (CallSite (call, return)),  CallSite (call, return)) `elem` possibleSummariesAt) $
                              -- (
                              --   if (length possibleSummariesAt > 1) then
                              --     traceShow ("# Implied summary Edges:", length expectedSummariesAt - 1, " of ", length possibleSummariesAt - 1 )
                              --   else
                              --     id
                              -- ) $
                              not $
                              (∀) expectedSummariesAt (\((n, CallSite (call', return'))) ->
                                               let actualIn'  = actualInForVar  ! ((call', return'), x)
                                                   actualOut' = actualOutForVar ! ((call', return'), y)
                                               in
                                                  -- traceShow ("Expected: ", (actualIn', actualOut', SummaryDependence)) $
                                                  (actualOut', SummaryDependence) `elem` (lsuc sdg actualIn')
                               )
                          ]
  where callGraphGivenIndepsFor x y = callGraphGivenIndeps x y cg cgNodeMap trivialDataIndependenceGraph parameterMaps
        cfg = tcfg p
        (cfgWithParameterNodes, parameterMaps@(ParameterMaps { parameterNodesFor, actualInForVar, actualOutForVar })) = withParameterNodes p
        pdg = programDependenceGraphP p
        sdg = addSummaryEdges parameterMaps pdg
        (trivialDataIndependenceGraph, _) = strongTrivialDataIndependenceGraphP p
        (cg, cgNodeMap) = callGraph p
        cgTrc = trc cg
        summaries = [((actualIn,  fromJust $ lab cfgWithParameterNodes actualIn),
                      (actualOut, fromJust $ lab cfgWithParameterNodes actualOut)
                     )
                    | (actualIn, actualOut, SummaryDependence) <- labEdges sdg
                    ]



addImplicitAndTrivialSummaryEdgesLfp :: DynGraph gr => Program gr -> ParameterMaps ->  Set SummaryIndependence -> Set FormalInActualInIndependence -> Set ActualOutFormalOutIndependence ->  gr SDGNode Dependence -> gr SDGNode Dependence
addImplicitAndTrivialSummaryEdgesLfp p parameterMaps@(ParameterMaps { trivialActualInFor }) summaryindependencies formalInActualInInIndependencies  actualOutFormalOutIndependencies sdg =
      insEdges [ (actualIn, actualOut,  SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries, not $ hasLEdge sdg (actualIn, actualOut,  SummaryDependence) ]
    $ sdg
  where summaries = implicitSummaryEdgesLfp p parameterMaps sdg summaryindependencies formalInActualInInIndependencies  actualOutFormalOutIndependencies
                  ∪ Set.fromList [ (actualIn, actualOut) | (actualOut, actualIn) <- Map.assocs trivialActualInFor, not $ (actualIn, actualOut, ())   ∈ summaryindependencies]


-- given a sdg with some summary edges, return all summary edges implied by the existing ones.
-- for "normal" ("full") sdg, all these summary edges will already be present, of course
implicitSummaryEdgesLfp :: DynGraph gr => Program gr -> ParameterMaps -> gr SDGNode Dependence -> Set SummaryIndependence -> Set FormalInActualInIndependence -> Set ActualOutFormalOutIndependence -> Set SummaryEdge
implicitSummaryEdgesLfp p parameterMaps sdg summaryindependencies formalInActualInInIndependencies  actualOutFormalOutIndependencies =  (㎲⊒) (Set.empty) (implicitSummaryComputationF parameterMaps sdg summaryindependencies formalInActualInInIndependencies  actualOutFormalOutIndependencies (cg, cgNodeMap))
  where (cg, cgNodeMap) = callGraph p


implicitSummaryPredecessorsF :: DynGraph gr =>
                    ParameterMaps ->
                    (Node -> SDGNode) ->
                    Set SummaryEdge ->
                    Set SummaryIndependence ->
                    Set FormalInActualInIndependence ->
                    Set ActualOutFormalOutIndependence ->
                    (gr CallGraphNode CallGraphEdge, Map CallGraphNode Node) ->
                    Set SummaryEdge ->
                    Set SummaryEdge
implicitSummaryPredecessorsF
                    parameterMaps@(ParameterMaps { actualInForVar, actualOutForVar, formalInForVar, formalOutForVar})
                    labelOf
                    baseSummaries
                    summaryindependencies
                    formalInActualInInIndependencies
                    actualOutFormalOutIndependencies
                    (cg, cgNodeMap)
                    implicitSummaries = -- traceShow (baseSummaries, implicitSummaries) $ 
    implicitSummaries
  ⊔ Set.fromList [ (actualIn', actualOut') | ((actualIn, ActualIn x (call, return)), (actualOut, ActualOut y _)) <- summaries,
                                             (n, IncludesCallSite)  <- lpre cg (cgNodeMap ! (CallSite (call, return))),
                                             let Procedure (entry, exit) = fromJust $ lab cg n,
                                             let formalIn   = formalInForVar  ! ((entry, exit), x),
                                             let formalOut  = formalOutForVar ! ((entry, exit), y),
                                             not $  (formalIn,  actualIn,  (), ())     ∈ formalInActualInInIndependencies,
                                             not $  (actualOut, formalOut, (), (), ()) ∈ actualOutFormalOutIndependencies,
                                             (m, Calls) <- lpre cg n,
                                             let CallSite (call', return') = fromJust $ lab cg m,
                                             let actualIn'  = actualInForVar  ! ((call', return'), x),
                                             let actualOut' = actualOutForVar ! ((call', return'), y)
    ]
  where summaries = [((actualIn,  labelOf actualIn),
                      (actualOut, labelOf actualOut)
                     )
                    | (actualIn, actualOut) <- Set.toList $ baseSummaries
                    ]
                ++  [((actualIn,  labelOf actualIn),
                      (actualOut, labelOf actualOut)
                     )
                    | (actualIn, actualOut) <- Set.toList $ implicitSummaries
                    ]


implicitSummaryComputationF :: DynGraph gr => ParameterMaps -> gr SDGNode Dependence -> Set SummaryIndependence -> Set FormalInActualInIndependence -> Set ActualOutFormalOutIndependence -> (gr CallGraphNode CallGraphEdge, Map CallGraphNode Node) -> Set SummaryEdge -> Set SummaryEdge
implicitSummaryComputationF
                    parameterMaps
                    sdg
                    summaryindependencies
                    formalInActualInInIndependencies
                    actualOutFormalOutIndependencies
                    (cg, cgNodeMap)
                    implicitSummaries = implicitSummaryPredecessorsF parameterMaps labelOf baseSummaries summaryindependencies formalInActualInInIndependencies actualOutFormalOutIndependencies (cg, cgNodeMap) implicitSummaries
  where labelOf n =  fromJust $ lab sdg n
        baseSummaries = Set.fromList [(actualIn, actualOut) | (actualIn, actualOut, SummaryDependence) <- labEdges sdg ]




implicitSummarySuccessorsF :: DynGraph gr => ParameterMaps -> (Node -> SDGNode) -> Set SummaryEdge -> gr SDGNode Independence -> (gr CallGraphNode CallGraphEdge, Map CallGraphNode Node) -> Set SummaryEdge -> Set SummaryEdge
implicitSummarySuccessorsF
                    parameterMaps@(ParameterMaps { actualInForVar, actualOutForVar, formalInForVar, formalOutForVar })
                    labelOf
                    baseSummaries
                    trivialDataIndependenceGraph
                    (cg, cgNodeMap)
                    implicitSummaries =
    implicitSummaries
  ⊔ Set.fromList [ (actualIn', actualOut') | ((actualIn, ActualIn x (call, return)), (actualOut, ActualOut y _)) <- summaries,
                                             (n, Calls)  <- lsuc cg (cgNodeMap ! (CallSite (call, return))),
                                             let Procedure (entry, exit) = fromJust $ lab cg n,
                                             let formalIn   = formalInForVar  ! ((entry, exit), x),
                                             let formalOut  = formalOutForVar ! ((entry, exit), y),
                                             (m, IncludesCallSite) <- lsuc cg n,
                                             let CallSite (call', return') = fromJust $ lab cg m,
                                             let actualIn'  = actualInForVar  ! ((call', return'), x),
                                             let actualOut' = actualOutForVar ! ((call', return'), y),
                                             not $  (formalIn,  actualIn,  DataIndependence) `elem` labEdges trivialDataIndependenceGraph,
                                             not $  (actualOut, formalOut, DataIndependence) `elem` labEdges trivialDataIndependenceGraph
    ]
  where summaries = [((actualIn,  labelOf actualIn),
                      (actualOut, labelOf actualOut)
                     )
                    | (actualIn, actualOut) <- Set.toList $ baseSummaries
                    ]
                ++  [((actualIn,  labelOf actualIn),
                      (actualOut, labelOf actualOut)
                     )
                    | (actualIn, actualOut) <- Set.toList $ implicitSummaries
                    ]



implicitSummarySuccessorsOfActualOutF :: DynGraph gr =>
                   ParameterMaps ->
                   (Node -> SDGNode) ->
                   Set SummaryEdge ->
                   Set ActualOutFormalOutIndependence ->
                   (gr CallGraphNode CallGraphEdge, Map CallGraphNode Node) ->
                   (Set Node, Set SummaryEdge) ->
                   (Set Node, Set SummaryEdge)
implicitSummarySuccessorsOfActualOutF
                    parameterMaps@(ParameterMaps { actualInForVar, actualOutForVar, formalInForVar, formalOutForVar })
                    labelOf
                    baseSummaries
                    actualOutFormalOutIndependencies
                    (cg, cgNodeMap)
                    (actualOuts, summaries) =
    (actualOuts ⊔ newActualOuts, summaries ⊔ newSummaries)
  where actualOutsWithNode = [ (actualOut, labelOf actualOut) | actualOut <- Set.toList $ actualOuts ]
        newActualOuts = Set.fromList [ actualOut' | (actualOut, ActualOut y (call, return)) <- actualOutsWithNode,
                               (n, Calls)  <- lsuc cg (cgNodeMap ! (CallSite (call, return))),
                               let Procedure (entry, exit) = fromJust $ lab cg n,
                               let formalOut  = formalOutForVar ! ((entry, exit), y),
                               (m, IncludesCallSite) <- lsuc cg n,
                               let CallSite (call', return') = fromJust $ lab cg m,
                               let actualOut' = actualOutForVar ! ((call', return'), y),
                               not $  (actualOut', formalOut, (), (), ()) ∈  actualOutFormalOutIndependencies

                        ]
        newSummaries = Set.fromList [ (actualIn, actualOut) | (actualIn, actualOut) <- Set.toList baseSummaries, actualOut ∈ newActualOuts ]

implicitSummaryPredecessorsOfActualInF :: DynGraph gr =>
                    ParameterMaps ->
                    (Node -> SDGNode) ->
                    Set FormalInActualInIndependence ->
                    (gr CallGraphNode CallGraphEdge, Map CallGraphNode Node) ->
                    Set (Node, Node) ->
                    Set Node -> Set Node
implicitSummaryPredecessorsOfActualInF
                    parameterMaps@(ParameterMaps { actualInForVar, actualOutForVar, formalInForVar, formalOutForVar })
                    labelOf
                    formalInActualInInIndependencies
                    (cg, cgNodeMap)
                    callSites
                    actualIns = actualIns ⊔ newActualIns
  where actualInsWithNode = [ (actualIn, labelOf actualIn) | actualIn <- Set.toList $ actualIns ]
        newActualIns = Set.fromList [ actualIn' | (actualIn, ActualIn x (call, return)) <- actualInsWithNode,
                                                  (n, IncludesCallSite)  <- lpre cg (cgNodeMap ! (CallSite (call, return))),
                                                  let Procedure (entry, exit) = fromJust $ lab cg n,
                                                  let formalIn   = formalInForVar  ! ((entry, exit), x),
                                                  not $  (formalIn,  actualIn, (), ()) ∈ formalInActualInInIndependencies,
                                                  (m, Calls) <- lpre cg n,
                                                  let CallSite (call', return') = fromJust $ lab cg m,
                                                  (call', return') ∈ callSites,
                                                  let actualIn'  = actualInForVar  ! ((call', return'), x)
                       ]


data PathState = Trivial | Translated | NonTrivial deriving (Show, Ord, Eq, Bounded, Enum)
instance JoinSemiLattice PathState where
  Trivial    `join` x          = x
  x          `join` Trivial    = x

  NonTrivial `join` x          = NonTrivial 
  x          `join` NonTrivial = NonTrivial

  Translated `join` Translated = Translated

instance BoundedJoinSemiLattice PathState where
  bottom = Trivial


after :: PathState -> PathState -> PathState
after Trivial x = x
after Translated Trivial    = Translated
after Translated Translated = NonTrivial
after Translated NonTrivial = NonTrivial
after NonTrivial x          = NonTrivial


addNonImplicitNonTrivialSummaryEdges :: DynGraph gr => Program gr -> ParameterMaps -> gr SDGNode Dependence -> (gr SDGNode Dependence, Set SummaryIndependence, Set FormalInActualInIndependence, Set ActualOutFormalOutIndependence)

addNonImplicitNonTrivialSummaryEdges p
                           parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, parameterNodesFor })
                           graph
  = (
      insEdges [ (actualIn, actualOut,  SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries]
    $ graph,
      summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies
    )
  where (summaries, summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)  = nonImplicitNonTrivialSummaryComputation parameterMaps graph (cg, cgNodeMap) initialWorkSet initialReached initialAoPaths initialSummaries  initialSummaryIndependencies initialformalInActualInIndependencies initialActualOutFormalOutIndependencies
        initialWorkSet   = Set.fromList [ (source, formalOut, pathStateForEdge graph (source, formalOut, edge))
                                                                                | formalOut <- formalOuts,
                                                                                  (source, edge) <- lpre graph formalOut,
                                                                                  isIntra edge
                           ]
                         ⊔ Set.fromList [ (source, actualIn,  pathStateForEdge graph (source, actualIn,  edge))
                                                                                | actualIn  <- relevantActualIns,
                                                                                  (source, edge) <- lpre graph actualIn,
                                                                                  isIntra edge
                           ]

        initialReached   = Map.fromList [ (formalOut, Map.fromList [(formalOut, Trivial)]) | formalOut <- formalOuts ]
                         ⊔ Map.fromList [ (actualIn,  Map.fromList [(actualIn, Trivial)])  | actualIn  <- relevantActualIns ]
        initialAoPaths   = Map.fromList [ (actualOut, Map.empty)                           | actualOut <- actualOuts ]
        initialSummaries = Set.empty
        formalOuts = [ formalOut | formalOut <- nodes graph, Just (FormalOut _)     <- [lab graph formalOut]]
        actualOuts = [ actualOut | actualOut <- nodes graph, Just (ActualOut  _ _ ) <- [lab graph actualOut]]
        actualIns  = [ actualIn  | actualIn  <- nodes graph, Just (ActualIn   _ _ ) <- [lab graph actualIn]]

        relevantActualIns =
                     [ actualIn  | actualIn  <- actualIns, not $ List.null $ lpre trivialDataIndependenceGraph actualIn ]
        
        initialSummaryIndependencies = Set.fromList $ 
                                       [ (actualIn, actualOut, ())        | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (formalIn,  FormalIn  x ) <- [(n, fromJust $ lab graph n)],
                                                                            (formalOut, FormalOut x') <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True,
                                                                            actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab graph actualIn],
                                                                            actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab graph actualOut],
                                                                            call == call'
                                       ]
        initialformalInActualInIndependencies = Set.fromList $ 
                                       [ (formalIn, actualIn, (),())      | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (formalIn, FormalIn  x )   <- [(n, fromJust $ lab graph n)],
                                                                            (actualIn, ActualIn  x' _) <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True
                                       ]
        initialActualOutFormalOutIndependencies = Set.fromList $ 
                                       [ (actualOut, formalOut, (),(),()) | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (actualOut, ActualOut  x  _) <- [(n, fromJust $ lab graph n)],
                                                                            (formalOut, FormalOut  x')   <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True
                                       ]
        (trivialDataIndependenceGraph, _) = strongTrivialDataIndependenceGraphP p
        (cg, cgNodeMap) = callGraph p


pathStateForEdge graph (n, m, e) = case (fromJust $ lab graph n, fromJust $ lab graph m, e) of
          (FormalIn  x,   FormalOut x',   DataDependence) -> assert (x == x')                                      $ NonTrivial
          (FormalIn  x,   ActualIn  x' _, DataDependence) -> assert (x == x')                                      $ Trivial
          (ActualOut x _, FormalOut x',   DataDependence) -> assert (x == x')                                      $ Trivial
          (ActualOut x _, ActualIn x' _,  DataDependence) -> assert (x == x')                                      $ Trivial

          (CFGNode _,     ActualIn x' _,  _             ) -> assert (e `elem` [DataDependence, ControlDependence]) $ NonTrivial
          (ActualOut x _, CFGNode _,      _             ) -> assert (e `elem` [DataDependence                   ]) $ NonTrivial
          (CFGNode _,     FormalOut x',   _             ) -> assert (e `elem` [DataDependence                   ]) $ NonTrivial
          (FormalIn x,    CFGNode _,      _             ) -> assert (e `elem` [DataDependence                   ]) $ NonTrivial

          (ActualIn x _,  ActualOut x' _, SummaryDependence) -> if (x == x') then Trivial else Translated

          (n',            m',             _             ) -> error (show (n', m', e))


type WorkListEdge =  (Node, Node, PathState) -- (sourece, formalOut, pathState)
nonImplicitNonTrivialSummaryComputation :: DynGraph gr =>
                   ParameterMaps ->
                   gr SDGNode Dependence ->
                   (gr CallGraphNode CallGraphEdge, Map CallGraphNode Node) ->
                   Set WorkListEdge ->
                   Map Node (Map Node PathState) ->
                   Map Node (Map Node PathState) ->
                   Set SummaryEdge ->
                   Set SummaryIndependence ->
                   Set FormalInActualInIndependence ->
                   Set ActualOutFormalOutIndependence ->
                   (Set SummaryEdge, Set SummaryIndependence, Set FormalInActualInIndependence , Set ActualOutFormalOutIndependence)
nonImplicitNonTrivialSummaryComputation
                   parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, trivialActualInFor })
                   graph
                   (cg, cgNodeMap)
                   workSet
                   reached
                   aoPaths
                   summaries
                   summaryindependencies
                   formalInActualInInIndependencies
                   actualOutFormalOutIndependencies
    | Set.null workSet = (summaries, summaryindependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)
    | otherwise = 
        case Map.lookup source (reached ! target) of
          Just pathState' -> if pathState ⊑ pathState' then old else new
          Nothing         ->                                         new
  where
        old = nonImplicitNonTrivialSummaryComputation parameterMaps graph (cg, cgNodeMap) (workSet'                                                                                             ) reached                aoPaths                 summaries                 (summaryindependencies                      )  (formalInActualInInIndependencies           ) (actualOutFormalOutIndependencies           )
        new = 
              nonImplicitNonTrivialSummaryComputation parameterMaps graph (cg, cgNodeMap) (workSet' ∪ newIntraWorklistEdgesViaIndependencies ∪ newIntraWorklistEdges  ∪ newSummaryWorklistEdges) (reached ⊔ newReached) (aoPaths ⊔ newAoPaths) (summaries ∪ newSummaries) (summaryindependencies ∖ lostIndependencies)  (formalInActualInInIndependencies ∖ lostFiAi) (actualOutFormalOutIndependencies ∖ lostAoFo)

        ((source, target, pathState), workSet') = Set.deleteFindMin workSet
        labelOf n = fromJust $ lab graph n

        newReached = Map.fromList [ (target, Map.fromList [(source, pathState)])]
        newAoPaths = case lab graph source of
            Just (ActualOut _ _) -> Map.fromList [ (source, Map.fromList [(target, pathState)]) ]
            _                    -> Map.empty
        newIntraWorklistEdges             = Set.fromList [ (source', target, pathState `after` pathStateForEdge graph (source', source, edge)) | (source', edge) <- lpre graph source, isIntra edge]
        newIntraWorklistEdgesViaIndependencies = case lab graph source of
            Just (ActualOut _ (call, return)) -> Set.fromList [ (actualIn', target, pathState `after` pathStateForEdge graph (actualIn', actualOut', SummaryDependence)) | (actualIn', actualOut') <- Set.toList allSummaries]
              where actualOut = source
                    (actualOut's, nonImplicitSummarieCandidates) =
                      (㎲⊒) (Set.singleton actualOut, Set.empty) (implicitSummarySuccessorsOfActualOutF parameterMaps labelOf summaries  actualOutFormalOutIndependencies (cg, cgNodeMap) )
                    callSites = Set.fromList [ (call', return') | actualOut' <- Set.toList $ actualOut's, let ActualOut _ (call', return') = fromJust $ lab graph actualOut' ]
                    allSummaries =   Set.fromList [ (actualIn', actualOut) | (actualIn', actualOut') <- Set.toList summaries, actualOut' == actualOut]
                                   ∪ Set.fromList [ (actualIn', actualOut) | actualIn' <- [ trivialActualInFor  ! actualOut ], not $ (actualIn', actualOut, ())   ∈ summaryindependencies ]
                                   ∪ Set.fromList [ (actualIn', actualOut) | actualIn' <- Set.toList $
                                                                               (㎲⊒) (Set.fromList [ actualIn | (actualIn, actualOut) <- Set.toList nonImplicitSummarieCandidates ])
                                                                                     (implicitSummaryPredecessorsOfActualInF parameterMaps labelOf formalInActualInInIndependencies (cg, cgNodeMap) callSites),
                                                                             let ActualIn _ (call', return') = fromJust $ lab graph actualIn',
                                                                             (call', return') == (call, return),
                                                                             let implicits = nonImplicitSummarieCandidates ∪ ((㎲⊒) (Set.empty) (implicitSummaryPredecessorsF parameterMaps labelOf nonImplicitSummarieCandidates  summaryindependencies formalInActualInInIndependencies actualOutFormalOutIndependencies (cg, cgNodeMap))),
                                                                             assert ((actualIn', actualOut) ∈ implicits) $ True
                                     ]
            _                                 -> Set.empty
        -- FIXME: we need to create worklist edges for implicit summaries that become "unblocked" by this removal
        lostAoFo = case (lab graph source, lab graph target) of
            (Just (ActualOut x _), Just (FormalOut x' )) -> Set.fromList [ (actualOut, formalOut, (), (), ()) | x == x']
              where actualOut = source
                    formalOut = target
            _                    -> Set.empty
        -- FIXME: we need to create worklist edges for implicit summaries that become "unblocked" by this removal
        lostFiAi = case (lab graph source, lab graph target) of 
            (Just (FormalIn x), Just (ActualIn x' _))    -> Set.fromList [ (formalIn,  actualIn,  (), ()    ) | x == x']
              where formalIn  = source
                    actualIn  = target
            _                    -> Set.empty
        (newSummaries, lostIndependencies, newSummaryWorklistEdges) = case (lab graph source, lab graph target) of
            (Just (FormalIn _), Just (FormalOut _)) -> 
                                 lop2sol $ 
                                 [ ( if (pathState == NonTrivial) then [(actualIn, actualOut   )  | x /= x'] else [],
                                    [(actualIn', actualOut',())  | x == x', (actualIn', actualOut') <- Set.toList $ allSummaries actualIn actualOut ],
                                    [(actualIn', formalOut', pathState' `after` pathStateForEdge graph (actualIn', actualOut', SummaryDependence)) | (actualIn', actualOut') <- Set.toList $ allSummaries actualIn actualOut,
                                                                                                       (formalOut', pathState') <- Map.assocs $ aoPaths ! actualOut'

                                    ]
                                   )
                                 | actualIn  <- Set.toList $ actualInsFor  ! formalIn,  Just (ActualIn  x  callReturn ) <- [lab graph actualIn],
                                   actualOut <- Set.toList $ actualOutsFor ! formalOut, Just (ActualOut x' callReturn') <- [lab graph actualOut],
                                   callReturn == callReturn' -- TODO: performance
                                 ]
            _                 -> (Set.empty, Set.empty, Set.empty)
          where formalIn = source
                formalOut = target
                allSummaries actualIn actualOut =
                      Set.singleton (actualIn, actualOut)                                                                                                                        -- the one we're about to create
                    ∪ (㎲⊒) (Set.empty) (implicitSummaryPredecessorsF parameterMaps labelOf (Set.singleton (actualIn, actualOut)) summaryindependencies formalInActualInInIndependencies actualOutFormalOutIndependencies (cg, cgNodeMap))  -- implicitly created
                lop2sol [] = (Set.empty, Set.empty, Set.empty)
                lop2sol ((a,b,c):xs) = ((Set.fromList a) ⊔ as, (Set.fromList b) ⊔ bs, (Set.fromList c) ⊔ cs)
                  where (as,bs,cs) = lop2sol xs



addNonImplicitNonTrivialSummaryEdgesGfpLfp :: DynGraph gr => Program gr -> ParameterMaps -> gr SDGNode Dependence -> (gr SDGNode Dependence, Set SummaryIndependence, Set FormalInActualInIndependence, Set ActualOutFormalOutIndependence)
addNonImplicitNonTrivialSummaryEdgesGfpLfp p
                      parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, parameterNodesFor })
                      graph
  = (
      insEdges [ (actualIn, actualOut, SummaryDependence)  | (actualIn, actualOut) <- Set.toList summaries,
                                                             (ActualIn  x call ) <- [fromJust $ lab graph actualIn],  -- avoid duplicate edges
                                                             (ActualOut y call') <- [fromJust $ lab graph actualOut], --
                                                             assert (call == call') $ True,                           --
                                                             assert (x /= y) $ True
      ]
    $ graph,
      summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies
    )
  where summaries = summariesGivenIndependencies (summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)
        (summaryIndependencies, (formalInActualInInIndependencies, actualOutFormalOutIndependencies)) =
            (𝝂) (initialSummaryIndependencies, (initialFormalInActualInIndependencies, initialActualOutFormalOutIndependencies)) independenciesF
          where
            initialSummaryIndependencies = Set.fromList $ 
                                       [ (actualIn, actualOut, ())        | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (formalIn,  FormalIn  x ) <- [(n, fromJust $ lab graph n)],
                                                                            (formalOut, FormalOut x') <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True,
                                                                            actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab graph actualIn],
                                                                            actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab graph actualOut],
                                                                            call == call'
                                       ]
            initialFormalInActualInIndependencies = Set.fromList $ 
                                       [ (formalIn, actualIn, (),())      | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (formalIn, FormalIn  x )   <- [(n, fromJust $ lab graph n)],
                                                                            (actualIn, ActualIn  x' _) <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True
                                       ]
            initialActualOutFormalOutIndependencies = Set.fromList $ 
                                       [ (actualOut, formalOut, (),(),()) | (n, m, DataIndependence) <- labEdges trivialDataIndependenceGraph,
                                                                            (actualOut, ActualOut  x  _) <- [(n, fromJust $ lab graph n)],
                                                                            (formalOut, FormalOut  x')   <- [(m, fromJust $ lab graph m)],
                                                                            assert (x == x') $ True
                                       ]
            (trivialDataIndependenceGraph, _) = strongTrivialDataIndependenceGraphP p


        
        intraOnly = efilter (\(n, m, e) -> isIntra e) graph

        independenciesF :: (Set SummaryIndependence, (Set FormalInActualInIndependence, Set ActualOutFormalOutIndependence))
                        -> (Set SummaryIndependence, (Set FormalInActualInIndependence, Set ActualOutFormalOutIndependence))
        independenciesF (summaryIndependencies, (formalInActualInIndependencies, actualOutFormalOutIndependencies)) =
            ( Set.fromList [ (actualIn,  actualOut, ())        | (actualIn,  actualOut, ()   )      <- Set.toList $ summaryIndependencies,            not $ (actualIn, actualOut) ∈ summaries ],
            ( Set.fromList [ (formalIn,  actualIn , (), ())    | (formalIn,  actualIn,  (), ())     <- Set.toList $ formalInActualInIndependencies,   not $ formalIn `elem` pre reachable actualIn ],
              Set.fromList [ (actualOut, formalOut, (), (),()) | (actualOut, formalOut, (), (), ()) <- Set.toList $ actualOutFormalOutIndependencies, not $ actualOut `elem` pre reachable formalOut ]
            ))
          where summaries = summariesGivenIndependencies (summaryIndependencies, formalInActualInIndependencies, actualOutFormalOutIndependencies)
                intraGraphWithSummaries = 
                                  addImplicitAndTrivialSummaryEdgesLfp p parameterMaps summaryIndependencies formalInActualInIndependencies actualOutFormalOutIndependencies
                                $ insEdges [ (actualIn, actualOut, SummaryDependence) | (actualIn, actualOut) <- Set.toList summaries ]
                                $ intraOnly
                reachable = trc intraGraphWithSummaries

        summariesGivenIndependencies  :: (Set SummaryIndependence, Set FormalInActualInIndependence, Set ActualOutFormalOutIndependence) -> Set SummaryEdge
        summariesGivenIndependencies  (summaryIndependencies, formalInActualInIndependencies, actualOutFormalOutIndependencies) =
           (㎲⊒) (Set.empty) (summaryComputationGivenIndependenciesF p parameterMaps intraOnly  (summaryIndependencies, formalInActualInIndependencies, actualOutFormalOutIndependencies))


summaryComputationGivenIndependenciesF :: DynGraph gr => Program gr -> ParameterMaps -> gr SDGNode Dependence -> (Set SummaryIndependence, Set FormalInActualInIndependence, Set ActualOutFormalOutIndependence) -> Set SummaryEdge -> Set SummaryEdge
summaryComputationGivenIndependenciesF
                    p
                    parameterMaps@(ParameterMaps { actualInsFor, actualOutsFor, parameterNodesFor })
                    graph
                    (summaryIndependencies, formalInActualInIndependencies, actualOutFormalOutIndependencies)
                    summaries =
    assert ([ e | (n, m, e) <- labEdges graph, not $ isIntra e ] == []) $
    summaries
  ⊔ Set.fromList [ (actualIn, actualOut) | (formalIn, FormalIn x)  <- labNodes reachable,
                                           (formalOut, FormalOut y) <- [ (m, fromJust $ lab reachable m) | m <- suc reachable formalIn],
                                           actualIn  <- Set.toList $ actualInsFor  ! formalIn,  (ActualIn  _ call ) <- [fromJust $ lab reachable actualIn],
                                           actualOut <- Set.toList $ actualOutsFor ! formalOut, (ActualOut _ call') <- [fromJust $ lab reachable actualOut],
                                           call == call',
                                           not $ hasLEdge intraGraphWithSummaries (actualIn, actualOut, SummaryDependence) 
    ]
  where intraGraphWithSummaries = 
                                  addImplicitAndTrivialSummaryEdgesLfp p parameterMaps summaryIndependencies formalInActualInIndependencies actualOutFormalOutIndependencies
                                $ insEdges [ (actualIn, actualOut, SummaryDependence) | (actualIn, actualOut) <- Set.toList summaries ]
                                $ graph
        reachable = trc intraGraphWithSummaries


                        

slice :: Graph gr => gr SDGNode Dependence -> (Dependence -> Bool) -> Set Node -> Set Node
slice graph follow nodes = (㎲⊒) nodes f
  where f nodes = nodes ∪ (Set.fromList [ m | n <- Set.toList nodes, (m,e) <- lpre graph n, follow e])

intraSlice ::  Graph gr => gr SDGNode Dependence -> Set Node -> Set Node
intraSlice graph nodes = slice graph follow nodes
  where follow ControlDependence      = True
        follow DataDependence         = True
        follow CallDependence         = False
        follow SummaryDependence      = True
        follow SpawnDependence        = False
        follow InterThreadDependence  = False
        follow ParameterInDependence  = False
        follow ParameterOutDependence = False


intraChop :: DynGraph gr => gr SDGNode Dependence -> Set Node -> Set Node -> Set Node
intraChop graph nodes1 nodes2  = (intraSlice graph nodes1) ∩ (intraSlice (grev graph) nodes2)


        
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
