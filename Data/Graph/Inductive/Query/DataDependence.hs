{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.DataDependence where

import Control.Monad.Gen
import Control.Monad

import Debug.Trace
import Control.Exception.Base (assert)


import Unicode



import IRLSOD
import Program
import Util

import Algebra.Lattice

import Data.Char

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Maybe (fromJust)

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.Dataflow
import Data.Graph.Inductive.Query.Dependence


{- Es passt schon die default Instanziierung:
   instance BoundedJoinSemiLattice (Map Var (Set Node))
-}

dependenceAnalysis :: Set Var -> DataflowAnalysis (Map Var (Set (LEdge CFGEdge))) CFGEdge
dependenceAnalysis vars = DataflowAnalysis {
    transfer = transfer,
    initial = initial
  }
 where
  initial = Map.fromList [ (var, Set.empty) | var <- Set.toList vars ]

  transfer e@(_,_,Guard _ _)  reachingDefs = reachingDefs
  transfer e@(_,_,Assign x _) reachingDefs = Map.insert x (Set.singleton e) reachingDefs
  transfer e@(_,_,Read   x _) reachingDefs = Map.insert x (Set.singleton e) reachingDefs
  transfer e@(_,_,Def    x)   reachingDefs = Map.insert x (Set.singleton e) reachingDefs
  transfer e@(_,_,Use    x)   reachingDefs = reachingDefs
  transfer e@(_,_,Print  _ _) reachingDefs = reachingDefs
  transfer e@(_,_,Spawn)      reachingDefs = reachingDefs
  transfer e@(_,_,NoOp)       reachingDefs = reachingDefs
  transfer e@(_,_,Call)       reachingDefs = initial
  transfer e@(_,_,Return)     reachingDefs = initial
  transfer e@(_,_,CallSummary)reachingDefs = initial



find :: Graph gr => gr a b -> Node -> ((Node, b) -> Bool) -> (a -> Bool) -> Node
find graph start followEdge found
    | found (label start) = start
    | otherwise   = case filter followEdge $ lsuc graph start of
        []      -> error ("not found, at:" ++ (show start))
        [(n,_)] -> find graph n followEdge found
        _       -> error "linear search only"
  where label n = fromJust $ lab graph n


-- finds :: Graph gr => gr a b -> Node -> ((Node, b) -> Bool) -> (a -> Bool) -> [Node]
-- finds graph start followEdge found 
--     | found (label start) = [start]
--     | otherwise   = do
--         (n,_) <- filter followEdge $ lsuc graph start
--         finds graph n followEdge found
--   where label n = fromJust $ lab graph n


data ParameterMaps = ParameterMaps {
    formalInFor   :: Map Node Node,       -- actualIn   ->     formalIn
    formalOutFor  :: Map Node Node,       -- actualOut  ->     formalOut
    actualInsFor  :: Map Node (Set Node), -- formalIn   -> Set actualIn
    actualOutsFor :: Map Node (Set Node), -- formalOut  -> Set actualOut
    trivialActualInFor :: Map Node Node,  -- actualOut  ->     actualIn  s.t.  both var(actualIn) == var(actualOut)
    actualInForVar  :: Map ((Node, Node), Var) Node,  -- ((call, return), x) -> actualIn  s.t. var(actualIn) == x
    actualOutForVar :: Map ((Node, Node), Var) Node,  -- ((call, return), x) -> actualOut s.t. var(actualOut) == x
    formalInForVar  :: Map ((Node, Node), Var) Node,  -- ((entry, exit), x) -> formalIn  s.t. var(formalIn) == x
    formalOutForVar :: Map ((Node, Node), Var) Node,  -- ((entry, exit), x) -> formalOut s.t. var(formalOut) == x
    parameterNodesFor :: Map (Node, Node) (Set Node)  --   (entry, exit)  -> (Set formalIn ∪ Set formalOut)
                                                      -- ∪ (call, return) -> (Set actualIn ∪ Set actualOut)
  } deriving (Eq, Show)

withParameterNodes :: DynGraph gr => Program gr -> (gr SDGNode CFGEdge, ParameterMaps)
withParameterNodes p@(Program { tcfg, entryOf, exitOf, staticProcedures })
    | Set.null allVars = (lifted, ParameterMaps Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty (Map.fromList [((entry, exit), Set.empty) | (entry, exit) <- entryExits]) )
    | otherwise = (graphWithParameterNodes, ParameterMaps { formalInFor = formalInFor, formalOutFor = formalOutFor, actualInsFor = actualInsFor, actualOutsFor = actualOutsFor, trivialActualInFor = trivialActualInFor, parameterNodesFor = parameterNodesFor, actualInForVar = actualInForVar, actualOutForVar = actualOutForVar, formalInForVar = formalInForVar, formalOutForVar = formalOutForVar })

  where (min, max) = nodeRange tcfg
        allVars = vars p
        lifted = nmap CFGNode tcfg
        entryExits  = [(entryOf procedure, exitOf procedure) | procedure <- Set.toList $ staticProcedures]
        callReturns = [(n,m)                                 | (n,m, CallSummary) <- labEdges tcfg]
        (graphWithParameterNodes, parameterNodesFor) = runGenFrom (max + 1) $ do
          (withFormals, formalNodesFor)    <- addFormals allVars entryExits  lifted      Map.empty
          (withActuals, parameterNodesFor) <- addActuals allVars callReturns withFormals formalNodesFor
          return (withActuals, parameterNodesFor)
        formalInFor = Map.fromList [ (n, find graphWithParameterNodes n follow (found v))   | (n, ActualIn v _) <- labNodes graphWithParameterNodes ]
          where follow (_, Use _) = True
                follow (_, Call ) = True
                follow (_, Def _) = True
                follow (_, NoOp ) = True
                follow          _ = False
                found v (FormalIn v') = v == v'
                found v _             = False
        formalOutFor = Map.fromList [ (n, find (grev graphWithParameterNodes) n follow (found v))   | (n, ActualOut v _) <- labNodes graphWithParameterNodes ]
          where follow (_, Use _)  = True
                follow (_, Def _)  = True
                follow (_, Return) = True
                follow          _ = False
                found v (FormalOut v') = v == v'
                found v _              = False
        actualInsFor =   Map.fromList [(formalIn, Set.empty) | (formalIn, FormalIn _) <- labNodes graphWithParameterNodes ]
                       ⊔ (invert formalInFor)
        actualOutsFor =  Map.fromList [(formalIn, Set.empty) | (formalIn, FormalIn _) <- labNodes graphWithParameterNodes ]
                       ⊔ (invert formalOutFor)
        trivialActualInFor =
                         Map.fromList [(actualOut, actualIn) | callReturn <- callReturns,
                                                               (actualIn,  ActualIn  x  _) <- [ (n, fromJust $ lab  graphWithParameterNodes n) | n <- Set.toList $ parameterNodesFor ! callReturn],
                                                               (actualOut, ActualOut x' _) <- [ (m, fromJust $ lab  graphWithParameterNodes m) | m <- Set.toList $ parameterNodesFor ! callReturn],
                                                               x == x'
                         ]
        actualInForVar  = Map.fromList [((callReturn, x), actualIn)  | callReturn <- callReturns,
                                                                       (actualIn,  ActualIn x _)  <- [ (n, fromJust $ lab  graphWithParameterNodes n) | n <- Set.toList $ parameterNodesFor ! callReturn]
                         ]
        actualOutForVar = Map.fromList [((callReturn, x), actualOut) | callReturn <- callReturns,
                                                                       (actualOut, ActualOut x _) <- [ (n, fromJust $ lab  graphWithParameterNodes n) | n <- Set.toList $ parameterNodesFor ! callReturn]
                         ]
        formalInForVar  = Map.fromList [((entryExit, x), formalIn)  | entryExit <- entryExits,
                                                                       (formalIn,  FormalIn x)    <- [ (n, fromJust $ lab  graphWithParameterNodes n) | n <- Set.toList $ parameterNodesFor ! entryExit]
                         ]
        formalOutForVar = Map.fromList [((entryExit, x), formalOut) | entryExit <- entryExits,
                                                                       (formalOut, FormalOut x)   <- [ (n, fromJust $ lab  graphWithParameterNodes n) | n <- Set.toList $ parameterNodesFor ! entryExit]
                         ]


addFormals :: DynGraph gr => Set Var -> [(Node, Node)] -> gr SDGNode CFGEdge -> Map (Node, Node) (Set Node) -> Gen Node (gr SDGNode CFGEdge, Map (Node, Node) (Set Node))
addFormals allVars                   [] graph parameterNodesFor = return (graph, parameterNodesFor)
addFormals allVars ((entry, exit):rest) graph parameterNodesFor = do
        (withFormalIns,  formalIns)  <- addAfter  entry NoOp Dummy [ (FormalIn  v, Def v) | v <- Set.toList $ allVars ] graph
        (withFormalOuts, formalOuts) <- addBefore exit             [ (FormalOut v, Use v) | v <- Set.toList $ allVars ] withFormalIns
        addFormals allVars rest withFormalOuts (parameterNodesFor ⊔ (Map.fromList [ ((entry, exit), formalIns ∪ formalOuts) ]))


addActuals :: DynGraph gr => Set Var -> [(Node, Node)] -> gr SDGNode CFGEdge -> Map (Node, Node) (Set Node) -> Gen Node (gr SDGNode CFGEdge, Map (Node, Node) (Set Node))
addActuals allVars []                    graph parameterNodesFor = return (graph, parameterNodesFor)
addActuals allVars ((call, return):rest) graph parameterNodesFor = do
        (withActualIns,  actualIns ) <- addAfter  call   NoOp Dummy [ (ActualIn  v (call, return), Use v) | v <- Set.toList $ allVars ] graph
        (withActualOuts, actualOuts) <- addBefore return            [ (ActualOut v (call, return), Def v) | v <- Set.toList $ allVars ] withActualIns
        addActuals allVars rest withActualOuts (parameterNodesFor ⊔ (Map.fromList [ ((call, return), actualIns ∪ actualOuts) ]))

addAfter :: DynGraph gr => Node -> b -> a ->  [(a,b)] -> gr a b -> Gen Node (gr a b, Set Node)
addAfter start startLabel lastLabel nodeLabels graph = do
  nodes <- forM nodeLabels (\(a, b) -> do
      n <- gen
      return ((n, a), b)
   )
  let ((firstNode,_), _) = head nodes
  lastNode <- gen
  let chain =  [ (from, to, e)  | (((from, _),e), ((to, _), _)) <- zip nodes ((tail nodes) ++ [((lastNode, undefined), undefined)]) ]
  let outgoing  = lsuc graph start
  return ( insEdge  (start, firstNode, startLabel)
         $ insEdges chain
         $ insEdges [(lastNode,  m, e) | (m,e) <- outgoing]
         $ delEdges [(start,     m)    | (m,e) <- outgoing]
         $ insNodes (fmap fst nodes)
         $ insNodes [(lastNode, lastLabel)]
         $ graph
         , Set.fromList $ fmap (fst.fst) nodes
         )


addBefore :: DynGraph gr => Node -> [(a,b)] -> gr a b -> Gen Node (gr a b, Set Node)
addBefore end nodeLabels graph = do
  nodes <- forM nodeLabels (\(a, b) -> do
      n <- gen
      return ((n, a), b)
   )
  let ((firstNode,_), _) = head nodes
  let chain =  [ (from, to, e)  | (((from, _),e), ((to, _), _)) <- zip nodes ((tail nodes) ++ [((end, undefined), undefined)]) ]
  let incoming  = lpre graph end
  return ( insEdges chain
         $ insEdges [(m, firstNode, e) | (m,e) <- incoming]
         $ delEdges [(m, end)          | (m,e) <- incoming]
         $ insNodes (fmap fst nodes)
         $ graph
         , Set.fromList $ fmap (fst.fst) nodes
         )



dataDependence :: DynGraph gr => gr a CFGEdge -> Set Var -> Node -> Map Node (Set Node)
dataDependence graph vars entry = Map.fromList [
      (n, Set.fromList $
          [ reachedFromN | reachedFromN <- nodes graph,
                           let edges :: Map Var (Set (LEdge CFGEdge))
                               edges = reaching ! reachedFromN,
                           let nodes :: Map Var (Set (Node))
                               nodes = fmap (\set -> Set.map (\(n,_,_) -> n) set) edges,
                           var <- Set.toList $ use graph reachedFromN,
                           n `Set.member` (nodes ! var)]
      )
     | n <- nodes graph
    ]
  where reaching :: Map Node (Map Var (Set (LEdge CFGEdge)))
        reaching = analysis (dependenceAnalysis vars) graph entry

dataDependenceGraph :: DynGraph gr => gr a CFGEdge -> Set Var -> Node -> gr a Dependence
dataDependenceGraph graph vars entry = mkGraph (labNodes graph) [ (n,n',DataDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = dataDependence graph vars entry



dataDependenceGraphP :: DynGraph gr => Program gr -> (gr SDGNode Dependence, ParameterMaps)
dataDependenceGraphP p@(Program { tcfg, mainThread, entryOf, procedureOf}) = (
      dataDependenceGraph withParameters (vars p) (entryOf $ procedureOf $ mainThread),
      parameterMaps
    )
  where (withParameters, parameterMaps) = withParameterNodes p



nonTrivialDataDependenceGraphP :: DynGraph gr => Program gr -> (gr SDGNode Dependence, ParameterMaps)
nonTrivialDataDependenceGraphP p@(Program { tcfg, mainThread, entryOf, procedureOf}) = (nonTrivialDataDependenceGraph, parameterMaps)
  where (withParameters, parameterMaps) = withParameterNodes p
        nonTrivialDataDependenceGraph = mkGraph (labNodes withParameters) [ (n, n', DataDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's, nonTrivial n n']
        dependencies = dataDependence withParameters (vars p) (entryOf $ procedureOf $ mainThread)
        nonTrivial n n' = case (lab withParameters n, lab withParameters n') of
          (Just (FormalIn  x),   Just (FormalOut x'))    -> x /= x'
          (Just (FormalIn  x),   Just (ActualIn  x' _ )) -> x /= x'
          (Just (ActualOut x _), Just (FormalOut x'))    -> x /= x'
          (Nothing,           _                  ) -> error "label not found"
          (_,                 Nothing            ) -> error "label not found"
          (_,                 _                  ) -> True






data MustKill  = MustKill (Node, Node) Var deriving (Show, Eq, Ord)

mustKill :: DynGraph gr => Program gr -> (Set MustKill)
mustKill p@(Program { tcfg, entryOf, exitOf, mainThread, procedureOf, staticProcedures }) = (𝝂) allMustKillAll mustKillF
  where mustKillF = mustKillFFor tcfg entry entryExits allVarsReachedByInitial
        entry = entryOf $ procedureOf $ mainThread
        allMustKillAll = Set.fromList [ MustKill (entry, exit) x | (entry, exit) <- entryExits, x <- Set.toList $ allVars ]
        entryExits = [ (entry, exit) | procedure <- Set.toList $ staticProcedures,
                                       let entry = entryOf procedure,
                                       let exit  = exitOf procedure
                     ]
        allVars = vars p
        allVarsReachedByInitial = Map.fromList [(x, True) | x <- Set.toList $ allVars ]

mustKillFFor :: DynGraph gr =>
    gr a CFGEdge ->
    Node ->
    [(Node, Node)] ->
    Map Var Bool ->
    Set MustKill ->
    Set MustKill
mustKillFFor graph entry entryExits allVarsReachedByInitial mustKills =
    Set.fromList [ MustKill (entry, exit) x | (entry, exit) <- entryExits, (x, False) <- Map.assocs $  initialReaches ! exit  ]
  where initialReachesGivenMustKillF = initialReachesGivenMustKillFFor graph allVarsReachedByInitial mustKills
        initialReaches  = (㎲⊒)
                           (Map.fromList [(entry, allVarsReachedByInitial)] ⊔ Map.fromList [(n, Map.empty) | n <- nodes graph])
                           initialReachesGivenMustKillF
initialReachesGivenMustKillFFor :: DynGraph gr =>
    gr a CFGEdge ->
    Map Var Bool -> 
    Set MustKill ->
    Map Node (Map Var Bool) ->
    Map Node (Map Var Bool)
initialReachesGivenMustKillFFor graph allVarsReachedByInitial mustKills initialReaches =
    initialReaches ⊔ Map.fromList [(n, (∐) [ transfer e (initialReaches ! m) | (m,label) <- lpre graph n, let e = (m,n,label) ]) | n <- nodes graph  ]
  where
    transfer :: (Node, Node, CFGEdge) -> Map Var Bool -> Map Var Bool
    transfer e@(_,_,Guard _ _)   initialReaches = initialReaches
    transfer e@(_,_,Assign x _)  initialReaches = Map.insert x False initialReaches
    transfer e@(_,_,Read   x _)  initialReaches = Map.insert x False initialReaches
    transfer e@(_,_,Def    x)    initialReaches = Map.insert x False initialReaches
    transfer e@(_,_,Use    x)    initialReaches = initialReaches
    transfer e@(_,_,Print  _ _)  initialReaches = initialReaches
    transfer e@(_,_,Spawn)       initialReaches = initialReaches
    transfer e@(_,_,NoOp)        initialReaches = initialReaches
    transfer e@(_,_,Call)        initialReaches = allVarsReachedByInitial
    transfer e@(_,_,Return)      initialReaches = Map.empty
    transfer e@(m,n,CallSummary) initialReaches = Map.union (Map.fromList [ (x, False) | MustKill (entry', exit') x <- Set.toList $ mustKills, entry' == entry, exit' == exit ])
                                                            initialReaches
      where [entry] =  [ entry | (entry, Call)   <- lsuc graph m ]  -- TODO: handle virtual calls
            [exit]  =  [ exit  | (exit,  Return) <- lpre graph n ]  -- TODO: handle virtual calls



data Definition = CFGEdge (LEdge CFGEdge) | Initial deriving (Show, Eq, Ord)


trivialDataIndependenceGraphP :: DynGraph gr => Program gr -> (gr SDGNode Independence, ParameterMaps)
trivialDataIndependenceGraphP p = trivialDataIndependenceGraphFromReachingP p reaching
  where reaching = reachingDefsP p


strongTrivialDataIndependenceGraphP :: DynGraph gr => Program gr -> (gr SDGNode Independence, ParameterMaps)
strongTrivialDataIndependenceGraphP p = trivialDataIndependenceGraphFromReachingP p reaching
  where reaching = strongReachingDefsP p


trivialDataIndependenceGraphFromReachingP :: DynGraph gr => Program gr -> Map Node (Map Var (Set Definition)) -> (gr SDGNode Independence, ParameterMaps)
trivialDataIndependenceGraphFromReachingP p@(Program { tcfg, mainThread, entryOf, exitOf, procedureOf, staticProcedureOf, staticProcedures }) reaching = (trivialDataIndependenceGraph, parameterMaps)
  where (withParameters, parameterMaps@(ParameterMaps { formalInFor, formalOutFor, actualInsFor, actualOutsFor, parameterNodesFor })) = withParameterNodes p
        allVars = vars p
        trivialDataIndependenceGraph = mkGraph (labNodes withParameters) trivialDataIndependences
        trivialDataIndependences = [
           (formalIn, actualIn, DataIndependence)
              | (entry, exit)  <- entryExits,
                let formals = Set.toList $ parameterNodesFor ! (entry, exit),
                (call, return) <- callReturns, staticProcedureOf call == staticProcedureOf entry, -- TODO: performance
                let actuals = Set.toList $ parameterNodesFor ! (call, return),
                
                let reachingCall = reaching ! call,
                let independentVars = allVars ∖ ( Set.fromList [ x | (x, defs) <- Map.assocs reachingCall, Initial ∈ defs ]),
                x <- Set.toList independentVars,
                let [formalIn] = [ formalIn | formalIn <- formals, isFormalInForX formalIn ]
                      where isFormalInForX n = case (lab withParameters n) of
                              Just (FormalIn x') -> x == x'
                              Nothing            -> error "no such node"
                              _                  -> False,
                let [actualIn] = [ actualIn | actualIn <- actuals, isActualInForX actualIn ]
                      where isActualInForX n = case (lab withParameters n) of
                              Just (ActualIn x' _) -> x == x'
                              Nothing            -> error "no such node"
                              _                  -> False
         ] ++ [
           (actualOut, formalOut, DataIndependence)
              | (entry, exit)  <- entryExits,
                let formals = Set.toList $ parameterNodesFor ! (entry, exit),
                (call, return) <- callReturns, staticProcedureOf call == staticProcedureOf entry, -- TODO: performance
                let actuals = Set.toList $ parameterNodesFor ! (call, return),
                
                let reachingExit = reaching ! exit,
                let independentVars = allVars ∖ ( Set.fromList [ x | (x, defs) <- Map.assocs reachingExit, CFGEdge (call, return, CallSummary) ∈ defs ]),
                x <- Set.toList independentVars,
                let [formalOut] = [ formalOut | formalOut <- formals, isFormalOutForX formalOut ]
                      where isFormalOutForX n = case (lab withParameters n) of
                              Just (FormalOut x') -> x == x'
                              Nothing            -> error "no such node"
                              _                  -> False,
                let [actualOut] = [ actualOut | actualOut <- actuals, isActualOutForX actualOut ]
                      where isActualOutForX n = case (lab withParameters n) of
                              Just (ActualOut x' _) -> x == x'
                              Nothing            -> error "no such node"
                              _                  -> False
         ] ++ [
           (formalIn, formalOut, DataIndependence)
              | (entry, exit)  <- entryExits,
                let formals = Set.toList $ parameterNodesFor ! (entry, exit),
                let reachingExit = reaching ! exit,
                let independentVars = allVars ∖ ( Set.fromList [ x | (x, defs) <- Map.assocs reachingExit, Initial ∈ defs ]),
                x <- Set.toList independentVars,
                let [formalOut] = [ formalOut | formalOut <- formals, isFormalOutForX formalOut ]
                      where isFormalOutForX n = case (lab withParameters n) of
                              Just (FormalOut x') -> x == x'
                              Nothing             -> error "no such node"
                              _                   -> False,
                let [formalIn] = [ formalIn| formalIn <- formals, isFormalInForX formalIn ]
                      where isFormalInForX n = case (lab withParameters n) of
                              Just (FormalIn  x') -> x == x'
                              Nothing             -> error "no such node"
                              _                   -> False
         ]
        entryExits = [ (entry, exit) | procedure <- Set.toList $ staticProcedures,
                                       let entry = entryOf procedure,
                                       let exit  = exitOf procedure
                     ]
        callReturns = [ (call, return) | (call, return, CallSummary) <- labEdges tcfg]



implicitDataDependenceGraphP :: DynGraph gr => Program gr -> (gr SDGNode Dependence, ParameterMaps)
implicitDataDependenceGraphP p@(Program { tcfg, mainThread, entryOf, exitOf, procedureOf, staticProcedureOf, staticProcedures }) = (implicitDataDependenceGraph, parameterMaps)
  where (withParameters, parameterMaps@(ParameterMaps { formalInFor, formalOutFor, actualInsFor, actualOutsFor, parameterNodesFor })) = withParameterNodes p
        reaching = reachingDefsP p
        allVars = vars p
        implicitDataDependenceGraph = mkGraph (labNodes withParameters) implicitDataDependences
        implicitDataDependences = [
           (formalIn, actualIn, DataDependence)
              | (entry, exit)  <- entryExits,
                let formals = Set.toList $ parameterNodesFor ! (entry, exit),
                (call, return) <- callReturns, staticProcedureOf call == staticProcedureOf entry, -- TODO: performance
                let actuals = Set.toList $ parameterNodesFor ! (call, return),
                
                (formalIn, Just (FormalIn x   ))   <- [ (n, lab withParameters n) | n <- formals],
                (actualIn, Just (ActualIn x' _))   <- [ (n, lab withParameters n) | n <- actuals], x == x'
         ] ++ [
           (actualOut, formalOut, DataDependence)
              | (entry, exit)  <- entryExits,
                let formals = Set.toList $ parameterNodesFor ! (entry, exit),
                (call, return) <- callReturns, staticProcedureOf call == staticProcedureOf entry, -- TODO: performance
                let actuals = Set.toList $ parameterNodesFor ! (call, return),
                
                (formalOut, Just (FormalOut x   )) <- [ (n, lab withParameters n) | n <- formals],
                (actualOut, Just (ActualOut x' _)) <- [ (n, lab withParameters n) | n <- actuals], x == x'
         ] ++ [
           (formalIn, formalOut, DataDependence)
              | (entry, exit)  <- entryExits,
                let formals = Set.toList $ parameterNodesFor ! (entry, exit),
                let reachingExit = reaching ! exit,

                (formalIn,  Just (FormalIn  x ))   <- [ (n, lab withParameters n) | n <- formals],
                (formalOut, Just (FormalOut x'))   <- [ (n, lab withParameters n) | n <- formals], x == x'
         ]
        entryExits = [ (entry, exit) | procedure <- Set.toList $ staticProcedures,
                                       let entry = entryOf procedure,
                                       let exit  = exitOf procedure
                     ]
        callReturns = [ (call, return) | (call, return, CallSummary) <- labEdges tcfg]



dataDependenceGraphViaIndependenceP :: DynGraph gr => Program gr -> (gr SDGNode Dependence, ParameterMaps)
dataDependenceGraphViaIndependenceP p@(Program { tcfg, mainThread, entryOf, procedureOf}) =
        assert (paramaterMaps1 == paramaterMaps2) $
        assert (paramaterMaps2 == paramaterMaps3) $
        (mergeTwoGraphs nonTrivialDataDependenceGraph trivialDataDependenceGraph, paramaterMaps1)
  where (implicitDataDependenceGraph,   paramaterMaps1) = implicitDataDependenceGraphP p
        (nonTrivialDataDependenceGraph, paramaterMaps2) = nonTrivialDataDependenceGraphP p
        (trivialDataIndependenceGraph,  paramaterMaps3) = trivialDataIndependenceGraphP p

        trivialDataDependenceGraph =   delEdges [ (from, to) | (from, to, DataIndependence) <- labEdges trivialDataIndependenceGraph ]
                                     $ implicitDataDependenceGraph




reachingDefsP ::  DynGraph gr => Program gr -> Map Node (Map Var (Set Definition))
reachingDefsP p@(Program { tcfg, entryOf, exitOf, mainThread, procedureOf, staticProcedures }) =
     (㎲⊒) (Map.fromList [(entry, allVarsReachedByInitial)] ⊔ Map.fromList [(n, Map.empty) | n <- nodes tcfg]) reachingDefsGivenMustKillF
  where reachingDefsGivenMustKillF = reachingDefsFFor
          (tcfg)
          (allVarsReachedByInitial)
        entry = entryOf $ procedureOf $ mainThread
        allVars = vars p
        allVarsReachedByInitial = Map.fromList [(x, Set.fromList [Initial]) | x <- Set.toList $ allVars ]


reachingDefsFFor :: DynGraph gr =>
    gr a CFGEdge ->
    Map Var (Set Definition) -> 
    Map Node (Map Var (Set Definition)) ->
    Map Node (Map Var (Set Definition))
reachingDefsFFor graph allVarsReachedByInitial reachingDefs =
    reachingDefs ⊔ Map.fromList [(n, (∐) [ transfer e (reachingDefs ! m) | (m,label) <- lpre graph n, let e = (m,n,label) ]) | n <- nodes graph  ]
  where
    transfer :: (Node, Node, CFGEdge) -> Map Var (Set Definition) -> Map Var (Set Definition)
    transfer e@(_,_,Guard _ _)   reachingDefs = reachingDefs
    transfer e@(_,_,Assign x _)  reachingDefs = Map.insert x (Set.fromList [ CFGEdge e ]) reachingDefs
    transfer e@(_,_,Read   x _)  reachingDefs = Map.insert x (Set.fromList [ CFGEdge e ]) reachingDefs
    transfer e@(_,_,Def    x)    reachingDefs = Map.insert x (Set.fromList [ CFGEdge e ]) reachingDefs
    transfer e@(_,_,Use    x)    reachingDefs = reachingDefs
    transfer e@(_,_,Print  _ _)  reachingDefs = reachingDefs
    transfer e@(_,_,Spawn)       reachingDefs = allVarsReachedByInitial
    transfer e@(_,_,NoOp)        reachingDefs = reachingDefs
    transfer e@(_,_,Call)        reachingDefs = allVarsReachedByInitial
    transfer e@(_,_,Return)      reachingDefs = Map.empty
    transfer e@(m,n,CallSummary) reachingDefs = Map.fromList [ (x, Set.fromList [ CFGEdge e ]) | x <- allVars ]
      where [entry] =  [ entry | (entry, Call)   <- lsuc graph m ]  -- TODO: handle virtual calls
            [exit]  =  [ exit  | (exit,  Return) <- lpre graph n ]  -- TODO: handle virtual calls
            allVars = Map.keys allVarsReachedByInitial





strongReachingDefsP ::  DynGraph gr => Program gr -> Map Node (Map Var (Set Definition))
strongReachingDefsP p@(Program { tcfg, entryOf, exitOf, mainThread, procedureOf, staticProcedures }) =
     (㎲⊒) (Map.fromList [(entry, allVarsReachedByInitial)] ⊔ Map.fromList [(n, Map.empty) | n <- nodes tcfg]) reachingDefsGivenMustKillF
  where reachingDefsGivenMustKillF = reachingDefsGivenMustKillFFor
          (tcfg)
          (allVarsReachedByInitial)
          (mustKill p)
        entry = entryOf $ procedureOf $ mainThread
        allVars = vars p
        allVarsReachedByInitial = Map.fromList [(x, Set.fromList [Initial]) | x <- Set.toList $ allVars ]


reachingDefsGivenMustKillFFor :: DynGraph gr =>
    gr a CFGEdge ->
    Map Var (Set Definition) -> 
    Set MustKill ->
    Map Node (Map Var (Set Definition)) ->
    Map Node (Map Var (Set Definition))
reachingDefsGivenMustKillFFor graph allVarsReachedByInitial mustKills reachingDefs =
    reachingDefs ⊔ Map.fromList [(n, (∐) [ transfer e (reachingDefs ! m) | (m,label) <- lpre graph n, let e = (m,n,label) ]) | n <- nodes graph  ]
  where
    transfer :: (Node, Node, CFGEdge) -> Map Var (Set Definition) -> Map Var (Set Definition)
    transfer e@(_,_,Guard _ _)   reachingDefs = reachingDefs
    transfer e@(_,_,Assign x _)  reachingDefs = Map.insert x (Set.fromList [ CFGEdge e ]) reachingDefs
    transfer e@(_,_,Read   x _)  reachingDefs = Map.insert x (Set.fromList [ CFGEdge e ]) reachingDefs
    transfer e@(_,_,Def    x)    reachingDefs = Map.insert x (Set.fromList [ CFGEdge e ]) reachingDefs
    transfer e@(_,_,Use    x)    reachingDefs = reachingDefs
    transfer e@(_,_,Print  _ _)  reachingDefs = reachingDefs
    transfer e@(_,_,Spawn)       reachingDefs = allVarsReachedByInitial
    transfer e@(_,_,NoOp)        reachingDefs = reachingDefs
    transfer e@(_,_,Call)        reachingDefs = allVarsReachedByInitial
    transfer e@(_,_,Return)      reachingDefs = Map.empty
    transfer e@(m,n,CallSummary) reachingDefs = Map.union
        (               Map.fromList [ (x, Set.fromList [ CFGEdge e ]) | MustKill (entry', exit') x <- Set.toList $ mustKills, entry' == entry, exit' == exit ])
        (reachingDefs ⊔ Map.fromList [ (x, Set.fromList [ CFGEdge e ]) | x <- allVars ])
      where [entry] =  [ entry | (entry, Call)   <- lsuc graph m ]  -- TODO: handle virtual calls
            [exit]  =  [ exit  | (exit,  Return) <- lpre graph n ]  -- TODO: handle virtual calls
            allVars = Map.keys allVarsReachedByInitial


