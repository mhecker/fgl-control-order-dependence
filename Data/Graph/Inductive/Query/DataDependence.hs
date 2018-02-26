{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.DataDependence where

import Control.Monad.Gen
import Control.Monad

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
        []      -> error "not found"
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
    formalInFor   :: Map Node Node,
    formalOutFor  :: Map Node Node,
    actualInsFor  :: Map Node (Set Node),
    actualOutsFor :: Map Node (Set Node)
  } deriving (Eq, Show)

withParameterNodes :: DynGraph gr => Program gr -> (gr SDGNode CFGEdge, ParameterMaps)
withParameterNodes p@(Program { tcfg, entryOf, exitOf, staticProcedures })
    | Set.null allVars = (lifted, ParameterMaps Map.empty Map.empty Map.empty Map.empty)
    | otherwise = (graphWithParameterNodes, ParameterMaps { formalInFor = formalInFor, formalOutFor = formalOutFor, actualInsFor = actualInsFor, actualOutsFor = actualOutsFor })

  where (min, max) = nodeRange tcfg
        allVars = vars p
        lifted = nmap CFGNode tcfg
        graphWithParameterNodes = runGenFrom (max + 1) $ do
          withFormals <- addFormals allVars [(entryOf procedure, exitOf procedure) | procedure <- Set.toList $ staticProcedures] lifted
          withActuals <- addActuals allVars [(n,m)                                 | (n,m, CallSummary) <- labEdges withFormals] withFormals
          return withActuals
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
        actualInsFor = invert formalInFor
        actualOutsFor = invert formalOutFor


addFormals :: DynGraph gr => Set Var -> [(Node, Node)] -> gr SDGNode CFGEdge -> Gen Node (gr SDGNode CFGEdge)
addFormals allVars [] graph = return graph
addFormals allVars ((entry, exit):rest) graph = do
        withFormalIns  <- addAfter  entry NoOp Dummy [ (FormalIn  v, Def v) | v <- Set.toList $ allVars ] graph
        withFormalOuts <- addBefore exit             [ (FormalOut v, Use v) | v <- Set.toList $ allVars ] withFormalIns
        addFormals allVars rest withFormalOuts


addActuals :: DynGraph gr => Set Var -> [(Node, Node)] -> gr SDGNode CFGEdge -> Gen Node (gr SDGNode CFGEdge)
addActuals allVars [] graph = return graph
addActuals allVars ((call, return):rest) graph = do
        withActualIns  <- addAfter  call   NoOp Dummy [ (ActualIn  v call, Use v) | v <- Set.toList $ allVars ] graph
        withActualOuts <- addBefore return            [ (ActualOut v call, Def v) | v <- Set.toList $ allVars ] withActualIns
        addActuals allVars rest withActualOuts

addAfter :: DynGraph gr => Node -> b -> a ->  [(a,b)] -> gr a b -> Gen Node (gr a b)
addAfter start startLabel lastLabel nodeLabels graph = do
  nodes <- forM nodeLabels (\(a, b) -> do
      n <- gen
      return ((n, a), b)
   )
  let ((firstNode,_), _) = head nodes
  lastNode <- gen
  let chain =  [ (from, to, e)  | (((from, _),e), ((to, _), _)) <- zip nodes ((tail nodes) ++ [((lastNode, undefined), undefined)]) ]
  let outgoing  = lsuc graph start
  return $ insEdge  (start, firstNode, startLabel)
         $ insEdges chain
         $ insEdges [(lastNode,  m, e) | (m,e) <- outgoing]
         $ delEdges [(start,     m)    | (m,e) <- outgoing]
         $ insNodes (fmap fst nodes)
         $ insNodes [(lastNode, lastLabel)]
         $ graph


addBefore :: DynGraph gr => Node -> [(a,b)] -> gr a b -> Gen Node (gr a b)
addBefore end nodeLabels graph = do
  nodes <- forM nodeLabels (\(a, b) -> do
      n <- gen
      return ((n, a), b)
   )
  let ((firstNode,_), _) = head nodes
  let chain =  [ (from, to, e)  | (((from, _),e), ((to, _), _)) <- zip nodes ((tail nodes) ++ [((end, undefined), undefined)]) ]
  let incoming  = lpre graph end
  return $ insEdges chain
         $ insEdges [(m, firstNode, e) | (m,e) <- incoming]
         $ delEdges [(m, end)          | (m,e) <- incoming]
         $ insNodes (fmap fst nodes)
         $ graph



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
