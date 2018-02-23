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

import Algebra.Lattice

import Data.Char

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

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
  transfer e@(_,_,Print  _ _) reachingDefs = reachingDefs
  transfer e@(_,_,Spawn)      reachingDefs = reachingDefs
  transfer e@(_,_,NoOp)       reachingDefs = reachingDefs
  transfer e@(_,_,Call)       reachingDefs = initial
  transfer e@(_,_,Return)     reachingDefs = initial
  transfer e@(_,_,CallSummary)reachingDefs = initial



withParameterNodes :: DynGraph gr => Program gr -> gr SDGNode CFGEdge
withParameterNodes  p@(Program { tcfg, mainThread, entryOf, procedureOf}) = undefined

withFormals :: DynGraph gr => Program gr -> gr SDGNode CFGEdge
withFormals  p@(Program { tcfg, mainThread, entryOf, procedureOf, staticProcedures })
    | Set.null allVars = lifted 
    | otherwise = runGenFrom (max + 1) $ do
        withFormals <- addAfter (entryOf $ procedureOf $ mainThread) NoOp Dummy [ (FormalIn v, Def v) | v <- Set.toList $ allVars ] lifted
        return withFormals

  where (min, max) = nodeRange tcfg
        allVars = vars p
        lifted = nmap CFGNode tcfg
        -- formalIns = Map.fromList [ (p, [ FormalIn v | v <- allVars
        --                            ) | p <- staticProcedures
        --             ]
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


dataDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
dataDependenceGraphP p@(Program { tcfg, mainThread, entryOf, procedureOf}) =
    dataDependenceGraph tcfg (vars p) (entryOf $ procedureOf $ mainThread)
