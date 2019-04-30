{-# LANGUAGE NamedFieldPuns #-}
module Program where

import Data.Graph.Inductive.Graph  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.TransClos (trc)

import qualified Data.Graph.Inductive.Query.DFS as DFS (reachable)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode

import IRLSOD
import Unicode

type StaticThread = Integer
type StaticProcedure = String

data Program gr = Program {
    tcfg :: gr CFGNode CFGEdge,
    staticThreads  :: Set StaticThread,
    procedureOf    :: StaticThread -> StaticProcedure,
    staticProcedureOf :: Node -> StaticProcedure,
    staticProcedures :: Set StaticProcedure,
    mainThread :: StaticThread,
    entryOf :: StaticProcedure -> Node,
    exitOf  :: StaticProcedure -> Node,
    observability :: ObservationalSpecification
}


-- | generate list of labeled nodes
genLNodes :: (Enum a) => a -> Int -> [LNode a]
genLNodes q i = take i (zip [1..] [q..])

vars :: Graph gr => Program gr -> Set Var
vars (Program { tcfg }) = Set.unions [ def tcfg n ∪ use tcfg n | n <- nodes tcfg]

cfgOfThread :: DynGraph gr => Program gr -> StaticThread -> gr CFGNode CFGEdge
cfgOfThread (Program { tcfg, entryOf, procedureOf }) thread = subgraph reachable inThreadOnly
  where inThreadOnly = labefilter (\(n,m,e) -> not $ e ∊ [Spawn, Return]) tcfg
        reachable = DFS.reachable (entryOf $ procedureOf $ thread) inThreadOnly


cfgOfProcedure :: DynGraph gr => Program gr -> StaticProcedure -> gr CFGNode CFGEdge
cfgOfProcedure (Program { tcfg, entryOf }) procedure = subgraph reachable inProcedureOnly
  where inProcedureOnly = labefilter (\(n,m,e) -> not $ e ∊ [Spawn, Call, Return]) tcfg
        reachable = DFS.reachable (entryOf $ procedure) inProcedureOnly
