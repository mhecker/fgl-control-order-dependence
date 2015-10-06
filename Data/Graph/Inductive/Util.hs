module Data.Graph.Inductive.Util where

import Util

import Data.Maybe (fromJust)
import Data.Graph.Inductive.Graph hiding (labnfilter) -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Query.DFS (scc)


-- adapted from from https://hackage.haskell.org/package/gbu-0.1/
mergeTwoGraphs :: DynGraph gr => gr a b -> gr a b -> gr a b
mergeTwoGraphs g1 g2 = foldr insEdge g1' $ labEdges g2
 where g1' = foldr mergeNode g1 $ labNodes g2
       mergeNode (n,a) g =
         if n `gelem` g1 then g
                         else insNode (n,a) g

-- | Returns the subgraph only containing the nodes which satisfy the
-- given predicate.
nfilter :: Graph gr => (Node -> Bool) -> gr a b -> gr a b
nfilter f = labnfilter (f . fst)


-- | Returns the subgraph only containing the labelled nodes which
-- satisfy the given predicate.
labnfilter :: Graph gr => (LNode a -> Bool) -> gr a b -> gr a b
labnfilter p gr = delNodes (map fst . filter (not . p) $ labNodes gr) gr


isInCycle :: Graph gr => gr a b -> Node -> Bool
isInCycle graph node = length component > 1
  where component = the (node `elem`) $ scc graph
