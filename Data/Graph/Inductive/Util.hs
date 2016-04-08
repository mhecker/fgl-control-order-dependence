module Data.Graph.Inductive.Util where

import Util

import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Control.Monad(liftM2)

import Data.Graph.Inductive.Graph hiding (labnfilter) -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Query.DFS (scc)
import Data.Graph.Inductive.Query.TransClos (trc)


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


-- | The condensation of the given graph by equivalence classes
-- adapted from Data.Graph.Inductive.Query.DFS.condensation
eqGraph :: Graph gr => [[Node]] -> gr a b -> gr [Node] ()
eqGraph classes gr = mkGraph vs es
  where
    vs = zip [1..] classes
    vMap = Map.fromList $ map swap vs

    swap = uncurry $ flip (,)

    getN = (vMap Map.!)
    es = [ (getN c1, getN c2, ()) | c1 <- classes, c2 <- classes
                                  , (c1 /= c2) && any (hasEdge gr) (liftM2 (,) c1 c2) ]


-- via http://dx.doi.org/10.1016/0167-6423(89)90039-7
trrAcyclic :: DynGraph gr => gr a () -> gr a ()
trrAcyclic graph = trrAcyclicCurrent closure (nodes graph)
  where closure = delEdges [(n,n) | n <- nodes graph] $ trc graph
        trrAcyclicCurrent g []     = g
        trrAcyclicCurrent g (k:ks) =
            trrAcyclicCurrent (delEdges [(i,j) | i <- pre g k,
                                                 j <- suc g k
                                        ]
                                        g
                              )
                              ks
