{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.Util.GraphTransformations where


import Data.Maybe(fromJust)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.Graph.Inductive.Graph

import Unicode
import Data.Graph.Inductive.Util(controlSinks)


sinkShrinkedGraphNoNewExitForSinks :: DynGraph gr => gr a b  -> [[Node]] -> gr () ()
sinkShrinkedGraphNoNewExitForSinks graph sinks = mkGraph (  [ (s,())   | sink <- sinks, let s = head sink]
                                            ++ [ (n,())   | n    <- nodes graph, not $ n ∈ sinkNodes ]
                                          )
                                          (
                                               [ (n,s,())       | sink <- sinks, let s = head sink, s' <- sink, n <- pre graph s', not $ n ∊ sink]
                                            ++ [ (n,m,()) | (n,m) <- edges graph, not $ n ∈ sinkNodes, not $ m ∈ sinkNodes ]
                                          )
    where sinkNodes   = Set.fromList [ x | sink <- sinks, x <- sink]

sinkShrinkedGraph :: DynGraph gr => gr a b  -> Node -> gr () ()
sinkShrinkedGraph graph endNode = foldl (flip insEdge) graph' [ (s,endNode,()) | sink <- sinks, let s = head sink ]
    where sinks  = controlSinks graph
          graph' = insNode (endNode, ()) $ sinkShrinkedGraphNoNewExitForSinks graph sinks 


choiceAtRepresentativesGraphOf :: forall gr a b . (DynGraph gr) => gr a b ->  gr a b
choiceAtRepresentativesGraphOf g = g''
  where g'' :: gr a b
        g'' = mkGraph ((nx, undefined) : (labNodes g))
                ([ e                          | e@(n,m,l) <- labEdges g] ++
                 [ (n,  nx, undefined)        | n <- representants]
                )
 
        representants  = [ head sink | sink <- controlSinks g]
        [nx] = newNodes 1 g


splitRepresentativesGraphOf :: forall gr a b . (DynGraph gr) => gr a b ->  gr a b
splitRepresentativesGraphOf g = g''
  where g'' :: gr a b
        g'' = mkGraph ([ (n', fromJust $ lab g n) | (n,n') <- Map.assocs splitPredOf ] ++ labNodes g)
                ([ e                          | e@(n,m,l) <- labEdges g, not $ m ∊ representants] ++
                 [ (n,  m',  l)               |   (n,m,l) <- labEdges g, Just m' <- [Map.lookup m splitPredOf], n /= m]
                )
 
        representants = [ head sink | sink <- controlSinks g]
        splitPred   = newNodes (length representants) g
        splitPredOf = Map.fromList $ zip representants splitPred

splitRepresentativesGraphNoTrivialOf :: forall gr a b . (DynGraph gr) => gr a b ->  gr a b
splitRepresentativesGraphNoTrivialOf g = g''
  where g'' :: gr a b
        g'' = mkGraph ([ (n', fromJust $ lab g n) | (n,n') <- Map.assocs splitPredOf ] ++ labNodes g)
                ([ e                          | e@(n,m,l) <- labEdges g, not $ m ∊ representants] ++
                 [ (n,  m',  l)               |   (n,m,l) <- labEdges g, Just m' <- [Map.lookup m splitPredOf], n /= m]
                )
 
        representants = [ head sink | sink <- controlSinks g, length sink > 1]
        splitPred   = newNodes (length representants) g
        splitPredOf = Map.fromList $ zip representants splitPred
