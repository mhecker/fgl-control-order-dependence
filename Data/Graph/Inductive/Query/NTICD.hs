{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.NTICD where

import Data.Maybe(fromJust)

import Data.List(foldl', intersect,foldr1)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import qualified Data.List as List

import Data.List ((\\), nub)


import IRLSOD
import Program

import Util(the, invert', foldM1)
import Unicode


import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic hiding (postorder)
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.DFS (scc, condensation)

import Debug.Trace
import Control.Exception.Base (assert)
tr msg x = seq x $ trace msg x


type T n = (n, n)

type SmnFunctional = Map (Node,Node) (Set (T Node)) -> Map (Node,Node) (Set (T Node))
type SmnFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> SmnFunctional


{- Generic utility functions -}

cdepGraphP :: DynGraph gr => (gr CFGNode CFGEdge -> gr CFGNode Dependence) -> Program gr -> gr CFGNode Dependence 
cdepGraphP graphGen  p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
    foldr mergeTwoGraphs empty [ insEdge (entry, exit, ControlDependence) $ 
                                 graphGen (insEdge (entry, exit, false) $ nfilter (\node -> staticThreadOf node == thread) tcfg)
                               | thread <- Set.toList staticThreads,  let entry = entryOf thread, let exit = exitOf thread ]

cdepGraph :: DynGraph gr => (gr a b -> Map Node (Set Node)) -> gr a b -> gr a Dependence
cdepGraph cdGen graph  = mkGraph (labNodes graph) [ (n,n',ControlDependence) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = cdGen graph


snmGfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmGfp graph f = (𝝂) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

snmLfp :: DynGraph gr => gr a b -> SmnFunctionalGen gr a b -> Map (Node, Node) (Set (T Node))
snmLfp graph f = (㎲⊒) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

ntXcd :: DynGraph gr => (gr a b -> Map (Node, Node) (Set (T Node))) -> gr a b -> Map Node (Set Node)
ntXcd snm graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            m /= n,
                                            let tmn = Set.size $ s ! (m,n),
                                            0 < tmn, tmn < (Set.size $ Set.fromList $ suc graph n)
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snm graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]




{- The functional from [1] Figure 5, which yields an *incorrect* implementation of nticd, both if we take its least or greatest fixed point.

   [1] "A New Foundation for Control Dependence and Slicing for Modern Program Structures", Journal Version

       http://doi.acm.org/10.1145/1275497.1275502

       VENKATESH PRASAD RANGANATH, TORBEN AMTOFT,
       ANINDYA BANERJEE, and JOHN HATCLIFF
       Kansas State University

       and
       MATTHEW B. DWYER
       University of Nebraska
-}

f5 :: DynGraph gr => SmnFunctionalGen gr a b
f5 graph condNodes _ _ _ s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- condNodes, p /= n,
                                                             (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]

                 ⊔ Map.fromList [ ((m,n), s ! (n,n)) | n <- condNodes, m <- suc graph n, m /= n ]


nticdF5GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF5GraphP = cdepGraphP nticdF5Graph

nticdF5Graph :: DynGraph gr => gr a b -> gr a Dependence
nticdF5Graph = cdepGraph nticdF5

nticdF5 :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF5 = ntXcd snmF5

snmF5 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF5 graph = snmLfp graph f5





{- two correct nticd implementations, using the gfp of functional f3/f3' -}
f3 :: DynGraph gr => SmnFunctionalGen gr a b
f3 graph condNodes reachable nextCond toNextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                  -- m `elem` reachable x,
                                                                  m `elem` toNextCond x]
                                  ) | m <- nodes graph, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                  m `elem` reachable x,
                                                                  Just n <- [nextCond x], 
                                                                  (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]

f3' :: DynGraph gr => SmnFunctionalGen gr a b
f3' graph condNodes reachable nextCond toNextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,p),
                        Set.fromList  [ (p,x) | x <- (suc graph p), m `elem` reachable x,
                                                                    m `elem` toNextCond x]
                      ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), m `elem` reachable x,
                                                                    Just n <- [nextCond x],
                                                (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                      ]
                    ) | m <- nodes graph, p <- condNodes]


nticdF3GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3GraphP = cdepGraphP nticdF3Graph

nticdF3Graph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3Graph = cdepGraph nticdF3

nticdF3 :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3 = ntXcd snmF3

snmF3 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3 graph = snmGfp graph f3


nticdF3'GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'GraphP = cdepGraphP nticdF3'Graph

nticdF3'Graph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3'Graph = cdepGraph nticdF3'

nticdF3' :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3' = ntXcd snmF3'

snmF3' :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3' graph = snmGfp graph f3'



f3'dual :: DynGraph gr => SmnFunctionalGen gr a b
f3'dual graph condNodes reachable nextCond toNextCond s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise =
                   Map.fromList [ ((m,p), (
                        Set.fromList  [ (p,x) | x <- (suc graph p), not $ m `elem` toNextCond x]
                      ⊓ Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x], (Set.size $ s ! (m,n)) /= 0 ]
                    ) ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), not $ m `elem` reachable x ]
                   ) | m <- nodes graph, p <- condNodes]
  where all p m = [ (p,x) | x <- (suc graph p)]


nticdF3'dualGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'dualGraphP = cdepGraphP nticdF3'dualGraph

nticdF3'dualGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdF3'dualGraph = cdepGraph nticdF3'dual

nticdF3'dual :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdF3'dual = ntXcd snmF3'dual

snmF3'dual :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3'dual graph = snmLfp graph f3'dual


{- the same, with less memory consumption -}
-- here, for given node node m, S[m,p] is represented by S[m',p] for that condition or join node m'
-- which preceeds  m in the graph (or: m itself, if there is no such node)
nticdF3'dualWorkListSymbolicGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3'dualWorkListSymbolicGraphP = cdepGraphP nticdF3'dualWorkListSymbolicGraph

nticdF3'dualWorkListSymbolicGraph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3'dualWorkListSymbolicGraph = cdepGraph nticdF3'dualWorkListSymbolic

nticdF3'dualWorkListSymbolic :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3'dualWorkListSymbolic = ntXcd snmF3'dualWorkListSymbolicLfp

snmF3'dualWorkListSymbolicLfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3'dualWorkListSymbolicLfp graph = snmWorkList (Set.fromList [ (m,n,x) | p <- condNodes, m <- representants, Set.size (smnInit ! (m,p)) /= 0, (n,x) <- prevCondsWithSucc p ]) smnInit
  where snmWorkList :: Set (Node, Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = expandSymbolic s
          | otherwise         = snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p,x), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' = if (not $ m `elem` toNextCond x) then (Set.insert (p,x) smp) else smp
                    influenced = if (Set.size smp == 0 && Set.size smp' > 0)
                                   then Set.fromList [ (m,n,x') | (n,x') <- prevCondsWithSucc p ]
                                   else Set.empty

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- condNodes, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, not $ m `elem` reachable x]) | p <- condNodes, m <- representants]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        prevCondsWithSucc = prevCondsWithSuccNode graph
        representantOf = prevRepresentantNodes graph
        representants = [ m | m <- nodes graph, (length (pre graph m) /= 1) ∨ (let [n] = pre graph m in n `elem` condNodes)]
        trncl = trc graph
        expandSymbolic s = Map.fromList [ ((m,p), s ! (representantOf m, p)) | p <- condNodes, m <- nodes graph]

{- A Worklist-Implementation of nticd, based on f3 -}
nticdF3WorkListGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3WorkListGraphP = cdepGraphP nticdF3WorkListGraph

nticdF3WorkListGraph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3WorkListGraph = cdepGraph nticdF3WorkList

nticdF3WorkList :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3WorkList = ntXcd snmF3WorkListGfp

snmF3WorkListGfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3WorkListGfp graph = snmWorkList (Set.fromList [ (m,p) | m <- nodes graph, p <- condNodes ]) smnInit
  where snmWorkList :: Set (Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' =   Set.fromList  [ (p,x) | x <- (suc graph p), m `elem` toNextCond x]
                           ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x],
                                                     (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                           ]
                    influenced = if (Set.size smp == Set.size smp')
                                   then Set.empty
                                   else Set.fromList [ (m,n) | n <- prevConds p ]

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, m `elem` reachable x]) | m <- nodes graph, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        prevConds = prevCondNodes graph
        trncl = trc graph

{- the same, with less memory consumption -}
-- here, for given node node m, S[m,p] is represented by S[m',p] for that condition or join node m'
-- which preceeds  m in the graph (or: m itself, if there is no such node)
nticdF3WorkListSymbolicGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdF3WorkListSymbolicGraphP = cdepGraphP nticdF3WorkListSymbolicGraph

nticdF3WorkListSymbolicGraph :: DynGraph gr => gr a b -> gr a Dependence
nticdF3WorkListSymbolicGraph = cdepGraph nticdF3WorkListSymbolic

nticdF3WorkListSymbolic :: DynGraph gr => gr a b -> Map Node (Set Node)
nticdF3WorkListSymbolic = ntXcd snmF3WorkListSymbolicGfp

snmF3WorkListSymbolicGfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3WorkListSymbolicGfp graph = snmWorkList (Set.fromList [ (m,p) | p <- condNodes, m <- representants  ]) smnInit
  where snmWorkList :: Set (Node, Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = expandSymbolic s
          | otherwise         = snmWorkList (influenced ⊔ workList') (Map.insert (m,p) smp' s)
              where ((m,p), workList') = Set.deleteFindMin workList
                    smp  = s ! (m,p)
                    smp' =   Set.fromList  [ (p,x) | x <- (suc graph p), m `elem` toNextCond x]
                           ⊔ Set.fromList  [ (p,x) | x <- (suc graph p), Just n <- [nextCond x],
                                                     (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                           ]
                    influenced = if (Set.size smp == Set.size smp')
                                   then Set.empty
                                   else Set.fromList [ (m,n) | n <- prevConds p ]
--                                 else Set.fromList [ (m,n) | n <- condNodes, x <- (suc graph n), Just p == nextCond x ]

        smnInit =  Map.fromList [ ((m,p), Set.empty) | m <- condNodes, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Set.fromList [ (p,x) | x <- suc graph p, m `elem` reachable x]) | p <- condNodes, m <- representants]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        prevConds = prevCondNodes graph
        representantOf = prevRepresentantNodes graph
        representants = [ m | m <- nodes graph, (length (pre graph m) /= 1) ∨ (let [n] = pre graph m in n `elem` condNodes)]
        trncl = trc graph
        expandSymbolic s = Map.fromList [ ((m,p), s ! (representantOf m, p)) | p <- condNodes, m <- nodes graph]



{- A correct implementation of ntscd, as given in [1], Figure 4,
   using the lfp of functional f4
-}
ntscdF4GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF4GraphP p = cdepGraphP ntscdF4Graph p

ntscdF4Graph :: DynGraph gr => gr a b -> gr a Dependence
ntscdF4Graph = cdepGraph ntscdF4 

ntscdF4 :: DynGraph gr => gr a b -> Map Node (Set Node)
ntscdF4 = ntXcd snmF4

snmF4 :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF4 graph = snmLfp graph f4

f4 graph condNodes _ _ _ s
  | (∃) [ (m,p,n) | m <- nodes graph, p <- condNodes, n <- condNodes, p /= n ]
        (\(m,p,n) ->   (Set.size $ s ! (m,n)) > (Set.size $ Set.fromList $ suc graph n)) = error "rofl"
  | otherwise = -- tr ("\n\nIteration:\n" ++ (show s)) $
                   Map.fromList [ ((x,p), Set.fromList [ (p,x) ]) | p <- condNodes, x <- suc graph p ]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- nodes graph, [ m ] == suc graph n])  | p <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,p), (∐) [ s ! (n,p) | n <- condNodes, p /= n,
                                                             (Set.size $ s ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]



{- A correct implementation of ntscd, by a tiny modification of [1], Figure 4 -}
ntscdF4WorkListGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF4WorkListGraphP = cdepGraphP ntscdF4WorkListGraph

ntscdF4WorkListGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdF4WorkListGraph = cdepGraph ntscdF4WorkList

ntscdF4WorkList :: DynGraph gr => gr a b -> Map Node (Set Node)
ntscdF4WorkList = ntXcd snmF4WorkListLfp

snmF4WorkListLfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF4WorkListLfp graph = snmWorkList (Set.fromList [ m | n <- condNodes, m <- suc graph n ]) smnInit
  where snmWorkList :: Set (Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ workList') s'
              where (n, workList') = Set.deleteFindMin workList
                    tn = Set.size $ Set.fromList $ suc graph n
                    s'
                     | tn == 1   = let [m] = nub $ suc graph n in     s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) |                                                 p <- condNodes ]
                     | tn  > 1   =                                    s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes ]
                     | otherwise = s 
                    influenced 
                     | tn == 1   = let [m] = nub $ suc graph n in  Set.fromList [ m |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | tn  > 1   =                                 Set.fromList [ m | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | otherwise = Set.empty
        smnInit =  Map.fromList [ ((m,n), Set.empty)              | n <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


{- A faulty implementation of ntscd, as given in [1], Figure 4 -}
ntscdFig4GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdFig4GraphP = cdepGraphP ntscdFig4Graph

ntscdFig4Graph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdFig4Graph = cdepGraph ntscdFig4

ntscdFig4 :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntscdFig4 = ntXcd snmFig4Lfp

snmFig4Lfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmFig4Lfp graph = snmWorkList (Set.fromList [ m | n <- condNodes, m <- suc graph n ]) smnInit
  where snmWorkList :: Set (Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ workList') s'
              where (n, workList') = Set.deleteFindMin workList
                    tn = Set.size $ Set.fromList $ suc graph n
                    s'
                     | tn == 1   = let [m] = nub $ suc graph n in     s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) |                                                 p <- condNodes ]
                     | tn  > 1   =                                    s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes ]
                     | otherwise = s 
                    influenced 
                     | tn == 1   = let [m] = nub $ suc graph n in  Set.fromList [ m |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                     | tn  > 1   =                                 Set.fromList [ m | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                     | otherwise = Set.empty
        smnInit =  Map.fromList [ ((m,n), Set.empty)              | n <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



{- A faulty implementation of nticd, as given in [1], Figure 5, with attempts to fix the worklist updates  -}
nticdFig5GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdFig5GraphP = cdepGraphP nticdFig5Graph

nticdFig5Graph :: DynGraph gr => gr a b ->  gr a Dependence
nticdFig5Graph = cdepGraph nticdFig5

nticdFig5 :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdFig5 = ntXcd snmFig5Lfp

snmFig5Lfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmFig5Lfp graph = snmWorkList (Set.fromList [ m | n <- condNodes, m <- suc graph n ]) smnInit
  where snmWorkList :: Set (Node) -> Map (Node, Node) (Set (T Node)) -> Map (Node, Node) (Set (T Node))
        snmWorkList workList s
          | Set.null workList = s
          | otherwise         = snmWorkList (influenced ⊔ influenced2 ⊔ workList') s''
              where (n, workList') = Set.deleteFindMin workList
                    tn = Set.size $ Set.fromList $ suc graph n
                    s'
                     | tn == 1   = let [m] = nub $ suc graph n in     s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) |                                                 p <- condNodes ]
                     | tn  > 1   =                                    s ⊔  Map.fromList [ ((m,p), s ! (m,p)  ⊔  s ! (n,p)) | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes ]
                     | otherwise = s
                    influenced
                     | tn == 1   = let [m] = nub $ suc graph n in  Set.fromList [ m |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p |                                                 p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | tn  > 1   =                                 Set.fromList [ m | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)]
                                                                 ⊔ Set.fromList [ p | m <- nodes graph, (Set.size $ s ! (m,n)) == tn, p <- condNodes, s ! (m,p)  /=  s ! (m,p)  ⊔  s ! (n,p)] -- these are missing in their paper
                     | otherwise = Set.empty

                    s''
                     | n `elem` condNodes ∧ (Set.size $ s' ! (n,n)) > 0  =  s' ⊔  Map.fromList [ ((m,n),                               s' ! (m,n)  ⊔  s' ! (n,n)) | m <- suc graph n, m /= n]
                     | otherwise = s'
                    influenced2
                     | n `elem` condNodes ∧ (Set.size $ s' ! (n,n)) > 0  =  Set.fromList [m | m <- suc graph n, m /= n, s' ! (m,n) /=  s' ! (m,n)  ⊔  s' ! (n,n)]
                                                                          ⊔ Set.fromList [n | m <- suc graph n, m /= n, s' ! (m,n) /=  s' ! (m,n)  ⊔  s' ! (n,n)] -- this is missing in their paper
                     | otherwise = Set.empty

        smnInit =  Map.fromList [ ((m,n), Set.empty)              | n <- condNodes, m <- nodes graph]
                 ⊔ Map.fromList [ ((m,n), Set.fromList [ (n,m) ]) | n <- condNodes, m <- suc graph n ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



{- A correct implementation of ntscd,
   using the lfp of functional f3.

   This shows that ntscd and nticd are, essentially, the lfp/gfp (respectively) of the *same* functional f3.
-}
ntscdF3GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdF3GraphP = cdepGraphP ntscdF3Graph

ntscdF3Graph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdF3Graph = cdepGraph ntscdF3

ntscdF3 :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntscdF3 = ntXcd snmF3Lfp

snmF3Lfp :: DynGraph gr => gr a b -> Map (Node, Node) (Set (T Node))
snmF3Lfp graph = snmLfp graph f3


nticdSinkContractionGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdSinkContractionGraphP p = cdepGraphP nticdSinkContractionGraph p 
  where  [endNodeLabel] = newNodes 1 $ tcfg p

nticdSinkContractionGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdSinkContractionGraph = cdepGraph nticdSinkContraction

nticdSinkContraction :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdSinkContraction graph              = Map.fromList [ (n, cdepClassic ! n) | n <- nodes graph, not $ n ∈ sinkNodes ]
                                        ⊔ Map.fromList [ (n, (∐) [ Set.fromList sink | s <- Set.toList $ cdepClassic ! n,
                                                                                        s ∈ sinkNodes,
                                                                                        let sink = the (s `elem`) sinks ]
                                                         ) | n <- nodes graph, not $ n ∈ sinkNodes
                                                       ]
                                        ⊔ Map.fromList [ (n, Set.empty) | n <- Set.toList sinkNodes ]
    where [endNode] = newNodes 1 graph
          sinks = controlSinks graph
          cdepClassic = controlDependence (sinkShrinkedGraph graph endNode) endNode
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]

sinkShrinkedGraph :: DynGraph gr => gr a b  -> Node -> gr () ()
sinkShrinkedGraph graph endNode   = mkGraph (  [ (s,())   | sink <- sinks, let s = head sink]
                                            ++ [ (n,())   | n    <- nodes graph, not $ n ∈ sinkNodes ]
                                            ++ [ (endNode, ()) ]
                                          )
                                          (
                                               [ (n,s,())       | sink <- sinks, let s = head sink, s' <- sink, n <- pre graph s', not $ n ∈ sink]
                                            ++ [ (s,endNode,()) | sink <- sinks, let s = head sink ]
                                            ++ [ (n,m,()) | (n,m) <- edges graph, not $ n ∈ sinkNodes, not $ m ∈ sinkNodes ]
                                          )
    where sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]
          sinks = controlSinks graph




nticdIndusGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdIndusGraphP = cdepGraphP nticdIndusGraph

nticdIndusGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdIndusGraph = cdepGraph nticdIndus

nticdIndus :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdIndus graph = go (nodes graph) [] deps
    where
      go []             seen newDeps = newDeps
      go (dependent:ds) seen newDeps = go ds seen newDeps'
        where newDeps' = process dependent newDeps
      process dependent newDeps = run dependent [ d | d <- nodes graph, dependent ∈ (deps ! d)] [] newDeps
        where 
          run dependent []            seen newDeps = newDeps
          run dependent (dependee:ds) seen newDeps
            | dependee `elem` seen                                       = run
                dependent
                ds
                seen
                newDeps
            | shouldRemoveDepBetween dependee dependent sinkNodes = run
                dependent
                (ds ++ [ d | d <- nodes graph, dependee ∈ (deps ! d) ])
                (dependee:seen)
                (Map.update (\dependents -> Just $ Set.delete  dependent  dependents) dependee newDeps)
            | otherwise               = run
                dependent
                ds
                (dependee:seen)
                (Map.update (\dependents -> Just $ Set.insert dependent  dependents) dependee newDeps)
          sinkNodes = nodesOfSinksNotContainingNode dependent
      
      deps = ntscdF4 graph
      csinks = controlSinks graph
      nodesOfSinksNotContainingNode node = [ n | sink <- csinks, not $ node `elem` sink, n <- sink]
      shouldRemoveDepBetween dependee dependent sinkNodes = run [dependee] [dependent]
        where run []     seen = True
              run (n:ns) seen
                | n `elem` seen   = run ns seen
                | n `elem` sinkNodes = False
                | otherwise = run ((suc graph n) ++ ns) (n:seen)



{- The definition of nticd -}
nticdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
nticdDefGraphP = cdepGraphP nticdDefGraph

nticdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
nticdDefGraph  = cdepGraph nticdDef

nticdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph, nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inPath` (nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inPath` (nl,path))
                                         ]
                       )
                     | ni <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inPath = inSinkPathFor graph

inSinkPathFor graph' n (s, path) = inSinkPathFromEntries [s] path
  where 
    inSinkPathFromEntries _       (SinkPath []           controlSink) = n `elem` controlSink
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n `elem` scc = (∀) entries (\entry -> let doms = (dom graph' entry) in
                          (∀) exits (\exit -> let domsexit = doms `get` exit in
                                 (entry /= exit || n == entry) && n `elem` domsexit)
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' `elem` next ]
            exits = [ n | (n,_) <- borderEdges ]
            get assocs key = fromJust $ List.lookup key assocs



{- The definition of ntscd -}
ntscdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntscdDefGraphP = cdepGraphP ntscdDefGraph

ntscdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntscdDefGraph  = cdepGraph ntscdDef

ntscdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntscdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (maximalPaths ! nk) (\path ->       nj `inPath` (nk,path)),
                                                (∃) (maximalPaths ! nl) (\path -> not $ nj `inPath` (nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where sccs = scc graph
        sccOf m =  the (m `elem`) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.

inPathFor graph' doms n (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  (MaximalPath []            endScc endNodes@(end:_))
                    | n `elem` endScc  = (∀) entries (\entry -> let domsEnd = (doms ! entry) `get` end in
                                                                (entry /= end || n == entry) && n `elem` domsEnd
                                         )
                                       ∨ (n `elem` endNodes)
                    | otherwise =  False
                inPathFromEntries entries  (MaximalPath (scc:prefix)  endScc endNodes)
                    | n `elem` scc = (∀) entries (\entry ->
                                      (∀) exits (\exit -> let domsexit = (doms ! entry) `get` exit in
                                             (entry /= exit || n == entry) && n `elem` domsexit)
                                     )
                                     ∨ (n `elem` endNodes)
                    | otherwise    =  inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' `elem` next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = fromJust $ List.lookup key assocs


mdomOf ::  DynGraph gr => gr a b -> Map Node (Set Node)
mdomOf graph = -- trace ("Sccs: " ++ (show $ length sccs) ++ "\t\tSize: " ++ (show $ length $ nodes graph)) $
               Map.fromList [ (y, Set.fromList [ x | x <- nodes graph, x `mdom` y]) | y <- nodes graph]
  where mdom x y =  (∀) (maximalPaths ! y) (\path ->       x `inPath` (y,path))
        maximalPaths = maximalPathsForNodes graph (nodes graph)
        inPath = inPathFor graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ]
        sccs = scc graph
        sccOf m =  the (m `elem`) $ sccs

sinkdomOf ::  DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOf graph = Map.fromList [ (y, Set.fromList [ x | x <- nodes graph, x `sinkdom` y]) | y <- nodes graph]
  where sinkdom x y =  (∀) (sinkPaths ! y) (\path ->       x `inPath` (y,path))
        sinkPaths = sinkPathsFor graph
        inPath = inSinkPathFor graph


-- sinkdomOfLfp ::  DynGraph gr => gr a b -> Map Node (Set Node)
-- sinkdomOfLfp graph = (㎲⊒) init f
--   where init =  Map.fromList [ (y, Set.empty) | y <- nodes graph]
--               ⊔ Map.fromList [ (y, Set.fromList $ sccOfY) | y <- nodes graph, let sccOfY = sccOf y, sccOfY `elem` sinks]
--               ⊔ Map.fromList [ (y, Set.fromList [y]) | y <- nodes graph]
--         f sinkdomOf = sinkdomOf
--                     ⊔ Map.fromList [ (y, (∏) [ sinkdomOf ! x  | y' <- sccOfY , x <- suc graph y', not $ x `elem` sccOfY])
--                                    |  y <- nodes graph, let sccOfY = sccOf y, not $ sccOfY `elem` sinks ]
--                     ⊔ Map.fromList [ (y, (∏) [ sinkdomOf ! y' | y' <- sccOfY , x <- suc graph y', not $ x `elem` sccOfY])
--                                    |  y <- nodes graph, let sccOfY = sccOf y, not $ sccOfY `elem` sinks ]
--                     ⊔ Map.fromList [ (y, (∏) [ sinkdomOf ! x | x <- suc graph y, x /= y ])
--                                    |  y <- nodes graph,                       not $ null $ filter (/= y) $                                  suc graph y]
--         sinks = controlSinks graph
--         sccs = scc graph
--         sccOf m =  the (m `elem`) $ sccs





type DomFunctional = Map Node (Set Node) ->  Map Node (Set Node)
type DomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> DomFunctional

domOfLfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
domOfLfp graph f = (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

domOfGfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
domOfGfp graph f = (𝝂) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
             ⊔ Map.fromList [ (y, Set.fromList $ reachable y) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph



fSinkDom graph _ _ nextCond toNextCond = f 
  where f sinkdomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Set.fromList $ toNextCond y)               | y <- nodes graph]
                    ⊔ Map.fromList [ (y,  (∏) [ sinkdomOf ! x | x <- suc graph n ]) | y <- nodes graph, Just n <- [nextCond y]]
sinkdomOfGfp graph = domOfGfp graph fSinkDom
mdomOfLfp graph = domOfLfp graph fSinkDom



fSinkDomDual graph _ reachable nextCond toNextCond = f 
  where f sinkdomOfCompl = Map.fromList [ (y, (
                             Set.fromList [ x | x <- nodes graph, x /= y]
                           ⊓ Set.fromList [ x | x <- nodes graph, not $ x ∈ ny]
                           ⊓ ((∐) [ sinkdomOfCompl ! x | Just n <- [nextCond y], x <- suc graph n ])
                           -- ⊓ ( case nextCond y of Just n  -> (∐) [  (sinkdomOfCompl! x) | x <- suc graph n ]
                           --                        Nothing -> allNodes)
                         ) ⊔ Set.fromList  [ x | x <- nodes graph, not $ x `elem` reachable y ]
                        ) | y <- nodes graph, let ny = Set.fromList $ toNextCond y]
        allNodes = Set.fromList $ nodes graph
sinkdomOfLfp graph = fmap (\s -> allNodes ∖ s) $ domOfLfp graph fSinkDomDual
  where allNodes = Set.fromList $ nodes graph

sinkdomOfisinkdomProperty :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOfisinkdomProperty graph =
          Map.fromList [ (y,
                 Set.fromList [ y ]
               ⊔ (∐) [ sinkdom ! z | z <- suc isinkdom y]
            )
          | y <- nodes graph]
  where sinkdom = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()
        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m `elem`) $ isinkdomSccs

{- this is somewhat inspired by [2]
   [2] Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy
       A Simple, Fast Dominance Algorithm

   http://www.citeulike.org/user/MatzeB/article/571160
-} 
isinkdomOfTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfTwoFinger graph = fmap (\s -> Set.fromList [ Set.findMin s | not $ Set.null s]) $  (㎲⊒) init f
  where init   = Map.fromList [ (x, Set.empty)        | x <- nodes graph]
               ⊔ Map.fromList [ (x, Set.fromList [y]) | x <- nodes graph, (_:y:_) <- [reverse $ toNextCond x]]
        f isinkdom = isinkdom 
                   ⊔ Map.fromList [ (x, Set.fromList [ z | z <- suc graph x,
                                                           z /= x,
                                                           let isinkdomTrc = trc $ insEdge (x,z,()) $ (fromSuccMap isinkdom :: gr () ()),
                                                           (∀) (suc graph x) (\y -> z `elem` (suc isinkdomTrc y))
                                                     ]
                                    )
                                  | x <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

isinkdomOfGfp2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfGfp2 graph = -- fmap (\s -> Set.fromList [ Set.findMin s | not $ Set.null s]) $  (𝝂) init f
                               (𝝂) init f
  where base  =       Map.fromList [ (x, Set.empty )          | x <- nodes graph, (Set.size $ succs x) == 0]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1]
        init  =       base 
                    ⊔ Map.fromList [ (x, Set.fromList [ y | y <- reachable x, y ∈ joinNodes ] )
                                                              | x <- condNodes ]
        f :: Map Node (Set Node) -> Map Node (Set Node)
        f isinkdom = -- traceShow isinkdom $
                     base 
                   ⊔ Map.fromList [ (x, Set.fromList [ z | z <- Set.toList $ isinkdom ! x,
                                                           (∀) (suc graph x) (\y -> z `elem` (suc isinkdomTrc y))
                                                     ]
                                    )
                                  | x <- condNodes]
          where isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: gr () ())
        condNodes = [ x | x <- nodes graph, (Set.size $ succs x) >= 1  ]
        joinNodes = [ x | x <- nodes graph, (Set.size $ preds x) >= 1  ]
        succs x     = Set.delete x $ Set.fromList $ suc graph x
        preds x     = Set.delete x $ Set.fromList $ pre graph x
        reachable x = suc trncl x
        trncl = trc graph



isinkdomOfTwoFinger5 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfTwoFinger5 graph = twoFinger worklist0 confirmed0 isinkdom0 succs0
  where isinkdom0   = Map.fromList [ (x, Set.empty )          | x <- nodes graph]
--                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1, not $ x ∈ sinkNodes]
                    ⊔ Map.fromList [ (x, Set.fromList [y])    | (s:sink) <- controlSinks graph, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
        worklist0   = Map.keysSet $ Map.filter (\x -> x ∈ condNodes   ∧  (not $ x ∈ sinkNodes)) pon2node
        confirmed0  = Set.fromList [ x                        | x <- nodes graph, (Set.size $ succs x) == 1]
                    ⊔ sinkNodes  
        succs  x    = Set.delete x $ Set.fromList $ suc graph x
        succs0      = Map.fromList [ (x, succs x)             | x <- nodes graph]
        condNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ succs x) > 1 ]
        sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- controlSinks graph, x <- sink]
        (node2pon, pon2node) = postorder graph
        
        twoFinger :: Set Integer -> Set Node -> Map Node (Set Node) -> Map Node (Set Node) -> Map Node (Set Node)
        twoFinger worklist confirmed isinkdom remsuccs
            | Set.null worklist = traceShow ("x", "mz", "zs", Set.map (pon2node !) worklist, confirmed, isinkdom, remsuccs) $
                                  -- let confirmedtrc = confirmed0 
                                  --                  ⊔ Set.fromList [ x | x <- Set.toList condNodes,
                                  --                                       x ∈ confirmed,
                                  --                                       ((Set.size $ remsuccs ! x) <= 1 ∧ (∀) (succs x ∖ (remsuccs ! x)) (\y -> let Just n = nextCond y in n ∈ confirmed))
                                  --                                       ∨
                                  --                                       (∀) [ n | y <- Set.toList $ succs x, Just n <- [nextCond y] ] (\n -> n ∈ confirmed) ]
                                  --     nextCond = nextCondNode graph
                                  -- in  (Map.filterWithKey (\x _ -> x ∈ confirmedtrc) isinkdom) ⊔  Map.fromList [ (x, Set.empty ) | x <- nodes graph]
                                  let 
                                      f isinkdom = isinkdom0
                                                 ⊔ Map.fromList [ (x, Set.fromList [ z | z <- Set.toList $ isinkdom ! x,
                                                                                         (∀) (suc graph x) (\y -> z `elem` (suc isinkdomTrc y))
                                                                                   ]
                                                                   )
                                                                | x <- Set.toList $ condNodes ∖ sinkNodes ]
                                        where isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: gr () ())
                                  in   (𝝂) isinkdom f
            | otherwise         = traceShow (x, mz, zs, Set.map (pon2node !) worklist, confirmed, isinkdom, remsuccs) $
                                  if (not $ changed) then twoFinger               worklist'  confirmed'                                   isinkdom  remsuccs'
                                                     else twoFinger (influenced ⊔ worklist') confirmed'  (Map.insert x zs                isinkdom) remsuccs'
          where (pon, worklist')  = Set.deleteFindMin worklist
                x = pon2node ! pon
                -- (x', others) = if (Set.null $ remsuccs ! x) then error $ "remsuccs ! " ++ (show x) else Set.deleteFindMin $ remsuccs ! x
                mz = foldM1 lca (Set.toList $ succs x)
                zs = case mz of
                      Just z  ->  if (x ∈ reachable isinkdom z) then
                                    first     $ Set.fromList [ x' | x' <- Set.toList $ remsuccs ! x, not $ x ∈ reachable isinkdom x'] 
                                  else
                                    Set.fromList [ z ]
                      Nothing ->  if Set.null $ Set.fromList [ x' | x' <- Set.toList $ remsuccs ! x, not $ x ∈ reachable isinkdom x'] then
                                    error "rofl"
                                  else
                                    first     $ Set.fromList [ x' | x' <- Set.toList $ remsuccs ! x, not $ x ∈ reachable isinkdom x']
                confirmed' = case mz of
                      Just z  -> Set.insert x confirmed
                      Nothing ->              confirmed
                remsuccs' :: Map Node (Set Node)
                remsuccs'  = case mz of
                      Just z  -> if (x ∈ reachable isinkdom z) then
                                   Map.insert x (remsuccs ! x ∖ (Set.fromList $ [ x' | x' <- Set.toList $ succs x, x ∈ reachable isinkdom x'])) remsuccs
                                 else
                                   remsuccs
                      Nothing ->   Map.insert x (remsuccs ! x ∖ (Set.fromList $ [ x' | x' <- Set.toList $ succs x, x ∈ reachable isinkdom x'])) remsuccs
                -- remsuccs' = if closedCycle then Map.insert x (Set.delete x' (remsuccs ! x)) remsuccs else remsuccs
                -- closedCycle = (x ∈ (reachable isinkdom x'))
                first :: Set Node -> Set Node
                first s = if Set.null s then Set.empty else Set.fromList [Set.findMin s]
                changed = if (Map.member x isinkdom) then (zs /= (isinkdom ! x)) {- ∨ closedCycle  -} else True
                influenced = {- Set.filter (\pon -> not $ Set.null $ remsuccs' ! (pon2node ! pon)) -} worklist0
                lca  n m = lca' isinkdom (n, Set.fromList [n]) (m, Set.fromList [m])
                lca' c (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((c ! n) ∖ ns ) of
                                     []   -> case Set.toList $ ((c ! m) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> lca' c (m', Set.insert m' ms) (n, ns)
                                                _    -> error "more than one successor in isinkdom" 
                                     [n'] -> lca' c (m,ms) (n', Set.insert n' ns)
                                     _    -> error "more than one successor in isinkdom" 

                reachable :: Map Node (Set Node) -> Node -> [Node]
                reachable c x = reverse $ reach x []
                  where reach :: Node -> [Node] -> [Node]
                        reach x seen
                          | x `elem` seen = seen
                          | otherwise     = case Set.toList $ c ! x of
                            []   -> (x:seen)
                            [x'] -> reach x' (x:seen)
                            _    -> error $ "reach " ++ (show x) ++ " " ++ (show seen) ++ " " ++ (show $ c ! x)





isinkdomOfSinkContraction :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfSinkContraction graph = fmap (Set.delete endNode) $ 
                                  Map.fromList [ (x, idomClassic ! x)  | x <- nodes graph, not $ x ∈ sinkNodes ]
                                ⊔ Map.fromList [ (x, Set.fromList [y]) | (s:sink) <- sinks, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
                                ⊔ Map.fromList [ (x, Set.empty)        | x <- nodes graph]
    where [endNode] = newNodes 1 graph
          sinks = controlSinks graph
          idomClassic = fmap (\x -> Set.fromList [x]) $ Map.fromList $ iDom (grev $ sinkShrinkedGraph graph endNode) endNode
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]




type Successor = (Set Node, Maybe Node)

sinkdomOfJoinUpperBound :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOfJoinUpperBound  graph =
                      (fmap fromJust $ joinUpperBound graph)
                    ⊔ Map.fromList [ (x, Set.empty)           | x <- nodes graph]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1, not $ x ∈ sinkNodes]
                    ⊔ Map.fromList [ (x, Set.fromList [y])    | (s:sink) <- controlSinks graph, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
    where succs  x    = Set.delete x $ Set.fromList $ suc graph x
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- controlSinks graph, x <- sink]

joinUpperBound :: forall gr a b. DynGraph gr => gr a b -> Map Node (Maybe (Set Node))
joinUpperBound graph = Map.delete dummyNode $ jub condNodes init
    where jub :: Set Node -> Map Node (Maybe (Set Node)) -> Map Node (Maybe (Set Node))
          jub worklist jubs 
              | Set.null worklist = jubs
              | otherwise         = if (ubX == ubX') then
                                      jub               worklist'                     jubs
                                    else
                                      jub (influenced ⊔ worklist') (Map.insert x ubX' jubs)
            where (x, worklist')  = Set.deleteFindMin worklist
                  successorsX = successors ! x
                  ubX         = jubs ! x
                  ubX'        = case foldr1 join successorsX of
                    (ns, Nothing) -> Just ns
                    _             -> Nothing

                  influenced = Set.fromList $ prevConds x

                  join :: Successor -> Successor -> Successor
                  join (ns, Nothing) (ms, Nothing) = (         ns ⊓ ms        , Nothing)
                  join (ns, Just n)  (ms, Nothing) = case jubs ! n of
                    Just ns' -> ((ns ⊔ ns') ⊓  ms, Nothing)
                    Nothing  -> (              ms, Nothing)
                  join (ns, Nothing) (ms, Just m)  = case jubs ! m of
                    Just ms' -> (       ns  ⊓ (ms ⊔ ms'), Nothing)
                    Nothing  -> (       ns              , Nothing)
                  join (ns, Just n)  (ms, Just m)  = case jubs ! m of
                    Just ms' -> case jubs ! n of
                                 Just ns' -> ( (ns ⊔ ns') ⊓ (ms ⊔ ms'), Nothing)
                                 Nothing  -> (              (ms ⊔ ms'), Nothing)
                    Nothing  -> case jubs ! n of
                                 Just ns' -> ( (ns ⊔ ns')             , Nothing)
                                 Nothing  -> (        (ns ⊔ ms),        Just dummyNode)
          [dummyNode] = newNodes 1 graph
          init = Map.fromList $ [ (x, if not $ List.null deadends then
                                        Just $ (∏) [ ns | (ns, Nothing) <- deadends] 
                                      else
                                        Nothing
                                  )
                                | x <- Set.toList $ condNodes,
                                  not $ x ∈ sinkNodes,
                                  let successorsX  = successors ! x,
                                  let deadends =  [ s | s@(_,Nothing) <- successorsX ]
                                ]
                                ++
                                [ (x, Just $ Set.fromList $ the (x `elem`) sinks ) | x <- Set.toList $ condNodes,
                                                                                     x ∈ sinkNodes
                                ]
                                ++
                                [ (dummyNode, Nothing) ]
                                   
          successors :: Map Node [Successor] 
          successors = Map.fromList [ (x, [ (Set.fromList $ toNextCond x',
                                             nextCond x'
                                            ) | x' <- Set.toList $ succs x ] 
                                      ) | x <- Set.toList $ condNodes]

          
          succs  x    = Set.delete x $ Set.fromList $ suc graph x
          preds  x    = Set.delete x $ Set.fromList $ pre graph x
          condNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ succs x) > 1 ]
          joinNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ preds x) > 1 ]
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]
          sinks       =  controlSinks graph
          nextCond    = nextRealCondNode graph
          prevConds   = prevRealCondNodes graph
          toNextCond  = toNextRealCondNode graph

isinkdomOfTwoFinger6 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfTwoFinger6 graph = twoFinger worklist0 isinkdom0
  where isinkdom0   = Map.fromList [ (x, Set.empty )          | x <- nodes graph]
--                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1, not $ x ∈ sinkNodes]
                    ⊔ Map.fromList [ (x, Set.fromList [y])    | (s:sink) <- controlSinks graph, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
        worklist0   = Map.keysSet $ Map.filter (\x -> x ∈ condNodes   ∧  (not $ x ∈ sinkNodes)) pon2node
        succs  x    = Set.delete x $ Set.fromList $ suc graph x
        condNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ succs x) > 1 ]
        sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- controlSinks graph, x <- sink]
        nextCond    = nextRealCondNode graph
        (node2pon, pon2node) = postorder graph
        
        twoFinger :: Set Integer ->  Map Node (Set Node) -> Map Node (Set Node)
        twoFinger worklist isinkdom
            | Set.null worklist = traceShow ("x", "mz", "zs", Set.map (pon2node !) worklist, isinkdom) $
                                  let 
                                      f isinkdom = isinkdom0
                                                 ⊔ Map.fromList [ (x, Set.fromList [ z | z <- Set.toList $ isinkdom ! x,
                                                                                         (∀) (suc graph x) (\y -> z `elem` (suc isinkdomTrc y))
                                                                                   ]
                                                                   )
                                                                | x <- Set.toList $ condNodes ∖ sinkNodes ]
                                        where isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: gr () ())
                                  in   (𝝂) isinkdom f
            | otherwise         = traceShow (x, mz, zs, Set.map (pon2node !) worklist, isinkdom) $
                                  if (not $ changed) then twoFinger               worklist'                                   isinkdom
                                                     else twoFinger (influenced ⊔ worklist')  (Map.insert x zs                isinkdom)
          where (pon, worklist')  = Set.deleteFindMin worklist
                x = pon2node ! pon
                -- (x', others) = if (Set.null $ remsuccs ! x) then error $ "remsuccs ! " ++ (show x) else Set.deleteFindMin $ remsuccs ! x
                mz
                  | (∀) (succs x) (\x' -> nextCond x' == Just x) =  foldM1 lca (Set.toList $ succs x)
                  | otherwise                                     = foldM1 lca [ x' | x' <- Set.toList $  succs x, nextCond x' /= Just x]
                deadends = [ x' | x' <- Set.toList $ succs x, nextCond x' == Nothing]
                zs
--                 | length deadends == 1 = Set.fromList deadends
--                 | length deadends >  1 = Set.empty -- if mz == Just z, z necessarilu lies on toNextCond x' for all x' s.t. x -> x'
                 | otherwise        = case mz of
                      Just z  ->  -- (if (x == (-93) ) then traceShow ("ROFL", x,z, reachable isinkdom z) else id) $
                                  -- if (x ∈ reachable isinkdom z) then
                                  --   -- error "rofl"
                                  --   first     $ Map.fromList [ (n,x') | x' <- Set.toList $ succs x , Just n <- [nextCond x'], node2pon ! n < node2pon ! x ]
                                  -- else
                                    Set.fromList [ z ]
                      Nothing ->  if (length deadends == 1) then Set.fromList deadends else
                                  if (length deadends  > 1) then Set.empty             else
                                  if Map.null $ Map.fromList [ (n,x') | x' <- Set.toList $ succs x , Just n <- [nextCond x'], node2pon ! n < node2pon ! x ] then
                                    -- (if length deadends == (Set.size $ succs x) then id else traceShow (deadends, (x, node2pon ! x),  [ (n, node2pon ! n) | x' <- Set.toList $ succs x , Just n <- [nextCond x']]) ) $
                                    Set.empty
                                  else
                                    first     $ Map.fromList [ (n,x') | x' <- Set.toList $ succs x , Just n <- [nextCond x'], node2pon ! n < node2pon ! x  ]
                first :: Map Node Node -> Set Node
--                first s = if Set.null s then Set.empty else Set.fromList [Set.findMin s]
                -- first s = if Set.null s then Set.empty else Set.fromList [ (pon2node !)  $ Set.findMin $ Set.map (node2pon !) s ]
                first s = if Map.null s then Set.empty else Set.fromList [ s ! ((pon2node !)  $ Set.findMax $ Set.map (node2pon !) $ Map.keysSet s) ]
                changed = if (Map.member x isinkdom) then (zs /= (isinkdom ! x)) {- ∨ closedCycle  -} else True
                influenced = {- Set.filter (\pon -> not $ Set.null $ remsuccs' ! (pon2node ! pon)) -} worklist0
                lca  n m = lca' isinkdom (n,n, Set.fromList [n]) (m,m, Set.fromList [m])
                lca' c (n0,n,ns) (m0,m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((c ! n) ∖ ns ) of
                                     []   -> case Set.toList $ ((c ! m) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> {- if (m' == x) then Just n0 else -} lca' c (m0, m', Set.insert m' ms) (n0, n, ns)
                                                _    -> error "more than one successor in isinkdom" 
                                     [n'] -> {- if (n' == x) then Just m0 else -} lca' c (m0, m, ms) (n0, n', Set.insert n' ns)
                                     _    -> error "more than one successor in isinkdom" 

                reachable :: Map Node (Set Node) -> Node -> [Node]
                reachable c x = reverse $ reach x []
                  where reach :: Node -> [Node] -> [Node]
                        reach x seen
                          | x `elem` seen = seen
                          | otherwise     = case Set.toList $ c ! x of
                            []   -> (x:seen)
                            [x'] -> reach x' (x:seen)
                            _    -> error $ "reach " ++ (show x) ++ " " ++ (show seen) ++ " " ++ (show $ c ! x)




sinkDF graph =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈ sinkdom ! p,
                                            (not $ x ∈ sinkdom ! y)  ∨  x == y ])
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph


sinkDFGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFGraphP = cdepGraphP sinkDFGraph

sinkDFGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFGraph = cdepGraph sinkDFcd

sinkDFcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFcd = xDFcd sinkDF


sinkDFLocalDef graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            (not $ x ∈ sinkdom ! y)  ∨  x == y ])
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph




sinkDFLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFLocal graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            x == y ∨
                                            (∀) (suc isinkdom y) (\z -> 
                                              (∀) (isinkdomSccOf z) (/= x)
                                            )  
                                      ]
                     )
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()
        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m `elem`) $ isinkdomSccs



sinkDFUpDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUpDef graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                            (∀) (suc isinkdom z) (\x -> (not $ x ∈ sinkdom ! y)  ∨  x == y)
                                      ]
                     )
                   | z <- nodes graph, (x:_) <- [suc isinkdom z]]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

sinkDFUpGivenX :: forall gr a b. DynGraph gr => gr a b -> Map (Node,Node) (Set Node)
sinkDFUpGivenX graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                (∀) (suc isinkdom y) (/= x)
                                      ]
                     )
                   | z <- nodes graph, x <- suc isinkdom z]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()


sinkDFUp :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUp graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                (∀) (suc isinkdom y) (/= x)
                                      ]
                     )
                   | z <- nodes graph, (x:_) <- [suc isinkdom z]]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()



sinkDFFromUpLocalDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocalDef graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- pre isinkdom x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocalDef graph
        dfup = sinkDFUpDef graph
        sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()



mdomOfimdomProperty :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mdomOfimdomProperty graph =
          Map.fromList [ (y,
                 Set.fromList [ y ]
               ⊔ (∐) [ mdom ! z | z <- suc imdom y]
            )
          | y <- nodes graph]
  where mdom = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m `elem`) $ imdomSccs



sinkDFFromUpLocalDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFFromUpLocalDefGraphP = cdepGraphP sinkDFFromUpLocalDefGraph

sinkDFFromUpLocalDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFFromUpLocalDefGraph = cdepGraph sinkDFFromUpLocalDefcd

sinkDFFromUpLocalDefcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFFromUpLocalDefcd = xDFcd sinkDFFromUpLocalDef



sinkDFFromUpLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocal graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z | z <- pre isinkdom x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocal graph
        dfup = sinkDFUp graph
        sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()


sinkDFFromUpLocalGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFFromUpLocalGraphP = cdepGraphP sinkDFFromUpLocalGraph

sinkDFFromUpLocalGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFFromUpLocalGraph = cdepGraph sinkDFFromUpLocalcd

sinkDFFromUpLocalcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFFromUpLocalcd = xDFcd sinkDFFromUpLocal


sinkDFF2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFF2 graph =
      (㎲⊒) (Map.fromList [(x, Set.empty) | x <- nodes graph]) f2
  where f2 df = df ⊔ 
           Map.fromList [ (x, (∐) [ Set.fromList [ y ] | y <- pre graph x,
                                                         (∀) (suc isinkdom y) (\z -> 
                                                           (∀) (isinkdomSccOf z) (/= x)
                                                         )
                                   ]
                          )
                        | x <- nodes graph]
         ⊔ Map.fromList [ (x, (∐) [ Set.fromList [ y ] | z <- pre isinkdom x,
                                                          y <- Set.toList $ df ! z,
                                                         (∀) (suc isinkdom y) (/= x) ])
                        | x <- nodes graph]
        sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()
        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m `elem`) $ isinkdomSccs


sinkDFF2GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFF2GraphP = cdepGraphP sinkDFF2Graph

sinkDFF2Graph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFF2Graph = cdepGraph sinkDFF2cd

sinkDFF2cd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFF2cd = xDFcd sinkDFF2

xDFcd :: DynGraph gr => (gr a b -> Map Node (Set Node)) -> gr a b ->  Map Node (Set Node)
xDFcd xDF graph                  = Map.fromList [ (n, Set.empty)       | n <- nodes graph]
                                 ⊔ Map.fromList [ (n, Set.delete n ns) | (n,ns) <- Map.assocs $
                                                                            (fmap Set.fromList $ invert' $ fmap Set.toList df )
                                                ]
  
  where df = xDF graph



immediateOf :: DynGraph gr => Map Node (Set Node) -> gr () ()
immediateOf succs = trr $ fromSuccMap $ succs

isinkdomOf    graph = immediateOf $ sinkdomOf    graph
isinkdomOfGfp graph = immediateOf $ sinkdomOfGfp graph

imdomOf    graph = immediateOf $ mdomOf    graph
imdomOfLfp graph = immediateOf $ mdomOfLfp graph






mDF graph =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈ mdom ! p,
                                            (not $ x ∈ mdom ! y)  ∨  x == y ])
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph


mDFGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFGraphP = cdepGraphP sinkDFGraph

mDFGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFGraph = cdepGraph mDFcd

mDFcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFcd = xDFcd mDF


mDFLocalDef graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            (not $ x ∈ mdom ! y)  ∨  x == y ])
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph




mDFLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFLocal graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            x == y ∨
                                            (∀) (suc imdom y) (\z -> 
                                              (∀) (imdomSccOf z) (/= x)
                                            )  
                                      ]
                     )
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m `elem`) $ imdomSccs



mDFUpDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUpDef graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                            (∀) (suc imdom z) (\c -> 
                                              (∀) (imdomSccOf c) (\x -> (not $ x ∈ mdom ! y)  ∨  x == y)
                                            )
                                      ]
                     )
                   | z <- nodes graph, (x:_) <- [suc imdom z]]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m `elem`) $ imdomSccs

mDFUpGivenX :: forall gr a b. DynGraph gr => gr a b -> Map (Node,Node) (Set Node)
mDFUpGivenX graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                (∀) (suc imdom y) (\c ->
                                                  (∀) (imdomSccOf c) (/= x)
                                                )
                                      ]
                     )
                   | z <- nodes graph, x <- suc imdom z]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m `elem`) $ imdomSccs


mDFUp :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUp graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                (∀) (suc imdom y) (\c ->
                                                  (∀) (imdomSccOf c) (/= x)
                                                )
                                      ]
                     )
                   | z <- nodes graph, (x:_) <- [suc imdom z]]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m `elem`) $ imdomSccs


mDFFromUpLocalDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocalDef graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- pre imdom x  ] ) | x <- nodes graph]
  where dflocal = mDFLocalDef graph
        dfup = mDFUpDef graph
        mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()



mDFFromUpLocalDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFFromUpLocalDefGraphP = cdepGraphP mDFFromUpLocalDefGraph

mDFFromUpLocalDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFFromUpLocalDefGraph = cdepGraph mDFFromUpLocalDefcd

mDFFromUpLocalDefcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFFromUpLocalDefcd = xDFcd mDFFromUpLocalDef




mDFFromUpLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocal graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z | z <- pre imdom x  ] ) | x <- nodes graph]
  where dflocal = mDFLocal graph
        dfup = mDFUp graph
        mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()


mDFFromUpLocalGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFFromUpLocalGraphP = cdepGraphP mDFFromUpLocalGraph

mDFFromUpLocalGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFFromUpLocalGraph = cdepGraph mDFFromUpLocalcd

mDFFromUpLocalcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFFromUpLocalcd = xDFcd mDFFromUpLocal



mDFF2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFF2 graph =
      (㎲⊒) (Map.fromList [(x, Set.empty) | x <- nodes graph]) f2
  where f2 df = df ⊔ 
           Map.fromList [ (x, (∐) [ Set.fromList [ y ] | y <- pre graph x,
                                                         (∀) (suc imdom y) (\c -> 
                                                           (∀) (imdomSccOf c) (/= x)
                                                         )
                                   ]
                          )
                        | x <- nodes graph]
         ⊔ Map.fromList [ (x, (∐) [ Set.fromList [ y ] | z <- pre imdom x,
                                                          y <- Set.toList $ df ! z,
                                                         (∀) (suc imdom y) (\c ->
                                                           (∀) (imdomSccOf c) (/= x)
                                                         )
                                   ])
                        | x <- nodes graph]
        mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m `elem`) $ imdomSccs


mDFF2GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFF2GraphP = cdepGraphP mDFF2Graph

mDFF2Graph :: DynGraph gr => gr a b ->  gr a Dependence
mDFF2Graph = cdepGraph mDFF2cd

mDFF2cd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFF2cd = xDFcd mDFF2



imdomOfTwoFinger6 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
imdomOfTwoFinger6 graph = twoFinger worklist0 imdom0
  where imdom0   = Map.fromList [ (x, Set.empty )          | x <- nodes graph]
                 ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1]
        worklist0   = Map.keysSet $ Map.filter (\x -> x ∈ condNodes) pon2node
        succs  x    = Set.fromList $ suc graph x
        condNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ succs x) > 1 ]
        (node2pon, pon2node) = postorder graph
        
        twoFinger :: Set Integer ->  Map Node (Set Node) -> Map Node (Set Node)
        twoFinger worklist imdom
            | Set.null worklist = -- traceShow ("x", "mz", "zs", Set.map (pon2node !) worklist, imdom) $
                                  imdom
            | otherwise         = -- traceShow (x, mz, zs, Set.map (pon2node !) worklist, imdom) $
                                  if (not $ changed) then twoFinger               worklist'                                   imdom
                                                     else twoFinger (influenced ⊔ worklist')  (Map.insert x zs                imdom)
          where (pon, worklist')  = Set.deleteFindMin worklist
                x = pon2node ! pon
                mz = foldM1 lca (Set.toList $ succs x)
                zs = case mz of
                      Just z  ->  Set.fromList [ z ]
                      Nothing ->  Set.fromList [ ]
                changed = zs /= (imdom ! x)
                influenced =  worklist0
                lca  n m = lca' imdom (n, Set.fromList [n]) (m, Set.fromList [m])
                lca' c (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((c ! n) ∖ ns ) of
                                     []   -> case Set.toList $ ((c ! m) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> lca' c ( m', Set.insert m' ms) (n, ns)
                                                _    -> error "more than one successor in imdom" 
                                     [n'] -> lca' c (m, ms) (n', Set.insert n' ns)
                                     _    -> error "more than one successor in imdom" 



idomToDF :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)  -> Map Node (Set Node)
idomToDF graph idom = 
      (㎲⊒) (Map.fromList [(x, Set.empty) | x <- nodes graph]) f2
  where f2 df = df ⊔ 
           Map.fromList [ (x, (∐) [ Set.fromList [ y ] | y <- pre graph x,
                                                         (∀) (suc idomG y) (\c -> 
                                                           (∀) (idomSccOf c) (/= x)
                                                         )
                                   ]
                          )
                        | x <- nodes graph]
         ⊔ Map.fromList [ (x, (∐) [ Set.fromList [ y ] | z <- pre idomG x,
                                                          y <- Set.toList $ df ! z,
                                                         (∀) (suc idomG y) (\c ->
                                                           (∀) (idomSccOf c) (/= x)
                                                         )
                                   ])
                        | x <- nodes graph]
        idomG = fromSuccMap idom :: gr () ()
        idomSccs = scc idomG
        idomSccOf m = the (m `elem`) $ idomSccs

        
mDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFTwoFinger graph = idomToDF graph $ imdomOfTwoFinger6 graph

imdomTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
imdomTwoFingerGraphP = cdepGraphP imdomTwoFingerGraph

imdomTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
imdomTwoFingerGraph = cdepGraph imdomTwoFingercd

imdomTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
imdomTwoFingercd = xDFcd mDFTwoFinger



{- Utility functions -}
toNextCondNode graph n = toNextCondSeen [n] n
    where toNextCondSeen seen n = case suc graph n of
            []    -> seen
            [ n'] -> if n' `elem` seen then seen else toNextCondSeen (n':seen) n'
            (_:_) -> seen

nextCondNode graph n = nextCondSeen [n] n
    where nextCondSeen seen n = case suc graph n of
            []    -> Nothing
            [ n'] -> if n' `elem` seen then Nothing else nextCondSeen (n':seen) n'
            (_:_) -> Just n



toNextRealCondNode graph n = toNextCondSeen [n] n
    where toNextCondSeen seen n = case List.delete n $ nub $ suc graph n of
            []    -> seen
            [ n'] -> if n' `elem` seen then seen else toNextCondSeen (n':seen) n'
            (_:_) -> seen

nextRealCondNode graph n = nextCondSeen [n] n
    where nextCondSeen seen n = case List.delete n $ nub $ suc graph n of
            []    -> Nothing
            [ n'] -> if n' `elem` seen then Nothing else nextCondSeen (n':seen) n'
            (_:_) -> Just n



nextJoinNode graph n = nextJoinSeen [n] n
    where nextJoinSeen seen n = case pre graph n of
            (_:_) -> Just n
            _     -> case suc graph n of
              []     -> Nothing
              [ n' ] -> if n' `elem` seen then Nothing else nextJoinSeen (n':seen) n'
              (_:_)  -> Nothing

nextJoinNodes graph n = nextJoinSeen [n] n []
    where nextJoinSeen seen n joins = case suc graph n of
              []     -> joins'
              [ n' ] -> if n' `elem` seen then joins' else nextJoinSeen (n':seen) n' joins'
              (_:_)  -> joins'
            where joins' = case pre graph n of
                     (_:_) -> n:joins
                     _     -> joins



prevRealCondNodes graph start = prevCondsF (List.delete start $ nub $ pre graph start)
    where prevCondsF front = concat $ fmap prevConds front
          prevConds  n
            | n == start = [n]
            | otherwise  = case List.delete n $ nub $ suc graph n of
                [ n'] -> prevCondsF (List.delete n $ nub $ pre graph n)
                (_:_) -> [n]



prevCondNodes graph start = prevCondsF (pre graph start)
    where prevCondsF front = concat $ fmap prevConds front
          prevConds  n
            | n == start = [n]
            | otherwise  = case suc graph n of
                [ n'] -> prevCondsF (pre graph n)
                (_:_) -> [n]

prevCondsWithSuccNode graph start = prevCondsF [(p, start) | p <- pre graph start]
    where prevCondsF front = concat $ fmap prevConds front
          prevConds  (n,x)
            | n == start = [(n,x)]
            | otherwise  = case suc graph n of
                [ n'] -> prevCondsF [ (p,n) | p <- pre graph n]
                (_:_) -> [(n,x)]



prevRepresentantNodes graph start =
      case suc graph start of
        (_:_:_) -> case pre graph start of
                     [n] -> prevRepresentant n start
                     _   -> start
        _       -> prevRepresentant start start
    where prevRepresentant n m =
            case suc graph n of
                [_] -> case pre graph n of
                  [n'] -> prevRepresentant n' n
                  _    -> n
                _   -> m

data SinkPath = SinkPath { prefix :: [[Node]], controlSink :: [Node] } deriving Show

data MaximalPath          = MaximalPath { mPrefix :: [[Node]],  mScc :: [Node], mEndNodes  :: [Node] } deriving Show
data MaximalPathCondensed = MaximalPathCondensed {
  mcPrefix :: [Node],   -- of Nodes in the condensed graph
  mcScc ::  Node,       --    Node  in the condensed graph
  mcEndNodes :: [Node]  -- of Nodes in the original graph
 }

controlSinks :: Graph gr => gr a b -> [[Node]]
controlSinks graph =
      [ scc | scc <- sccs, (∀) scc (\n ->
                            (∀) (suc graph n) (\n' -> n' `elem` scc)
                           )
                   ]
    where sccs = scc graph

sinkPathsFor :: DynGraph gr => gr a b -> Map Node [SinkPath]
sinkPathsFor graph = Map.fromList [ (n, sinkPaths n) | n <- nodes graph ]
    where
      sccs = scc graph
      sccOf m =  the (m `elem`) $ sccs
      sinks = controlSinks graph     -- TODO: dont repeat scc computation
      condensed = condensation graph --       or here
--      trcCondensed = trc condensed
      sinkPaths n = [ SinkPath { prefix = fmap (fromJust . (lab condensed)) revPath, controlSink = sink } | sink <- sinks , revPath <- revPaths (nodeMap ! (sccOf n)) ( nodeMap ! sink) ]
      revPaths :: Node -> Node -> [[Node]]
      revPaths ns sink
       | ns == sink    = [[]]
       | otherwise     = fmap (ns:) [ path | ns' <- suc condensed ns, path <- revPaths ns' sink ]
      nodeMap = Map.fromList [ (ns, n) | (n, ns) <- labNodes condensed ]




maximalPathsFor :: DynGraph gr => gr a b -> Map Node [MaximalPath]
maximalPathsFor graph = maximalPathsForNodes graph [ n | p <- condNodes, n <- suc graph p ]
    where
      condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]

maximalPathsForNodes :: DynGraph gr => gr a b -> [Node] -> Map Node [MaximalPath]
maximalPathsForNodes graph relevantNodes = Map.fromList [ (n, maximalPaths n) | n <- relevantNodes]
    where
      sccs = scc graph
      sccOf m =  the (m `elem`) $ sccs
      condensed = condensation graph --       or here
      maximalPaths n = [ MaximalPath { mPrefix   = reverse $  fmap (fromJust . (lab condensed)) $ mcPrefix revPath,
                                       mScc      =                 (fromJust . (lab condensed)) (mcScc revPath),
                                       mEndNodes = reverse $ mcEndNodes revPath
                                     }
                       |  revPath <- revPaths [(nodeMap ! (sccOf n))] ]
      revPaths :: [Node] -> [MaximalPathCondensed]
      revPaths (ns:rest)
         | suc condensed ns == []   =    pathsToCycleInNs
                                      ++ pathsToSinkInNs
         | (length nsNodes ) > 1    =    pathsToCycleInNs
                                      ++ pathsToSinkInNs
                                      ++ pathsToSuccessors
         | let [n] = nsNodes in
           n `elem` suc graph n     =    [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = nsNodes } ] -- ==  pathsToCycleInNs
                                      ++ pathsToSuccessors
         | otherwise                =    pathsToSuccessors
       where
         pathsToCycleInNs  = [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = cycle } | cycle <- cyclesInScc nsNodes graph ]
         pathsToSinkInNs   = [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = sink  } | sink  <- [ [n] | n <- nsNodes, length (suc graph n) == 0] ]
         pathsToSuccessors = [ path | ns' <- suc condensed ns, path <- revPaths (ns':ns:rest)]
         nsNodes = fromJust $ lab condensed ns
      nodeMap = Map.fromList [ (ns, n) | (n, ns) <- labNodes condensed ]


-- Speed this up, using http://dx.doi.org/10.1137/0205007 or http://dx.doi.org/10.1137/0205007 ?!?! See http://stackoverflow.com/questions/546655/finding-all-cycles-in-graph
cyclesInScc scc@(n:_) graph = cyclesFromIn scc graph n
cyclesFrom graph n = cyclesFromIn (nodes graph) graph n
cyclesFromIn nodes graph n = cyclesFromPath [n]
    where
      cyclesFromPath path@(n:_) =      [ n':(takeWhile (/=n') path) | n' <- suc graph n, n' `elem` nodes,       n' `elem` path]
                                   ++  [ cycle                      | n' <- suc graph n, n' `elem` nodes, not $ n' `elem` path, cycle <- cyclesFromPath (n':path) ]



-- Examples
      
-- shows necessity of change in the "linear path section" rule
exampleLinear :: Graph gr => gr () ()
exampleLinear = mkGraph [(-27,()),(-23,()),(-10,()),(4,()),(21,()),(25,()),(26,())] [(-27,21,()),(-23,-10,()),(-23,25,()),(21,-27,()),(25,-27,()),(25,-27,()),(25,4,()),(25,21,()),(26,-27,()),(26,-23,()),(26,-10,()),(26,4,()),(26,21,()),(26,25,())]

exampleLinearSimple :: Graph gr => gr () ()
exampleLinearSimple =
    mkGraph [(n,()) | n <- [1..5]]
            [(1,2,()), (1,4,()),
             (4,5,()), (4,3,()),
             (2,3,()), (3,2,())
            ]

exampleLinearSimpleLong :: Graph gr => gr () ()
exampleLinearSimpleLong =
    mkGraph [(n,()) | n <- [1..7]]
            [(1,2,()), (1,4,()),
             (4,5,()), (4,3,()),
             (2,3,()), (3,6,()), (6,7,()), (7,2,())
            ]
