{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.NTICD where

import Data.Maybe(fromJust)
import Control.Monad (liftM)
import Data.List(foldl', intersect,foldr1)

import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

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
import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort)

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
        expandSymbolic s = Map.fromList [ ((m,p), s ! (r, p)) | p <- condNodes, m <- nodes graph, Just r <- [representantOf m]]
                         ⊔ Map.fromList [ ((m,p), Set.empty)  | p <- condNodes, m <- nodes graph, Nothing == representantOf m]

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
        expandSymbolic s = Map.fromList [ ((m,p), s ! (r, p)) | p <- condNodes, m <- nodes graph, Just r <- [representantOf m]]
                         ⊔ Map.fromList [ ((m,p), Set.empty)  | p <- condNodes, m <- nodes graph, Nothing == representantOf m]



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




{- The definition of ntacd -}
ntacdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntacdDefGraphP = cdepGraphP ntacdDefGraph

ntacdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntacdDefGraph  = cdepGraph ntacdDef

ntacdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntacdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inSinkPathAfter` (ni,nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inSinkPathAfter` (ni,nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where 
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inSinkPathAfter = inSinkPathAfterFor graph


{- The definition of ntbcd -}
ntbcdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntbcdDefGraphP = cdepGraphP ntbcdDefGraph

ntbcdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntbcdDefGraph  = cdepGraph ntbcdDef

ntbcdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntbcdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inSinkPathAfter'` (ni,nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inSinkPathAfter'` (ni,nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where 
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inSinkPathAfter' = inSinkPathAfterFor' graph


inSinkPathAfterFor :: DynGraph gr => gr a b -> Node -> (Node, Node, SinkPath) -> Bool
inSinkPathAfterFor graph' n (cond, s, path) = inSinkPathFromEntries [s] path
  where 
    inSinkPathFromEntries _       (SinkPath []           controlSink) = n `elem` controlSink ∧ (
                          (  (not $ cond `elem` controlSink) -- ∧
                             -- ((∀) (cyclesInScc  controlSink graph') (\cycle -> n ∈ cycle))
                          )
                        ∨ (  (cond `elem` controlSink) ∧
                             (s == cond ∨ n `elem` (suc withoutCondTrc s))
                          )
                      )
      where withoutCondTrc = trc $ delNode cond graph'
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n `elem` scc = -- traceShow (s, n, cond, entries, scc, controlSink) $ 
                         (True) ∧ (
--                         (not (cond ∈ scc) ∨ (n `elem` (suc (trc $ delNode cond graph') s)  )  ∨ (s == cond) ) ∧ (
                           (∀) entries (\entry -> let doms = (dom graph' entry) in
                            (∀) exits (\exit -> let domsexit = doms `get` exit in
                                   (entry /= exit || n == entry) && n `elem` domsexit)
                           )
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' `elem` next ]
            exits = [ n | (n,_) <- borderEdges ]
            get assocs key = fromJust $ List.lookup key assocs



inSinkPathAfterFor' :: DynGraph gr => gr a b -> Node -> (Node, Node, SinkPath) -> Bool
inSinkPathAfterFor' graph' n (cond, s, path) = inSinkPathFromEntries [s] path
  where
    get assocs key = fromJust $ List.lookup key assocs
    inSinkPathFromEntries entries (SinkPath []           controlSink) = n `elem` controlSink ∧ (
                          (  (not $ cond `elem` controlSink) ∧ (
                              ((∀) entries (\entry -> let doms = dom graph' entry in
                                (∀) cycles  (\cycle -> let c = head cycle in
                                  (n ∈ cycle) ∨ (n `elem` (doms `get` c))
                                )
                               )
                              )
                             )
                          )
                        ∨ (  (cond `elem` controlSink) ∧ (∀) entries (\entry -> 
                             (entry == cond ∨ n `elem` (suc withoutCondTrc entry))
                          ))
                      )
      where withoutCondTrc = trc $ delNode cond graph'
            cycles = (cyclesInScc  controlSink graph')
--     inSinkPathFromEntries entries (SinkPath []           controlSink) =
--                              (∀) entries (\entry -> 
--                                (∀) (nrPaths (initial entry) entry ) (\path ->  (n ∈ path))
--                              )
-- -- (Set.fromList path == Set.fromList controlSink) →
--       where cycles = (cyclesInScc  controlSink graph')
--             initial entry = Map.fromList [ (m, Set.empty) | m <- controlSink ]
--                           ⊔ Map.fromList [ (x, Set.fromList [(x,entry)]) | x <- controlSink, x ∈ pre graph' entry ]
--             nrPaths :: Map Node (Set (Node,Node)) -> Node -> [[Node]]
--             nrPaths taken n
--              | Set.null allowedEdges      = [[n]]
--              | otherwise                  = -- traceShow taken $
--                                             [ n:p | m <- Set.toList $ Set.map snd $ allowedEdges,
--                                                     p <- nrPaths (Map.adjust (\taken -> Set.insert (n,m) taken ) n taken) m  ]
--                where allowedEdges = (Set.fromList $ [(n,m) | m <- suc graph' n]) ∖ (taken ! n)

            
    -- inSinkPathFromEntries entries (SinkPath []           controlSink) =
    --                          (∀) entries (\entry -> (entry == cond) ∨
    --                            n ∈ (suc (trc $ delEdges ([(cond, x) | x <- suc graph' cond]) graph') entry)
    --                          )
    --   where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries entries  (SinkPath []           controlSink) = n `elem` controlSink ∧ (
    --                          ((∀) entries (\entry -> let doms = dom graph' entry in
    --                            (∀) cycles  (\cycle -> let c = head cycle in
    --                              (s ∈ cycle) ∨ (n ∈ cycle) ∨ (n `elem` (doms `get` c))
    --                            )
    --                           )
    --                          )
    --                         )
    --   where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries entries  (SinkPath []           controlSink) = n `elem` controlSink ∧ (
    --                          ((∀) entries (\entry -> let doms = dom graph' entry in
    --                            (∀) cycles  (\cycle -> let c = head cycle in
    --                               (s == cond) ∨ ((cond ∈ cycle) → (n ∈ cycle) ∨ (n `elem` (doms `get` c)))
    --                            )
    --                           )
    --                          )
    --                         )
    --  where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries _       (SinkPath []           controlSink) = n `elem` controlSink ∧ (
    --                          ((∀) (cyclesInScc  controlSink graph') (\cycle -> (s ∈ cycle) ∨ (n ∈ cycle)))
    --                       )
    -- inSinkPathFromEntries entries       (SinkPath []           controlSink) = n `elem` controlSink ∧ (
    --                          ((∀) (cyclesInScc  controlSink graph') (\cycle ->
    --                            ((∃) entries (∈ cycle)) → (s ∈ cycle) ∨ (n ∈ cycle)))
    --                       )
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n `elem` scc = -- traceShow (s, n, cond, entries, scc, controlSink) $ 
                         (True) ∧ (
--                         (not (cond ∈ scc) ∨ (n `elem` (suc (trc $ delNode cond graph') s)  )  ∨ (s == cond) ) ∧ (
                           (∀) entries (\entry -> let doms = (dom graph' entry) in
                            (∀) exits (\exit -> let domsexit = doms `get` exit in
                                   (entry /= exit || n == entry) && n `elem` domsexit)
                           )
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' `elem` next ]
            exits = [ n | (n,_) <- borderEdges ]




{- The definition of ntnrcd -}
ntnrcdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntnrcdDefGraphP = cdepGraphP ntnrcdDefGraph

ntnrcdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntnrcdDefGraph  = cdepGraph ntnrcdDef

ntnrcdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntnrcdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph, nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (nrPaths ! (ni,nk)) (\path ->       nj `inPath` path),
                                                (∃) (nrPaths ! (ni,nl)) (\path -> not $ nj `inPath` path)
                                         ]
                       )
                     | ni <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        nrPaths = nrPathsFor graph
        inPath n (NrPath { path }) = n ∈ path

data NrPath = NrPath { path :: [Node] } deriving Show

nrPathsFor :: DynGraph gr => gr a b -> Map (Node,Node) [NrPath]
nrPathsFor graph = Map.fromList [ ((n,m), fmap (\p -> NrPath { path = p }) $ nrPathsFor (n,m)) | n <- nodes graph, m <- suc graph n ]
    where
      nrPathsFor :: (Node,Node) -> [[Node]]
      nrPathsFor (n,m) = nrPaths (forbidden (n,m)) (initial (n,m)) m
      initial (n,m)   = Map.fromList [(n, Set.empty) | n <- nodes graph]
--                  ⊔ Map.fromList [(n, Set.fromList $ [ (n,m) ]) ]
      forbidden (n,m) = Set.fromList $ [ (n,m) ] 
--      forbidden (n,m) = Map.fromList [(x, Set.fromList $ [ (x,n) ]) |  x <- pre graph n ]
--      nrPathsF taken ns = concat $ fmap (nrPaths taken) ns
      nrPaths :: Set (Node, Node) -> Map Node (Set (Node,Node)) -> Node -> [[Node]]
      nrPaths forbidden taken n
--       | Set.null allowedEdges  ∧  (not $ Set.null $ (Set.fromList  [(n,m) | m <- suc graph n]) ⊓ forbidden)  = []
       | Set.null allowedEdges  ∧  (not $ Set.null $ (Set.fromList  [(n,m) | m <- suc graph n]) ⊓ (forbidden ∖ (taken ! n)))  = []
       | Set.null allowedEdges                                                                                                = [[n]]
       | otherwise                  = -- traceShow taken $
                                      [ n:p | m <- Set.toList $ Set.map snd $ allowedEdges,
                                              p <- nrPaths forbidden (Map.adjust (\taken -> Set.insert (n,m) taken ) n taken) m  ]
        where allowedEdges = (Set.fromList $ [(n,m) | m <- suc graph n]) ∖ (taken ! n)




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
                                            assert (
                                            (∀) (suc isinkdom z)                                (\x -> (not $ x ∈ sinkdom ! y)  ∨  x == y)
                                            ↔
                                            (∀) (suc isinkdom z) (\c ->  (∀) (isinkdomSccOf c)  (\x -> (not $ x ∈ sinkdom ! y)  ∨  x == y))
                                            ) True,
                                            (∀) (suc isinkdom z) (\x -> (not $ x ∈ sinkdom ! y)  ∨  x == y)
                                      ]
                     )
                   | z <- nodes graph, (x:_) <- [suc isinkdom z]]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m `elem`) $ isinkdomSccs

sinkDFUpGivenX :: forall gr a b. DynGraph gr => gr a b -> Map (Node,Node) (Set Node)
sinkDFUpGivenX graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                assert (
                                                (∀) (suc isinkdom y)                                (/=x)
                                                ↔
                                                (∀) (suc isinkdom y) (\c ->  (∀) (isinkdomSccOf c)  (/=x))
                                                ) True,
                                                (∀) (suc isinkdom y) (/= x)
                                      ]
                     )
                   | z <- nodes graph, x <- suc isinkdom z]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m `elem`) $ isinkdomSccs


sinkDFUp :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUp graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                assert (
                                                (∀) (suc isinkdom y)                                (/=x)
                                                ↔
                                                (∀) (suc isinkdom y) (\c ->  (∀) (isinkdomSccOf c)  (/=x))
                                                ) True,
                                                (∀) (suc isinkdom y) (/= x)
                                      ]
                     )
                   | z <- nodes graph, (x:_) <- [suc isinkdom z]]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m `elem`) $ isinkdomSccs




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
sinkDFF2 graph = idomToDF graph isinkdom
  where sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()


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
mDFF2 graph = idomToDF graph imdom
  where mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()

mDFF2GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFF2GraphP = cdepGraphP mDFF2Graph

mDFF2Graph :: DynGraph gr => gr a b ->  gr a Dependence
mDFF2Graph = cdepGraph mDFF2cd

mDFF2cd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFF2cd = xDFcd mDFF2



imdomOfTwoFinger6 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
imdomOfTwoFinger6 graph = twoFinger 0 worklist0 imdom0
  where imdom0   = Map.fromList [ (x, Set.empty )                 | x <- nodes graph]
                 ⊔ Map.fromList [ (x, Set.fromList $ suc graph x) | x <- nodes graph, length (suc graph x) == 1]
        worklist0   = condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (suc graph x) > 1 ]
        prevConds   = prevCondNodes graph

        solution = mdomOfLfp graph
        invariant worklist imdom = -- if (True) then True else
                                   -- (if (not inv) then (traceShow (worklist, imdom, imdomWorklist)) else id) $
                                   inv
          where inv =   (∀) (nodes graph) (\n -> (∀) (solution ! n) (\m ->
                                (m ∈ (suc imdomWorklistTrc  n))
                        ))
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case Set.toList ms of
                            []  -> True
                            [m] -> (m ∈ solution ! n) ∧ (∀) (solution ! n) (\m' -> m' == n  ∨  (m' ∈ solution ! m))
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          (Set.null ms  ∧  (∃) (solution ! n) (\m -> m /= n)) → (
                            n ∈ worklistLfp
                          )
                        )
                imdomTrc = trc $ (fromSuccMap imdom :: gr () ())
                worklistLfp = (㎲⊒) Set.empty f
                  where f wl = worklist
                             ⊔ Set.fromList [ p | p <- Set.toList condNodes,
                                                  w <- Set.toList wl,
                                                  n <- nodes graph,
                                                  (∃) (solution ! n) (\m -> m /= n),
                                                  w ∈ solution ! n,
                                                  (∀) (solution ! n) (\m -> m == n  ∨  (m ∈ solution ! w)),
                                                  p ∈ prevConds n
                                            ]
                imdomWorklist = imdom
                              ⊔ Map.fromList [ (w, Set.fromList [ m | m <- Set.toList $ solution ! w,
                                                                      (∀) (solution ! w) (\m' -> m' == w  ∨  (m' ∈ solution ! m))
                                                                ]
                                               )
                                             | w <- Set.toList $ worklistLfp ]
                imdomWorklistTrc = trc $ (fromSuccMap  imdomWorklist :: gr () ())

        twoFinger :: Integer -> Set Node ->  Map Node (Set Node) -> Map Node (Set Node)
        twoFinger i worklist imdom
            | Set.null worklist = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                  -- traceShow (Set.size worklist0, i) $ 
                                  assert (invariant worklist imdom) $
                                  imdom
            | otherwise         = -- traceShow (x, mz, zs, influenced, worklist, imdom) $
                                  assert (invariant worklist imdom) $
                                  if (not $ changed) then twoFinger (i+1)               worklist'                                   imdom
                                                     else twoFinger (i+1) (influenced ⊔ worklist')  (Map.insert x zs                imdom)
          where (x, worklist')  = Set.deleteFindMin worklist
                mz = foldM1 lca (suc graph x)
                zs = case mz of
                      Just z  -> if z/= x then
                                   Set.fromList [ z ]
                                 else
                                   Set.fromList [ ]
                      Nothing ->  Set.fromList [ ]
                changed = zs /= (imdom ! x)
                influenced = let imdomRev = invert' $ fmap Set.toList imdom
                                 preds = predsSeenFor imdomRev [x] [x]
                             in  -- traceShow (preds, imdomRev) $ 
                                 Set.fromList $ foldMap prevConds preds
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



imdomOfTwoFinger7 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
imdomOfTwoFinger7 graph = fmap toSet $ twoFinger 0 worklist0 imdom0
  where toSet Nothing  = Set.empty
        toSet (Just x) = Set.fromList [x]
        imdom0   =             Map.fromList [ (x, Just z   ) | x <- nodes graph, [z] <- [suc graph x]]
                   `Map.union` Map.fromList [ (x, Nothing  ) | x <- nodes graph]
        worklist0   = condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (suc graph x) > 1 ]
        prevConds   = prevCondNodes graph

        solution = mdomOfLfp graph
        invariant worklist imdom = -- if (True) then True else
                                   -- (if (not inv) then (traceShow (worklist, imdom, imdomWorklist)) else id) $
                                   inv
          where inv =   (∀) (nodes graph) (\n -> (∀) (solution ! n) (\m ->
                                (m ∈ (suc imdomWorklistTrc  n))
                        ))
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> (m ∈ solution ! n) ∧ (∀) (solution ! n) (\m' -> m' == n  ∨  (m' ∈ solution ! m))
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          (isNothing ms  ∧  (∃) (solution ! n) (\m -> m /= n)) → (
                            n ∈ worklistLfp
                          )
                        )
                imdomTrc = trc $ (fromSuccMap (fmap toSet imdom) :: gr () ())
                worklistLfp = (㎲⊒) Set.empty f
                  where f wl = worklist
                             ⊔ Set.fromList [ p | p <- Set.toList condNodes,
                                                  w <- Set.toList wl,
                                                  n <- nodes graph,
                                                  (∃) (solution ! n) (\m -> m /= n),
                                                  w ∈ solution ! n,
                                                  (∀) (solution ! n) (\m -> m == n  ∨  (m ∈ solution ! w)),
                                                  p ∈ prevConds n
                                            ]
                imdomWorklist = fmap toSet imdom
                              ⊔ Map.fromList [ (w, Set.fromList [ m | m <- Set.toList $ solution ! w,
                                                                      (∀) (solution ! w) (\m' -> m' == w  ∨  (m' ∈ solution ! m))
                                                                ]
                                               )
                                             | w <- Set.toList $ worklistLfp ]
                imdomWorklistTrc = trc $ (fromSuccMap  imdomWorklist :: gr () ())

        twoFinger :: Integer -> Set Node ->  Map Node (Maybe Node) -> Map Node (Maybe Node)
        twoFinger i worklist imdom
            |   Set.null worklist = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                    -- traceShow (Set.size worklist0, i) $ 
                                    assert (invariant worklist imdom) $
                                    imdom
            | otherwise           = -- traceShow (x, mz, zs, influenced, worklist, imdom) $
                                    assert (invariant worklist imdom) $
                                    if (not $ new) then twoFinger (i+1)               worklist'                                   imdom
                                    else                twoFinger (i+1) (influenced ⊔ worklist')  (Map.insert x zs                imdom)
          where (x, worklist')  = Set.deleteFindMin worklist
                mz = foldM1 lca (suc graph x)
                zs = case mz of
                      Just z  -> if z/= x then
                                   Just z
                                 else
                                   Nothing
                      Nothing ->  Nothing
                new     = assert (isNothing $ imdom ! x) $
                          (not $ isNothing zs)
                influenced = let imdomRev = invert' $ fmap maybeToList imdom
                                 preds = predsSeenFor imdomRev [x] [x]
                             in  -- traceShow (preds, imdomRev) $
                                 Set.fromList $ [ n | n <- foldMap prevConds preds, n /= x, isNothing $ imdom ! n]
                lca :: Node -> Node -> Maybe Node
                lca  n m = lca' imdom (n, Set.fromList [n]) (m, Set.fromList [m])
                lca' :: Map Node (Maybe Node) -> (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lca' c (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((toSet (c ! n)) ∖ ns ) of
                                     []   -> case Set.toList $ ((toSet (c ! m)) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> lca' c ( m', Set.insert m' ms) (n, ns)
                                     [n'] -> lca' c (m, ms) (n', Set.insert n' ns)



withPossibleIntermediateNodesFromiXdom :: forall gr a b x. (Ord x, DynGraph gr) => gr a b -> Map Node (Set (Node, x)) -> Map Node (Set (Node, (x, Set Node)))
withPossibleIntermediateNodesFromiXdom graph ixdom = Map.fromList [ (n, Set.fromList [(m,(x,pi))])  | (n, ms) <- Map.assocs ixdom, [(m,x)] <- [Set.toList $ ms], let pi = pis ! n ]
                                                   ⊔ Map.fromList [ (n, Set.fromList []          )  | (n, ms) <- Map.assocs ixdom, []      <- [Set.toList $ ms]                   ]
  where pis = possibleIntermediateNodesFromiXdom graph $  fmap (Set.map fst) $ ixdom
  
possibleIntermediateNodesFromiXdom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node)
possibleIntermediateNodesFromiXdom graph ixdom = (㎲⊒) init f
  where init     = Map.fromList [ (n, Set.empty)                       | n <- Map.keys ixdom ]
        f pis    = pis
                 ⊔ Map.fromList [ (p, Set.delete z $
                                      (∐) [ Set.fromList [ y ]  ⊔  pis ! y | x <- suc graph p,
                                                                              let path = revPathFromTo ixdom x z,
                                                                              y <- path
                                      ]
                                  )
                                | p <- condNodes,
                                  [z] <- [Set.toList $ ixdom ! p]
                   ]
        condNodes   = [ x | x <- nodes graph, length (suc graph x) > 1 ]

        revPathFromTo ixdom x z = revPathFromToA x []
          where revPathFromToA x ps 
                   | x == z    = ps
                   | otherwise = revPathFromToA next (x:ps)
                 where [next] = Set.toList $ ixdom ! x



-- TODO: limit this to starts of linear section
predsSeenFor :: Map Node [Node] -> [Node] -> [Node] -> [Node]
predsSeenFor imdomRev = predsSeenF where
      predsSeenF :: [Node] -> [Node] -> [Node]
      predsSeenF seen front = concat $ fmap (predsSeen seen) front
      predsSeen  :: [Node] -> Node -> [Node]
      predsSeen seen x = case Map.lookup x imdomRev of 
        Nothing  -> seen
        Just ys  -> let new = (filter (not . (∈ seen)) ys) in predsSeenF (new ++ seen) new



idomToDF :: forall gr a b. DynGraph gr => gr a b -> gr () () -> Map Node (Set Node)
idomToDF graph idomG = 
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
        idomSccs = scc idomG

        idomSccOfMap = Map.fromList [ (c, cycle) | cycle <- idomSccs, not $ isSingleton cycle, c <- cycle ]
        idomSccOf m = case Map.lookup m idomSccOfMap of
          Nothing -> [m]
          Just cycle -> cycle

        isSingleton [x] = True
        isSingleton _   = False

idomToDFFast :: forall gr a b. DynGraph gr => gr a b -> gr () () -> Map Node (Set Node)
idomToDFFast graph idomG = foldl f2 (Map.fromList [(x, Set.empty) | x <- nodes graph]) sorting
  where f2 df x = cycleCompletion $ Map.insert x (local ⊔  up) df
          where local =       (∐) [ Set.fromList [ y ] | y <- pre graph x,
                                                         (∀) (suc idomG y) (\c -> 
                                                           (∀) (idomSccOf c) (/= x)
                                                         )
                                   ]
                up    =       (∐) [ Set.fromList [ y ] | z <- pre idomG x,
                                                          y <- Set.toList $ df ! z,
                                                         (∀) (suc idomG y) (\c ->
                                                           (∀) (idomSccOf c) (/= x)
                                                         )
                                   ]
        cycleCompletion df = foldr update df [ (c, allYs) | cycle <- Map.elems idomSccOfMap, let allYs = (∐) [ df ! c | c <- cycle ], c <- cycle ]
          where update (c, allYs) df = Map.insert c allYs df 

        sorting = topsort idomG
        idomSccs = scc idomG -- TODO: use the fact that SCC algorithms implicitly yield a  topsort

        idomSccOfMap = Map.fromList [ (c, cycle) | cycle <- idomSccs, not $ isSingleton cycle, c <- cycle ]
        idomSccOf m = case Map.lookup m idomSccOfMap of
          Nothing -> [m]
          Just cycle -> cycle

        isSingleton [x] = True
        isSingleton _   = False


mDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFTwoFinger graph = idomToDFFast graph $ (fromSuccMap $ imdomOfTwoFinger6 graph :: gr () ())

imdomTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
imdomTwoFingerGraphP = cdepGraphP imdomTwoFingerGraph

imdomTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
imdomTwoFingerGraph = cdepGraph imdomTwoFingercd

imdomTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
imdomTwoFingercd = xDFcd mDFTwoFinger



type SmmnFunctional = Map (Node,Node,Node) (Set (T Node)) -> Map (Node,Node,Node) (Set (T Node))
type SmmnFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> SmmnFunctional


fMust :: DynGraph gr => SmmnFunctionalGen gr a b
fMust graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 `elem` toNxtCondX,
                                                                      not $ m2 `elem` (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 `elem` toNxtCondX,
                                                                     m1 `elem` (reachable x)
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]


fMustNoReachCheck :: DynGraph gr => SmmnFunctionalGen gr a b
fMustNoReachCheck graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 `elem` toNxtCondX,
                                                                      not $ m2 `elem` (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 `elem` toNxtCondX
                                                                     -- m1 `elem` (reachable x)
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]





fMay :: DynGraph gr => SmmnFunctionalGen gr a b
fMay graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 `elem` toNxtCondX,
                                                                      not $ m2 `elem` (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     let toNxtCondX = toNextCond x,
                                                                     m1 `elem` (reachable x),
                                                                     not $ m2 `elem` toNxtCondX,
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) > 0
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]


fMay' :: DynGraph gr => SmmnFunctionalGen gr a b
fMay' graph condNodes reachable nextCond toNextCond s =
              (∐) [ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) ])]
                                | p <- condNodes,
                                  x <- suc graph p,
                                  let toNxtCondX = toNextCond x,
                                  m1 <- toNxtCondX,
                                  m2 <- nodes graph,
                                  not $ m2 `elem` (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                  ]
           ⊔      Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 `elem` toNxtCondX,
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) > 0
                                             ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes
                  ]



combinedBackwardSlice :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map (Node, Node) (Set Node) -> Node -> Node -> Set Node
combinedBackwardSlice graph cd od m1 m2 =  (㎲⊒) (Set.fromList [m1, m2]) f
  where f slice = slice
                ⊔ Set.fromList [ n | m <- Set.toList slice, n <- Set.toList $ cdReversed ! m ]
                ⊔ Set.fromList [ n | m1 <- Set.toList slice, m2 <- Set.toList slice, m1 /= m2, n <- Set.toList $ od ! (m1,m2) ]
        cdReversed = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
                   ⊔ (fmap Set.fromList $ invert' $ fmap Set.toList cd )

ntscdMyDodSlice :: (Show (gr a b), DynGraph gr) => gr a b ->  Node -> Node -> Set Node
ntscdMyDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = ntscdF3 graph
        d     = myDod graph

ntscdDodSlice :: (Show (gr a b), DynGraph gr) => gr a b ->  Node -> Node -> Set Node
ntscdDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = ntscdF3 graph
        d     = dod graph


        
nticdMyWodSlice :: (Show (gr a b), DynGraph gr) => gr a b ->  Node -> Node -> Set Node
nticdMyWodSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = nticdF3 graph
        w     = myWod graph

wodTEILSlice :: (Show (gr a b), DynGraph gr) => gr a b ->  Node -> Node -> Set Node
wodTEILSlice graph = combinedBackwardSlice graph empty w
  where empty = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
        w     = wodTEIL' graph


wodTEIL :: (DynGraph gr, Show (gr a b)) => gr a b -> Map Node (Set (Node,Node))
wodTEIL graph = xodTEIL smmnMust smmnMay graph
  where smmnMust = smmnFMustWod graph
        smmnMay  = smmnFMayWod graph


wodTEIL' :: (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node,Node) (Set Node)
wodTEIL' graph = Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
               ⊔ (fmap Set.fromList $ invert' $ fmap Set.toList wTEIL )
  where wTEIL = wodTEIL graph




mustBeforeMaximalDef :: (DynGraph gr, Show (gr a b)) => gr a b -> Map Node (Set (Node, Node))
mustBeforeMaximalDef graph =
                Map.fromList [ (n, Set.empty) | n <- nodes graph]
              ⊔ Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- nodes graph,
                                                            m2 <- nodes graph,
                                                            n /= m1, n /= m2, m1 /= m2,
                                                            (∀) paths (\path -> (m1,m2) `inPathBefore` (n,path))
                                                ]
                               ) | n <- nodes graph, let paths = maximalPaths ! n ]
  where sccs = scc graph
        sccOf m =  the (m `elem`) $ sccs
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        inPathBefore = inPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.

smmnFMustWod :: (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustWod graph = smmnGfp graph fMust


smmnFMayWod :: (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMayWod graph = smmnLfp graph fMay'


smmnFMustDod :: (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustDod graph = smmnLfp graph fMust

smmnFMustNoReachCheckDod :: (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustNoReachCheckDod graph = smmnLfp graph fMustNoReachCheck


smmnFMayDod :: (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMayDod graph = smmnLfp graph fMay'




smmnGfp :: (DynGraph gr , Show (gr a b)) => gr a b -> SmmnFunctionalGen gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnGfp graph f = -- traceShow graph $ 
                  (𝝂) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m1,m2,p), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m1,m2,p), Set.fromList [ (p,x) | x <- suc graph p]) | m1 <- nodes graph, m2 <- nodes graph, m2 /= m1, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

smmnLfp :: (DynGraph gr, Show (gr a b)) => gr a b -> SmmnFunctionalGen gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnLfp graph f = -- traceShow graph $ 
                  (㎲⊒) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m1,m2,p), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

{- a combinator to generate order dependencies in the style of [2]

  [2] Slicing for modern program structures: a theory for eliminating irrelevant loops
      TorbenAmtoft
      https://doi.org/10.1016/j.ipl.2007.10.002
-}
xodTEIL:: DynGraph gr => (Map (Node, Node, Node ) (Set (T Node))) ->
                         (Map (Node, Node, Node ) (Set (T Node))) ->
                         gr a b ->
                         Map Node (Set (Node,Node))
xodTEIL smmnMust smmnMay graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- nodes graph,
                                                  m2 <- nodes graph,
                                                  Set.size (smmnMay ! (m1,m2,n)) > 0,
                                                  Set.size (smmnMay ! (m2,m1,n)) > 0,
                                                  let s12n = smmnMust ! (m1,m2,n),
                                                  let s21n = smmnMust ! (m2,m1,n),
                                                  Set.size s12n + Set.size s21n > 0
                                      ]
                     ) | n <- condNodes
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]

{- a combinator to generate order dependencies in the style of [1] -}
xod smmnMust s graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  Set.size (s ! (m1,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  Set.size (s ! (m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  let s12n = smmnMust ! (m1,m2,n),
                                                  let s21n = smmnMust ! (m2,m1,n),
                                                  Set.size s12n > 0,
                                                  Set.size s21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


myXod smmnMust s graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  Set.size (s ! (m1,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  Set.size (s ! (m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  let s12n = smmnMust ! (m1,m2,n),
                                                  Set.size s12n > 0,
                                                  Set.size s12n < (Set.size $ Set.fromList $ suc graph n)
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


myWod graph = myXod sMust s3 graph
  where sMust = smmnFMustWod graph
        s3    = snmF3 graph

myWodFast :: forall gr a b. (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node,Node) (Set Node)
myWodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- isinkdomCycles,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       let color = colorLfpFor graph m1 m2,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- (entriesFor cycle) ++ (condsIn cycle),
                                                                   n /= m1 ∧ n /= m2,
                                                           assert (m1 `elem` (suc isinkdomTrc n)) True,
                                                           assert (m2 `elem` (suc isinkdomTrc n)) True,
                                                                   myDependence color n
                                                                  -- let s12n = sMust ! (m1,m2,n),
                                                                  -- Set.size s12n > 0,
                                                                  -- Set.size s12n < (Set.size $ Set.fromList $ suc graph n)
                                                ]
                  ]
  where sMust = smmnFMustWod graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∈ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∈ cycle]
        condsIn cycle    = [ n | n <- cycle, length (suc graph n) > 1]
        myDependence = myDependenceFor graph


dod graph = xod sMust s3 graph
  where sMust = smmnFMustDod graph
        s3    = snmF3Lfp graph

myDod graph = myXod sMust s3 graph
  where sMust = smmnFMustDod graph
        s3    = snmF3Lfp graph


myDodFast :: forall gr a b. (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node,Node) (Set Node)
myDodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- imdomCycles,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       let color = colorLfpFor graph m1 m2,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entriesFor cycle,
                                                           assert (n /= m1 ∧ n /= m2) True,
                                                           assert (m1 `elem` (suc imdomTrc n)) True,
                                                           assert (m2 `elem` (suc imdomTrc n)) True,
                                                                  myDependence color n
                                                ]
                   ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        imdom = imdomOfTwoFinger6 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∈ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∈ cycle]
        myDependence = myDependenceFor graph



dodFast :: forall gr a b. (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node,Node) (Set Node)
dodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 `elem` (suc imdomTrc n),
                                                  m2 `elem` (suc imdomTrc n),
                                                  -- allImdomReachable (Set.fromList [n]) n (Set.fromList [m1,m2]),
                                                  let s12n = sMust ! (m1,m2,n),
                                                  let s21n = sMust ! (m2,m1,n),
                                                  Set.size s12n > 0,
                                                  Set.size s21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where sMust = smmnFMustNoReachCheckDod graph
        imdom = imdomOfTwoFinger6 graph
        -- allImdomReachable seen n ms
        --   | Set.null ms   = True
        --   | n ∈ ms        = allImdomReachable               seen  n (Set.delete n ms)
        --   | Set.null next = False
        --   | n' ∈ seen     = False
        --   | otherwise     = allImdomReachable (Set.insert n seen) n' ms
        --      where next = imdom ! n
        --            [n'] = Set.toList next
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



{- this algorithm does *not* work, see: Program.Examples.dodSuperFastCounterExample6 -}
dodSuperFast :: forall gr a b. (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node,Node) (Set Node)
dodSuperFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 `elem` (suc imdomTrc n),
                                                  m2 `elem` (suc imdomTrc n),
                                                  (∃) (suc graph n) (\x -> mustBeforeAny (m1,m2,x)),
                                                  (∃) (suc graph n) (\x -> mustBeforeAny (m2,m1,x))
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where imdom = imdomOfTwoFinger6 graph
        pis   = possibleIntermediateNodesFromiXdom graph imdom
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())
        mustBeforeAny (m1,m2,x) = mustBeforeAnySeen (Set.fromList [x]) x
          where mustBeforeAnySeen seen n
                  | n == m2 = False
                  | n == m1 = True
                  | Set.null next = False
                  | m2 ∈ toNext = False
                  | otherwise = mustBeforeAnySeen (Set.insert n seen) n'
                      where next = imdom ! n
                            toNext   = pis ! n
                            [n']     = Set.toList next
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


data Color = Undefined | White | Black | Uncolored deriving (Show, Ord, Eq, Bounded, Enum)

instance JoinSemiLattice Color where
  Undefined `join` x         = x
  x         `join` Undefined = x

  Uncolored `join` x         = Uncolored
  x         `join` Uncolored = Uncolored

  White     `join` White     = White
  Black     `join` Black     = Black

  x         `join` y         = Uncolored

instance BoundedJoinSemiLattice Color where
  bottom = Undefined


instance PartialOrd.PartialOrd Color where
  c1 `leq` c2 =  c1 ⊔ c2 == c2

dodColoredDag :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDag graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 `elem` (suc trcGraph m2),
                                                  m2 `elem` (suc trcGraph m1),
                                                  dependence n m1 m2
                               ]
                      ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                   ]
  where trcGraph = trc graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph


myDependenceFor graph color n = whiteChild ∧ otherChild
          where 
                whiteChild = (∃) (suc graph n) (\x -> color ! x == White)
                otherChild = (∃) (suc graph n) (\x -> assert ( color ! x /= Undefined) 
                                                      color ! x /= White)


dependenceFor graph n m1 m2 = whiteChild ∧ blackChild
          where color = colorFor graph n m1 m2
                whiteChild = (∃) (suc graph n) (\x -> color ! x == White)
                blackChild = (∃) (suc graph n) (\x -> color ! x == Black)

colorFor graph n m1 m2 = color
          where color = fst $ colorFor n (init, Set.fromList [m1,m2])
                  where init =             Map.fromList [ (m1, White), (m2, Black) ]
                               `Map.union` Map.fromList [ (n, Uncolored) | n <- nodes graph]
                colorFor :: Node -> (Map Node Color, Set Node) -> (Map Node Color, Set Node)
                colorFor n (color, visited)
                  | n ∈ visited = (color, visited)
                  | otherwise   = ( Map.insert n ((∐) [ color' ! x | x <- suc graph n ]) color', visited')
                      where (color', visited') = foldr colorFor (color, Set.insert n visited) (suc graph n)



colorFunctionalFor :: forall gr a b. DynGraph gr => gr a b -> Node -> Node -> Map Node Color -> Map Node Color
colorFunctionalFor graph m1 m2 color =
      color
    ⊔ Map.fromList [ (m1, White), (m2, Black) ]
    ⊔ Map.fromList [ (n, (∐) [ color ! x | x <- suc graph n ]) | n <- nodes graph, n /= m1, n /= m2 ]

colorLfpFor graph m1 m2 =  (㎲⊒) (Map.fromList [ (n, Undefined) | n <- nodes graph]) f
  where f = colorFunctionalFor graph m1 m2

dodColoredDagFixed :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDagFixed graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 `elem` (suc imdomTrc n),
                                                  m2 `elem` (suc imdomTrc n),
                                                  dependence n m1 m2
                               ]
                      ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                   ]
  where trcGraph = trc graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph
        imdom = imdomOfTwoFinger6 graph
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())


dodColoredDagFixedFast :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDagFixedFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((mm1,mm2), ns) | cycle <- imdomCycles,
                                       (m1,m2) <- unorderedPairsOf cycle,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entriesFor cycle,
                                                           assert (n /= m1 ∧ n /= m2) True,
                                                           assert (m1 `elem` (suc imdomTrc n)) True,
                                                           assert (m2 `elem` (suc imdomTrc n)) True,
                                                                   dependence n m1 m2
                                                ],
                                       (mm1,mm2) <- [(m1,m2),(m2,m1)]
                   ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph
        imdom = imdomOfTwoFinger6 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∈ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∈ cycle]

        unorderedPairsOf []     = []
        unorderedPairsOf (x:xs) = [ (x,y) | y <- xs ] ++ unorderedPairsOf xs


wodFast :: forall gr a b. (DynGraph gr, Show (gr a b)) => gr a b -> Map (Node,Node) (Set Node)
wodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  let sMay12n = sMay ! (m1,m2,n),
                                                  let sMay21n = sMay ! (m2,m1,n),
                                                  ((n /= m2) ∧ (Set.size sMay12n > 0))  ∨  ((n == m1) ∧ (m2 ∈ suc graphTrc n)),
                                                  ((n /= m1) ∧ (Set.size sMay21n > 0))  ∨  ((n == m2) ∧ (m1 ∈ suc graphTrc n)),
                                                  let sMust12n = sMust ! (m1,m2,n),
                                                  let sMust21n = sMust ! (m2,m1,n),
                                                  Set.size sMust12n > 0 ∨ Set.size sMust21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where sMust = smmnFMustNoReachCheckDod graph
        sMay  = smmnFMayWod graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        graphTrc = trc $ graph



wodDef :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
wodDef graph = Map.fromList [ ((m1,m2), Set.fromList [ p | p <- condNodes,
                                                           (∃) (maximalPaths ! p) (\path -> (m1,m2) `mayInPathBefore` (p,path)),
                                                           (∃) (maximalPaths ! p) (\path -> (m2,m1) `mayInPathBefore` (p,path)),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m2,m1) `inPathBefore` (x,path))
                                                           ∨ (∀) (maximalPaths ! x) (\path -> (m1,m2) `inPathBefore` (x,path))
                                                           )
                                        ]
                                )
                            | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
  where sccs = scc graph
        sccOf m =  the (m `elem`) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPathBefore = inPathForBefore graph doms
        mayInPathBefore = mayInPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're ju

dodDef :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodDef graph = Map.fromList [ ((m1,m2), Set.fromList [ p | p <- condNodes,
                                                           (∀) (maximalPaths ! p) (\path ->   m1 `inPath` (p,path)
                                                                                            ∧ m2 `inPath` (p,path)),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m1,m2) `inPathBefore` (x,path))
                                                           ),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m2,m1) `inPathBefore` (x,path))
                                                           )
                                        ]
                                )
                            | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
  where sccs = scc graph
        sccOf m =  the (m `elem`) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        inPathBefore = inPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.

inPathForBefore :: DynGraph gr => gr a b -> Map Node [(Node, [Node])] -> (Node,Node) -> (Node, MaximalPath) -> Bool
inPathForBefore graph' doms (m1,m2) (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  thispath@(MaximalPath []            endScc endNodes@(end:_))
                    | m1 `elem` endScc  = -- traceShow (entries, thispath) $ 
                                          (∀) entries (\entry -> let domsEnd = (doms ! entry) `get` end
                                                                     domsm2   = (doms ! entry) `get` m2 in
                                                                 (entry /= end || m1 == entry) && m1 `elem` domsEnd && ((not $ m2 `elem` endScc) ∨ (m1 `elem` domsm2))
                                          )
                                          ∨ ((m1 `elem` endNodes) ∧
                                             (∀) entries (\entry ->  let domsm2   = (doms ! entry) `get` m2 in ((not $ m2 `elem` endScc) ∨ (m1 `elem` domsm2)))
                                          )

                    | otherwise         = -- traceShow (entries, thispath) $
                                          False
                inPathFromEntries entries  thispath@(MaximalPath (scc:prefix)  endScc endNodes)
                    | m1 `elem` scc = -- traceShow (entries, thispath) $
                                      (∀) entries (\entry ->
                                        (∀) exits (\exit -> let domsexit = (doms ! entry) `get` exit 
                                                                domsm2   = (doms ! entry) `get` m2   in
                                             (entry /= exit || m1 == entry) && m1 `elem` domsexit && ((not $ m2 `elem` scc) ∨ (m1 `elem` domsm2))
                                        )
                                      )
                                      ∨
                                      ((m1 `elem` endNodes) ∧
                                       (∀) entries (\entry ->  let domsm2   = (doms ! entry) `get` m2 in ((not $ m2 `elem` scc) ∨ (m1 `elem` domsm2)))
                                      )
                    | otherwise    =  -- traceShow (entries, thispath) $
                                      (not $ m2 `elem` scc) ∧ inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' `elem` next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = case  List.lookup key assocs of
                                   Nothing -> error $ "lookup " ++ (show key) ++ "  " ++ (show assocs)
                                   Just v  -> v



mayInPathForBefore :: DynGraph gr => gr a b -> Map Node [(Node, [Node])] -> (Node,Node) -> (Node, MaximalPath) -> Bool
mayInPathForBefore graph' doms (m1,m2) (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  thispath@(MaximalPath []            endScc endNodes@(end:_))
                    | m1 `elem` endScc ∧ m2 `elem` endScc  = -- traceShow (entries, thispath) $
                                      (∃) entries (\entry -> let domsm1 = (doms ! entry) `get` m1 in
                                                             not $ m2 `elem` domsm1
                                      )
                    | m1 `elem` endScc  = -- traceShow (entries, thispath) $
                                          True
                    | otherwise         = -- traceShow (entries, thispath) $
                                          False
                inPathFromEntries entries  thispath@(MaximalPath (scc:prefix)  endScc endNodes)
                    | m1 `elem` scc ∧ m2 `elem` scc = -- traceShow (entries, thispath) $
                                      (∃) entries (\entry -> let domsm1 = (doms ! entry) `get` m1 in
                                                             not $ m2 `elem` domsm1
                                      )
                    | m1 `elem` scc = -- traceShow (entries, thispath) $
                                      True
                    | m2 `elem` scc = -- traceShow (entries, exits, thispath) $
                                      (∃) entries (\entry ->
                                        (∃) exits (\exit -> let domsexit = (doms ! entry) `get` exit in
                                                                not $ m2 `elem` domsexit
                                        )
                                      )
                                    ∧ inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                    | otherwise     = -- traceShow (entries, thispath) $
                                      inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' `elem` next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = case  List.lookup key assocs of
                                   Nothing -> error $ "lookup " ++ (show key) ++ "  " ++ (show assocs)
                                   Just v  -> v





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
      case pre graph start of
        (_:_:_) -> Just start
        []      -> Just start
        [n]     -> prevRepresentant [start] n start
    where prevRepresentant seen n m -- invariance : n is only predecessor of m, m is no join node
              | n ∈ seen  = Nothing
              | otherwise = case suc graph n of
                  (_:_:_) -> Just m
                  [m']    -> assert (m' == m) $
                             case pre graph n of
                               [n']    -> prevRepresentant (n:seen) n' n
                               _       -> Just n


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
maximalPathsFor graph = maximalPathsForNodes graph [ n | p <- condNodes, n <- suc graph p ++ [p]]
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




data Reachability  = Unreachable | Unknown | FixedSteps Integer | FixedStepsPlusOther Integer Node | UndeterminedSteps deriving (Show, Eq)
instance JoinSemiLattice Reachability where
  Unreachable   `join` x           = x
  x             `join` Unreachable = x

  FixedSteps x `join` FixedSteps y
    | x == y    = FixedSteps x
    | otherwise = UndeterminedSteps

  FixedStepsPlusOther x n  `join` FixedStepsPlusOther y m
    | x == y ∧ n == m  = FixedStepsPlusOther x n 
    | otherwise = UndeterminedSteps

  x         `join` y         = UndeterminedSteps

instance BoundedJoinSemiLattice Reachability where
  bottom = Unreachable

instance Ord Reachability where
  Unreachable   `compare` Unreachable = EQ
  Unreachable   `compare` x           = LT
  x             `compare` Unreachable = GT

  FixedSteps x `compare` FixedSteps y = compare x y
  FixedStepsPlusOther x n  `compare` FixedStepsPlusOther y m = case cnm of
      EQ -> compare x y
      _  -> cnm
    where cnm  = compare n m

  FixedSteps _ `compare` FixedStepsPlusOther _ _ = LT
  FixedStepsPlusOther _ _ `compare` FixedSteps _ = GT
 
  UndeterminedSteps `compare` UndeterminedSteps = EQ
  UndeterminedSteps `compare` x                 = GT
  x                 `compare` UndeterminedSteps = LT
  

plusAt :: Node -> Reachability -> Integer ->  Reachability
plusAt n r y = r `plus` y where
  (FixedSteps x)            `plus` y = FixedSteps (x+y)
  (FixedStepsPlusOther x m) `plus` y = FixedStepsPlusOther (x+y) m
  (Unreachable)             `plus` y = Unreachable
  (UndeterminedSteps)       `plus` y = FixedStepsPlusOther y n


joinPlus ::  Reachability -> Integer ->  Reachability
joinPlus r y = r `plus` y where
  (FixedSteps x)            `plus` y = FixedSteps (x+y)
  (FixedStepsPlusOther x n) `plus` y = FixedStepsPlusOther (x+y) n
  r                         `plus` y = r


type SmnTimingEquationSystem =
       Map (Node,Node) (Map (Node,Node) Reachability)
type SmnTimingEquationSystemGen gr a b =
       gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node])
    -> SmnTimingEquationSystem

solveTimingEquationSystem ::  SmnTimingEquationSystem -> SmnTimingEquationSystem
solveTimingEquationSystem s = if (s == s') then s else solveTimingEquationSystem s'
          where s' =     Map.fromList [ ((m,p), Map.fromList [ ((p,x), r) | ((p',x), rpx) <- Map.assocs smp,
                                                                            assert (p == p') True,
                                                                            let r = case rpx of
                                                                                      FixedStepsPlusOther i q -> let smq = s ! (m,q)
                                                                                                                     rmq = (∐) [ r | r <- Map.elems smq ]
                                                                                                                 in case rmq of
                                                                                                                      FixedSteps j             -> FixedSteps (1+i+j)
                                                                                                                      FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+i+j) q'
                                                                                                                      _            -> rpx
                                                                                      _                       -> rpx
                                                            ]
                                        )
                                      | ((m,p), smp) <- Map.assocs s ]


timingF3EquationSystem :: DynGraph gr => SmnTimingEquationSystemGen gr a b
timingF3EquationSystem graph condNodes reachable nextCond toNextCond =
                   Map.fromList [ ((m,p), Map.fromList  [ ((p,x), FixedSteps i) | x <- suc graph p,
                                                                                  (i,m2) <- (zip [0..] (toNextCondInOrder x)), m2 == m ]
                                  ) | m <- nodes graph, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), reachability) | x <- (suc graph p),
                                                                           m `elem` reachable x,
                                                                           Just n <- [nextCond x],
                                                                           let plus = plusAt n,
                                                                           let toNextCondX = toNextCond x,
                                                                           not $ m ∈ toNextCondX,
                                                                           let stepsToN = List.genericLength toNextCondX - 1,
                                                                           let reachabilityFromN = FixedStepsPlusOther 0 n,
                                                                           let reachability = reachabilityFromN `plus` stepsToN
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]
  where toNextCondInOrder = reverse . toNextCond

timingF3EquationSystem' :: DynGraph gr => SmnTimingEquationSystemGen gr a b
timingF3EquationSystem' graph condNodes reachable nextCond toNextCond =
                        Map.fromList [ ((m,p), Map.empty) | m <- nodes graph, p <- condNodes]
                 ⊔ (∐) [ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), FixedSteps i) ]) ]
                         | p <- condNodes, x <- suc graph p,    (i,m) <- (zip [0..] (toNextCondInOrder x))
                       ]
                 ⊔ (∐) [ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), reachability) ]) ]
                         | p <- condNodes, x <- suc graph p,    Just n <- [nextCond x],
                                                                           m <- reachable x,
                                                                           let plus = plusAt n,
                                                                           let toNextCondX = toNextCond x,
                                                                           not $ m ∈ toNextCondX,
                                                                           let stepsToN = List.genericLength toNextCondX - 1,
                                                                           let reachabilityFromN = FixedStepsPlusOther 0 n,
                                                                           let reachability = reachabilityFromN `plus` stepsToN
                        ]
  where toNextCondInOrder = reverse . toNextCond


snmTimingEquationSystem :: DynGraph gr => gr a b -> SmnTimingEquationSystemGen gr a b -> SmnTimingEquationSystem
snmTimingEquationSystem graph f = f graph condNodes reachable nextCond toNextCond
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

snmTimingF3 :: DynGraph gr => gr a b -> SmnTimingEquationSystem
snmTimingF3 graph     = snmTimingEquationSystem graph timingF3EquationSystem'

snmTimingSolvedF3 :: DynGraph gr => gr a b -> SmnTimingEquationSystem
snmTimingSolvedF3 graph = snmTimingEquationSystem graph timingSolvedF3EquationSystem
  where timingSolvedF3EquationSystem graph condNodes reachable nextCond toNextCond = solveTimingEquationSystem $ timingF3EquationSystem' graph condNodes reachable nextCond toNextCond

timingF3summary :: DynGraph gr => gr a b -> Map Node (Map Node Reachability)
timingF3summary     = timingXsummary snmTimingF3

timingSolvedF3summary :: DynGraph gr => gr a b -> Map Node (Map Node Reachability)
timingSolvedF3summary = timingXsummary snmTimingSolvedF3

timingXsummary :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Map Node Reachability)
timingXsummary snmTiming graph = 
      Map.fromList [ (n, Map.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Map.fromList [ (m,r `joinPlus` 1 ) | m <- nodes graph,
                                                          m /= n,
                                                          let rmn = s ! (m,n),
                                                          let r = (∐) [ r | r <- Map.elems rmn ]
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


timingF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingF3dependence     = timingXdependence snmTimingF3

timingSolvedF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSolvedF3dependence = timingXdependence snmTimingSolvedF3

timingSolvedF3sparseDependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSolvedF3sparseDependence = timingXsparseDependence snmTimingSolvedF3


timingXdependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
timingXdependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
--                                          m /= n,
                                            let rmn = s ! (m,n),
                                            (length [ r | r <- Map.elems rmn, r /= Unreachable ]) > 1,
                                            let r = (∐) [ r | r <- Map.elems rmn ],
                                            r == UndeterminedSteps
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



timingXsparseDependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
timingXsparseDependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            m /= n,
                                            let rmn = s ! (m,n),
                                            (length [ r | r <- Map.elems rmn, r /= Unreachable ]) > 1,
                                            (∃) (Map.elems rmn) (\r ->
                                              (∃) (Map.elems rmn) (\r' ->  r ⊔ r' == UndeterminedSteps ∧ ( 
                                                                             case (r,r') of
                                                                               (FixedStepsPlusOther _ u, FixedStepsPlusOther _ v)  -> (not $ n ∈ [u,v]) ∧ (u /= v)
                                                                               _                                                   -> True
                                                                           )
                                              )
                                            )
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        trncl = trc graph
        nextCond = nextCondNode graph

type TimeDomFunctional = Map Node (Map Node (Set Integer)) ->  Map Node (Map Node (Set Integer))
type TimeDomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> TimeDomFunctional

tdomOfLfp :: DynGraph gr => gr a b -> TimeDomFunctionalGen gr a b -> Map Node (Set (Node, Integer))
tdomOfLfp graph f = fmap (\m -> Set.fromList [ (n, steps) | (n, ss) <- Map.assocs m, steps <- Set.toList ss ]) $
        (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Map.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

fTimeDom :: DynGraph gr => TimeDomFunctionalGen gr a b
fTimeDom graph _ _ nextCond toNextCond = f 
  where f timeDomOf = fmap (fmap (Set.singleton . Set.findMin)) $ 
                      Map.fromList [ (y, Map.fromList [(y, Set.fromList [0]    )]) | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Map.fromList [(n, Set.fromList [steps]) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                                   | y <- nodes graph
                                                                                     
                                   ]
                    ⊔ Map.fromList [ (y,
                                         fmap (Set.map (\s -> s + (steps + 1))) $
                                         Map.filter (not . Set.null) $
                                         (∏) [ timeDomOf ! x | x <- suc graph n ]
                                     )
                                                                                   | y <- nodes graph,
                                                                                     Just n <- [nextCond y],
                                                                                     let steps = (toInteger $ length $ toNextCond y) - 1
                                   ]
timdomOfLfp graph = tdomOfLfp graph fTimeDom



type TimeMayDomFunctional = Map Node (Map Node Reachability) ->  Map Node (Map Node Reachability)
type TimeMayDomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> TimeMayDomFunctional

fTimeMayDom :: DynGraph gr => TimeMayDomFunctionalGen gr a b
fTimeMayDom graph _ _ nextCond toNextCond = f 
  where f timeDomOf = -- traceShow timeDomOf $
                      Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                               | y <- nodes graph
                                   ]
                    ⊔ Map.fromList [ (y, let all = (∐) [ Map.keysSet $ timeDomOf ! x | x <- suc graph n ] in
                                         let plus = joinPlus in
                                         fmap (\s -> s `plus` (steps + 1)) $
                                         Map.fromList [ (m, (∐) [  steps  | x <- suc graph n, Just steps <- [Map.lookup m (timeDomOf ! x)]   ]) | m <- Set.toList all, not $ m ∈ toNextCond y ]
                                     )
                                                                                   | y <- nodes graph,
                                                                                     Just n <- [nextCond y],
                                                                                     let steps = (toInteger $ length $ toNextCond y) - 1
                                   ]



type SnTimingEquationSystem =
       Map Node (Map Node Reachability)
type SnTimingEquationSystemGen gr a b =
       gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node])
    -> SnTimingEquationSystem


timeMayDomEquationSystemGen :: DynGraph gr => SnTimingEquationSystemGen gr a b
timeMayDomEquationSystemGen graph condNodes _ nextCond toNextCond =
                      -- Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                      -- ⊔
                         Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                                | p <- condNodes, y <- suc graph p
                         ]

timeMayDomEquationSystem graph = timeMayDomEquationSystemGen graph condNodes reachable nextCond toNextCond
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

solveSnTimingEquationSystem ::  DynGraph gr => gr a b -> SnTimingEquationSystem -> SnTimingEquationSystem
solveSnTimingEquationSystem graph s = solve s0
          where nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                s0 = s
                solve s = -- traceShow (s ! 3) $ traceShow (s ! 4) $ traceShow ("") $
                          if (s == s') then s else solve s'
                  where s' = Map.fromList [ (y, Map.union (s0 ! y) r) | (y, sy) <- Map.assocs s,
                                                                        let r = Map.fromList [ (m, case sxm of
                                                                                                     FixedSteps j             -> FixedSteps (1+steps+j)
                                                                                                     FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+steps+j) q'
                                                                                                     UndeterminedSteps        -> FixedStepsPlusOther steps n
                                                                                               )
                                                                                             | Just n <- [nextCond y],
                                                                                               let steps = (toInteger $ length $ toNextCond y) - 1,
                                                                                               let sx =  (∐) [ s ! x | x <- suc graph n ],
                                                                                               (m, sxm) <- Map.assocs sx
                                                                                ]
                            ]


timingSnSolvedDependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSnSolvedDependence graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (p, Set.fromList [ m | let sx = (∐) [ s ! x  | x <- suc graph p ],
                                            (m, sxm) <- Map.assocs sx,
                                            sxm == UndeterminedSteps
                                      ]
                     ) | p <- condNodes
                  ]
  where s0 =  timeMayDomEquationSystem graph
        s  =  solveSnTimingEquationSystem graph s0
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


tmaydomOfLfp :: DynGraph gr => gr a b -> TimeMayDomFunctionalGen gr a b -> Map Node (Set (Node, Integer ))
tmaydomOfLfp graph f = fmap (\m -> Set.fromList [ (n, steps) | (n, ss) <- Map.assocs m, FixedSteps steps <- [ss] ]) $
-- tmaydomOfLfp :: DynGraph gr => gr a b -> TimeMayDomFunctionalGen gr a b -> Map Node (Set (Node, Reachability))
-- tmaydomOfLfp graph f = fmap (\m ->   Set.fromList [ (n, r) | (n, rs) <- Map.assocs m, r <- [rs] ]) $
        (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Map.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

timmaydomOfLfp graph = tmaydomOfLfp graph fTimeMayDom




timdomOfTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set (Node, Integer))
timdomOfTwoFinger graph = fmap toSet $ twoFinger 0 worklist0 imdom0
  where toMap Nothing  = Map.empty
        toMap (Just (x, sx)) = Map.fromList [(x,sx)]
        toSet Nothing  = Set.empty
        toSet (Just x) = Set.fromList [x]
        imdom0   =             Map.fromList [ (x, Just (z,1)) | x <- nodes graph, [z] <- [suc graph x]]
                   `Map.union` Map.fromList [ (x, Nothing   ) | x <- nodes graph]
        worklist0   = condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (suc graph x) > 1 ]
        prevConds   = prevCondNodes graph

        twoFinger :: Integer -> Set Node ->  Map Node (Maybe (Node, Integer)) -> Map Node (Maybe (Node, Integer))
        twoFinger i worklist imdom
            |   Set.null worklist = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                    -- traceShow (Set.size worklist0, i) $ 
                                    imdom
            | otherwise           = -- traceShow (x, mz, zs, influenced, worklist, imdom) $
                                    if (not $ new) then twoFinger (i+1)               worklist'                                   imdom
                                    else                twoFinger (i+1) (influenced ⊔ worklist')  (Map.insert x zs                imdom)
          where (x, worklist')  = Set.deleteFindMin worklist
                mz :: Maybe (Node, Integer, Set Node)
                mz = foldM1 lca [ (y, 1, Set.empty) | y <- suc graph x]
                zs = case mz of
                      Just (z,sz,_)  -> if z /= x then
                                          Just (z, sz)
                                        else
                                          Nothing
                      Nothing ->  Nothing
                new     = assert (isNothing $ imdom ! x) $
                          (not $ isNothing zs)
                influenced = let imdomRev = invert' $ fmap maybeToList $ fmap (liftM fst) imdom
                                 preds = predsSeenFor imdomRev [x] [x]
                             in  -- traceShow (preds, imdomRev) $
                                 Set.fromList $ [ n | n <- foldMap prevConds preds, n /= x, isNothing $ imdom ! n]
                lca :: (Node, Integer, Set Node) -> (Node, Integer, Set Node) -> Maybe (Node, Integer, Set Node)
                lca  (n, sn, forbiddenNs) (m, sm, forbiddenMs) = lca' imdom (n, sn, Map.fromList [(n,sn)], forbiddenNs) (m, sm, Map.fromList [(m,sm)], forbiddenMs)
                lca' :: Map Node (Maybe (Node, Integer)) -> (Node, Integer, Map Node Integer, Set Node) -> (Node, Integer, Map Node Integer, Set Node ) -> Maybe (Node, Integer, Set Node)
                lca' c (n, sn, ns, forbiddenNs) (m, sm, ms, forbiddenMs)
                    | m ∈ Map.keys ns ∧ ((ns ! m) == sm) = -- traceShow ((n,sn,ns,forbiddenNs), (m,sm,ms,forbiddenMs)) $
                                                           assert (ms ! m == sm) $
                                                           let left  = Set.fromList [ v | (v,s) <- Map.assocs ns, s <= sm ]
                                                               right = Map.keysSet ms
                                                           in
                                                           assert (left ∩ right == Set.fromList [m]) $
                                                           Just (m, sm, left ∪ right)
                    | n ∈ Map.keys ms ∧ ((ms ! n) == sn) = -- traceShow ((n,sn,ns,forbiddenNs), (m,sm,ms,forbiddenMs)) $
                                                           assert (ns ! n == sn) $
                                                           let left  = Set.fromList [ v | (v,s) <- Map.assocs ms, s <= sn ]
                                                               right = Map.keysSet ns
                                                           in
                                                           assert (left ∩ right == Set.fromList [n]) $
                                                           Just (n, sn, left ∪ right)
                    | otherwise = -- traceShow ((n,sn,ns,forbiddenNs), (m,sm,ms,forbiddenMs)) $
                                  case Set.toList $ (Set.map fst $ toSet $ (c ! n)) ∖ (Map.keysSet ns ∪ forbiddenNs) of
                                     []   -> case Set.toList $ (Set.map fst $ toSet (c ! m)) ∖ (Map.keysSet ms ∪ forbiddenMs) of
                                                []   -> Nothing
                                                [_] -> let Just (m',sm') = c ! m
                                                       in lca' c ( m', sm + sm', Map.insert m' (sm+sm') ms, forbiddenMs) (n, sn, ns, forbiddenNs)
                                     [_] -> let Just (n',sn') = c ! n
                                            in lca' c (m, sm, ms, forbiddenMs) (n', sn + sn', Map.insert n' (sn+sn') ns, forbiddenNs)


alternativeTimingXdependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
alternativeTimingXdependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            m /= n,
                                            let rmn = s ! (m,n),
                                            ((_,nl), rl) <- Map.assocs rmn,
                                            ((_,nr), rr) <- Map.assocs rmn,
                                            if (rl == Unreachable)       then error "unsolved snmTiming" else True,
                                            if (rr == Unreachable)       then error "unsolved snmTiming" else True,
                                            if (rl == UndeterminedSteps) then error "unsolved snmTiming" else True,
                                            if (rr == UndeterminedSteps) then error "unsolved snmTiming" else True,
                                            case (rl,rr) of
                                              (FixedSteps i, FixedSteps j)                         -> (i /= j)
                                              (FixedStepsPlusOther i l', FixedStepsPlusOther j r') -> (i /= j) ∨ (l' /= r')
                                              (FixedSteps i, _)                                    -> True 
                                              (_,            FixedSteps j)                         -> True 
                                              (_,            _)                                    -> False
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


alternativeTimingSolvedF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
alternativeTimingSolvedF3dependence = alternativeTimingXdependence snmTimingSolvedF3
