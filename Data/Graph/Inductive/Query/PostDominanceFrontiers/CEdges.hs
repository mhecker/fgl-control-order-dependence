module Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges where


import Control.Exception.Base (assert)

import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.PQueue.Prio.Max as Prio.Max

import Data.Graph.Inductive.Graph


import Unicode
import Util (reachableFrom, reachableFromM, invert''', findCyclesM, treeLevel, fromSet)

import Data.Graph.Inductive.Util (controlSinks)
import Data.Graph.Inductive.Query.PostDominance (isinkdomOfTwoFinger8ForSinks, imdomOfTwoFinger7)

import Data.Graph.Inductive.Query.NTICDNumbered (iPDomForSinks)

dfViaCEdges :: Graph gr => gr a b -> Map Node (Maybe Node) -> Node -> Set Node
dfViaCEdges graph idom = \x -> Set.fromList [ y | z <- Set.toList $ reachableFrom idom' (Set.fromList [x]),
                                                  y <- cEdges ! z, {- y <- pre graph z, not $ z ∈ idomsOf y -}
                                                  (not $ x ∈ reachableFromM idom (idomsOf y) Set.empty)
                         ]
  where idom' = invert''' idom
        idomsOf y = case idom ! y of
          Nothing -> Set.empty
          Just y' -> cycleOf y'
        (cycleOfM,_) =  findCyclesM $ idom
        cycleOf x = Map.findWithDefault (Set.singleton x) x cycleOfM
        cEdges = Map.fromList [(z, [ y | y <- pre graph z, not $ z ∈ idomsOf y ]) | z <- nodes graph]


idfViaCEdgesFastForCycles :: Graph gr => (Map Node (Set Node), [Set Node]) -> gr a b -> Map Node (Maybe Node) -> Set Node -> Set Node
idfViaCEdgesFastForCycles (cycleOfM, cycles) graph idom = \xs0 -> if Set.null xs0 then
                                       Set.empty
                                     else
                                       let queue0 = Prio.Max.fromList [ (levelOf ! x, x) | x <- Set.toList xs0 ]
                                           ((lvlX,x), queue) = Prio.Max.deleteFindMax queue0
                                       in go Set.empty x lvlX [x] queue xs0
  where 
        go processed x lvlX zs queue idf
          | List.null zs  ∧ Prio.Max.null queue =
             idf
          | List.null zs  ∧ x' ∈ processed = go               processed  x' lvlX'  []                          queue' idf
          | List.null zs                  =  go               processed  x' lvlX'  [x']                        queue' idf
          | z ∈ processed                 =  go               processed  x  lvlX   zs'                         queue  idf
          | otherwise     = 
                            let isDf (y,_,lvlY') = lvlY' < lvlX
                                ys = assert ((∀) (Map.findWithDefault [] z cEdges) (\p@(y,_,_) -> y ∈ idf ∨ isDf p ==  (not $ x ∈ reachableFromM idom (Set.fromList [y]) Set.empty ))) $
                                     List.filter (\p@(y,_,_) -> (not $ y ∈ idf) ∧ isDf p) (Map.findWithDefault [] z cEdges)
                                zNew = case Map.lookup z idom' of
                                  Nothing   -> Set.empty
                                  Just zNew -> zNew
                            in go (Set.insert z processed) x lvlX (Set.fold (:) zs' zNew) (queue `with` ys) (foldr (Set.insert . fst) idf ys)
          where ((lvlX', x'), queue') = Prio.Max.deleteFindMax queue
                (z:zs') = zs
                with queue ys = foldr (\(y,lvlY,_) queue -> Prio.Max.insert lvlY y queue) queue ys
                fst (a,_,_) = a

        idom'  = invert''' idom
        levelOf = Map.fromList [ (n,l) | nl <- treeLevel idom' roots, (n,l) <- nl]
          where roots = foldr (\(n,m) roots -> if m == Nothing then Set.fromList [n] : roots else roots) cycles (Map.assocs idom)
        cEdges :: Map Node [(Node, Integer, Integer)]
        cEdges = foldr f Map.empty (edges graph)
          where f (y,z) cEdges = case idom ! y of
                           Nothing ->                                      Map.insertWith (++) z [(y,levelOf ! y, -1          )] cEdges
                           Just y' -> if z ∈ (cycleOf y') then cEdges else Map.insertWith (++) z [(y,levelOf ! y, levelOf ! y')] cEdges
                cycleOf x = Map.findWithDefault (Set.singleton x) x cycleOfM


idfViaCEdgesFast :: Graph gr => gr a b -> Map Node (Maybe Node) -> Set Node -> Set Node
idfViaCEdgesFast graph idom = idfViaCEdgesFastForCycles cycles graph idom
  where cycles = findCyclesM idom


nticdSliceViaCEdgesFast graph = \ms -> idf ms
  where sinks            = controlSinks graph
        sinkS            = fmap Set.fromList sinks
        sinkNodes        = (∐) [ sink | sink <- sinkS]
        nonSinkCondNodes = Map.fromList [ (n, succs) | n <- nodes graph, not $ n ∈ sinkNodes, let succs = suc graph n, length succs > 1 ]

        idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph

        cycles = (foldr Map.union Map.empty [ Map.fromSet (\n -> sink) sink | sink <- sinkS], sinkS)

        idf = idfViaCEdgesFastForCycles cycles graph idom

nticdSliceNumberedViaCEdgesFast graph = \ms -> idf ms
  where sinks            = controlSinks graph
        sinkS            = fmap Set.fromList sinks
        
        idom = Map.fromList $ iPDomForSinks sinks graph

        cycles = (foldr Map.union Map.empty [ Map.fromSet (\n -> sink) sink | sink <- sinkS], sinkS)

        idf = idfViaCEdgesFastForCycles cycles graph idom


nticdSliceViaCEdgesFastFor :: DynGraph gr => [[Node]] -> gr a b -> Map Node (Maybe Node) ->  Set Node -> Set Node
nticdSliceViaCEdgesFastFor roots graph idom =  \ms -> idf ms
  where sinkS = [ Set.fromList root | root@(_:_:_) <- roots ]
        cycles = (foldr Map.union Map.empty [ Map.fromSet (\n -> sink) sink | sink <- sinkS], sinkS)
        idf = idfViaCEdgesFastForCycles cycles graph idom



ntscdSliceViaCEdgesFast graph = \ms -> idf ms
  where idom = imdomOfTwoFinger7 graph
        idf = idfViaCEdgesFast graph (fmap fromSet idom)
