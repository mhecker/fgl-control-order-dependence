module Data.Graph.Inductive.Query.Slices.CEdges where

import Control.Exception.Base (assert)

import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)


import Data.Graph.Inductive


import Unicode
import Util(fromSet, without, restrict, invert''', reachableFrom)

import Data.Graph.Inductive.Util (delSuccessorEdges, controlSinks)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import Data.Graph.Inductive.Query.PostDominance (isinkdomOftwoFinger8Up, isinkdomOfTwoFinger8DownSingleNodeSinks, isinkdomOfTwoFinger8ForSinks)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges (idfViaCEdgesFastForCycles)


wodTEILSliceViaNticdReuse :: (Show (gr a b),  DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSliceViaNticdReuse g =  \ms ->
    let toMs  = rdfs (Set.toList ms) g
        toMsS = Set.fromList toMs
        g'    = Set.fold (flip delSuccessorEdges) (subgraph toMs g) ms
        msSinks = [ sink | sink <- sinks, (∃) ms (\m -> m `elem` sink) ]
        idom'0 = id
               $ Map.union (Map.fromSet    (\m     -> Nothing) $ ms)
               $ Map.union (Map.mapWithKey (\x _   -> Nothing) $ Map.filterWithKey isEntry $ condNodes')
               $ Map.union (Map.mapWithKey (\x [z] ->                     assert (z /= x) $ Just z                   ) noLongerCondNodes)
               $ Map.union (Map.fromList  [ (x, case suc g' x of { [z] -> assert (z /= x) $ Just z  ; _ -> Nothing  }) | msSink <- msSinks, x <- msSink ])
               $ fmap intoMs
               $ restrict idom toMsS
          where isEntry x _ = case idom ! x of
                  Nothing -> False
                  Just z -> z ∈ sinkNodes
                intoMs n@(Nothing) = n
                intoMs n@(Just x)
                  | x ∈ toMsS = n
                  | otherwise = Nothing
        idom'0Rev   = invert''' idom'0
        processed'0 = reachableFrom idom'0Rev ms
        todo'0      = without nonSinkCondNodes' processed'0
        worklist'0  = Dequeue.fromList $ Map.assocs todo'0
        idom'1 = Map.union (fmap (\x -> Nothing) todo'0)
               $ idom'0
        idom'1Rev = invert''' idom'1
        idom'2 = isinkdomOftwoFinger8Up                  g'                                                               nonSinkCondNodes'   worklist'0  processed'0 idom'1Rev idom'1
        idom'  = isinkdomOfTwoFinger8DownSingleNodeSinks g' sinkNodes' (Map.filterWithKey (\x _ -> idom'2 ! x /= Nothing) nonSinkCondNodes')                                    idom'2
        sinks' = [ [m] | m <- Set.toList ms]
        sinkNodes' = ms
        (condNodes', noLongerCondNodes) =
              Map.partition isCond
            $ fmap (List.filter (∈ toMsS))
            $ restrict condNodes (toMsS ∖ ms)
          where isCond []  = False
                isCond [_] = False
                isCond _   = True
        nonSinkCondNodes' = condNodes'

        sinkS' = fmap Set.fromList sinks'
        cycleOf' =  Map.fromList [ (s, sink) | sink <- sinkS', s <- Set.toList $ sink ]
        
        idom'Direct = Map.fromList $ iPDomForSinks sinks' g'
    in -- (if idom' == idom'Direct then id else traceShow (ms, g, "*****", idom, idom'0, idom'1, idom'2, idom', fmap fromSet $ isinkdomOfTwoFinger8 g')) $ 
       assert (idom' == idom'Direct) $
       -- nticdSliceLazy g' cycleOf' (invert''' idom'Direct) ms
       idfViaCEdgesFastForCycles (cycleOf', sinkS') g' idom'Direct ms
  where
        sinks            = controlSinks g
        sinkNodes        = (∐) [ Set.fromList sink | sink <- sinks]
        condNodes        = Map.fromList [ (n, succs) | n <- nodes g, let succs = suc g n, length succs > 1 ]
        nonSinkCondNodes = without condNodes sinkNodes
        idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes g
