{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.TSCD where

import Control.Exception.Base (assert)

import Data.List (nub)
import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive
import Data.Graph.Inductive.Util (delSuccessorEdges {-fromSuccMap, toSuccMap-})

import Unicode
import Util(reachableFrom, toSet, fromSet, foldM1, invert'')

import Data.Graph.Inductive.Query.LCA(lcaTimdomOfTwoFingerFastCost)
import Data.Graph.Inductive.Query.NTICD (prevCondImmediateNodes, combinedBackwardSlice, onedomOf, domsOf, dfFor, anyDFLocalDef, anyDFUpGivenXViaAnydomsDef, anyDFFromUpLocalDefViaAnydoms, imdomOfTwoFinger6, ntscdSlice, ntscdMyDodSliceViaNtscd, TimeDomFunctionalGen, TimeDomFunctional, tdomOfLfp, itimdomMultipleOfTwoFingerCost)

tscdSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSlice graph =  combinedBackwardSlice graph tscd' w
  where tscd' = invert'' $ tscdOfLfp graph
        w     = Map.empty

tscdCostSlice :: (DynGraph gr) => gr a b ->  (Node -> Node -> Integer) -> Set Node -> Set Node
tscdCostSlice graph cost =  combinedBackwardSlice graph tscd' w
  where tscd' = invert'' $ tscdOfNaiveCostfLfp graph cost 
        w     = Map.empty


tscdOfLfp :: DynGraph gr => gr a b -> Map Node (Set Node)
tscdOfLfp graph = Map.fromList [ (n, Set.fromList [ m | timdom <- timdoms,  (m, steps) <- Set.toList timdom, (∃) timdoms (\timdom' -> not $ (m, steps) ∈ timdom') ]) |
                    n <- nodes graph,
                    let timdoms = [ timdom ! x | x <- suc graph n]
                  ]
  where timdom = timdomOfLfp graph

tscdOfNaiveCostfLfp :: DynGraph gr => gr a b -> (Node -> Node -> Integer) -> Map Node (Set Node)
tscdOfNaiveCostfLfp graph cost = Map.fromList [ (n, Set.fromList [ m | timdom <- timdoms,  (m, steps) <- Set.toList timdom, (∃) timdoms (\timdom' -> not $ (m, steps) ∈ timdom') ]) |
                    n <- nodes graph,
                    let timdoms =  [ Set.fromList [ (m, steps + cost n x) | (m, steps) <- Set.toList $ timdom ! x ] | x <- suc graph n ]
                  ]
  where timdom = timdomOfNaiveCostLfp graph cost

fTimeDomNaiveCost :: DynGraph gr => gr a b -> (Node -> Node -> Integer) -> TimeDomFunctional
fTimeDomNaiveCost graph cost = f
  where f timeDomOf = -- traceShow timeDomOf $
                      Map.fromList [ (y, Map.fromList [(y, Set.fromList [0]    )]) | y <- nodes graph]
                    ⊔ Map.fromList [ (y,
                                         Map.delete y $ 
                                         (∏) [ fmap (Set.map (+ cost y x)) $ timeDomOf ! x | x <- suc graph y ]
                                     )
                                     | y <- nodes graph, suc graph y /= []
                                   ]
                
timdomOfNaiveCostLfp graph cost =
        fmap (\m -> Set.fromList [ (n, steps) | (n, ss) <- Map.assocs m, steps <- Set.toList ss ]) $
        (㎲⊒) init (fTimeDomNaiveCost graph cost)
  where init = Map.fromList [ (y, Map.empty) | y <- nodes graph]



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

timdomsOf graph = domsOf graph timdom
  where timdom = fmap (Set.map fst) $ timdomOfLfp graph

timdomsCostOf graph costF = domsOf graph timdom
  where timdom = fmap (Set.map fst) $ timdomOfNaiveCostLfp graph costF


timDF graph = dfFor graph timdom
  where timdom = fmap (Set.map fst) $ timdomOfLfp graph

timDFCost graph costF = dfFor graph timdom
  where timdom = fmap (Set.map fst) $ timdomOfNaiveCostLfp graph costF


timDFLocalDef graph = anyDFLocalDef timdom graph
  where timdom = fmap (Set.map fst) $ timdomOfLfp graph
        onedom = onedomOf timdom


timDFCostLocalDef graph costF = anyDFLocalDef timdom graph
  where timdom = fmap (Set.map fst) $ timdomOfNaiveCostLfp graph costF
        onedom = onedomOf timdom

timDFLocalViaTimdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timDFLocalViaTimdoms graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ timdoms ! y
                                      ]
                     )
                   | x <- nodes graph ]
  where timdoms = timdomsOf graph

timDFCostLocalViaTimdoms :: forall gr a b. DynGraph gr => gr a b -> (Node -> Node -> Integer) -> Map Node (Set Node)
timDFCostLocalViaTimdoms graph costF =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ timdoms ! y
                                      ]
                     )
                   | x <- nodes graph ]
  where timdoms = timdomsCostOf graph costF



timDFUpGivenXViaTimdoms :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
timDFUpGivenXViaTimdoms graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ timdf ! z,
                                                not $ x ∈ timdoms ! y
                                      ]
                     )
                   | z <- nodes graph,  x <- Set.toList $ timdoms ! z]
  where timdoms = timdomsOf graph
        timdf   = timDF graph


timDFCostUpGivenXViaTimdoms :: forall gr a b. DynGraph gr => gr a b -> (Node -> Node -> Integer) -> Map (Node, Node) (Set Node)
timDFCostUpGivenXViaTimdoms graph costF =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ timdf ! z,
                                                not $ x ∈ timdoms ! y
                                      ]
                     )
                   | z <- nodes graph,  x <- Set.toList $ timdoms ! z]
  where timdoms = timdomsCostOf graph costF
        timdf   = timDFCost graph costF

timDFUpGivenXViaTimdomsDef :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
timDFUpGivenXViaTimdomsDef graph = anyDFUpGivenXViaAnydomsDef timdom graph
  where timdom  = fmap (Set.map fst) $ timdomOfLfp graph

timDFCostUpGivenXViaTimdomsDef :: forall gr a b. DynGraph gr => gr a b -> (Node -> Node -> Integer) -> Map (Node, Node) (Set Node)
timDFCostUpGivenXViaTimdomsDef graph costF = anyDFUpGivenXViaAnydomsDef timdom graph
  where timdom  = fmap (Set.map fst) $ timdomOfNaiveCostLfp graph costF

timDFFromUpLocalDefViaTimdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timDFFromUpLocalDefViaTimdoms graph = anyDFFromUpLocalDefViaAnydoms timdom graph
  where timdom = fmap (Set.map fst) $ timdomOfLfp graph


timDFCostFromUpLocalDefViaTimdoms :: forall gr a b. DynGraph gr => gr a b -> (Node -> Node -> Integer) -> Map Node (Set Node)
timDFCostFromUpLocalDefViaTimdoms graph costF = anyDFFromUpLocalDefViaAnydoms timdom graph
  where timdom = fmap (Set.map fst) $ timdomOfNaiveCostLfp graph costF

timingLeaksTransformation :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) Integer -> Set Node -> (Map (Node, Node) Integer, Map Node (Set (Node, Integer)))
timingLeaksTransformation g0 cost0 ms  = f notmissing itimdomMultiple0 cost0
  where g = foldr (flip delSuccessorEdges) g0 ms
        notmissing = condNodes ∩ Set.fromList [ n | (n,ms) <- Map.assocs imdom, not $ Set.null ms ] ∩ ns
          where condNodes = Set.fromList [ n | n <- nodes g, let succs = suc g n, length succs > 1]
                imdom = imdomOfTwoFinger6 g

                ns = assert (s' == ntscdMyDodSliceViaNtscd g0        ms) $
                     assert (s0 == tscdCostSlice           g0 cost0F ms) $
                     assert (nsSimple == nsLimitedToTscdFrontiers) $
                     nsSimple
                  where nsSimple = s0 ∖ s'
                        nsLimitedToTscdFrontiers = Set.fromList [ n | n <- Set.toList $ s0  , not $ n ∈ s', not $ Set.null $ tscd ! n  ∩  s0]
                          where tscd = tscdOfNaiveCostfLfp g cost0F

        s' = ntscdSlice     g        ms
        s0 = tscdCostSlice  g cost0F ms

        itimdomMultiple0 = itimdomMultipleOfTwoFingerCost g cost0F

        cost0F n m = cost0 ! (n, m)

        f :: Set Node -> Map Node (Set (Node, Integer)) -> Map (Node, Node) Integer -> (Map (Node, Node) Integer, Map Node (Set (Node, Integer)))
        f ns itimdomMultiple cost
           | Set.null ns   = (cost, itimdomMultiple)
           | not succReach = -- traceShow (False, n, mz, ns, cost, itimdomMultiple) $
                             f ns0 itimdomMultiple  cost
           | otherwise     = -- traceShow (True,  n, (m, sm), mz, ns, cost, itimdomMultiple) $
                             f ns' itimdomMultiple' cost'

          where (n, ns0) = Set.deleteFindMin ns
                mz :: Maybe (Node, Integer, Map Node (Set Integer), Set Node, Map Node Integer)
                mz = let succs = nub $ suc g n 
                         nodeCost0 = Map.fromList [ (x, 0) | x <- succs ]
                     in foldM1 lca [ (x, cost ! (n,x), Map.fromList [(x, Set.fromList [cost ! (n,x)])], Set.fromList [x], nodeCost0) | x <- succs]
                lca = lcaTimdomOfTwoFingerFastCost itimdomM
                  where itimdomM = fmap (fromSet) itimdomMultiple

                Just (m, sm, _, _, nodeCost) = mz

                succReach = mz /= Nothing
                influenced = let imdomRev  = (invert'' $ fmap (Set.map fst) itimdomMultiple) in
                             let preds = reachableFrom imdomRev (Set.fromList [n])
                             in  notmissing ∩ (Set.fromList $ [ n0 | n0 <- foldMap prevCondsImmediate preds, n0 /= n])

                itimdomMultiple' = Map.insert n (Set.fromList [(m, sm)]) itimdomMultiple
                cost'            = Map.fromList [ ((n,x), cost ! (n,x) + nodeCostX) | (x, nodeCostX) <- Map.assocs nodeCost ] `Map.union` cost
                ns'
                 | Just (m, sm) /= (fromSet $ itimdomMultiple ! n) = ns0 ∪ influenced
                 | otherwise                                       = ns0

        prevCondsImmediate = prevCondImmediateNodes g


timingCorrection :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) Integer -> (Map (Node, Node) Integer, Map Node (Set (Node, Integer)))
timingCorrection g cost0 = f notmissing itimdomMultiple0 cost0
  where notmissing = condNodes ∩ Set.fromList [ n | (n,ms) <- Map.assocs imdom, not $ Set.null ms ]
          where condNodes = Set.fromList [ n | n <- nodes g, let succs = suc g n, length succs > 1]
                imdom = imdomOfTwoFinger6 g

        itimdomMultiple0 = itimdomMultipleOfTwoFingerCost g cost0F
          where cost0F n m = cost0 ! (n, m)

        f :: Set Node -> Map Node (Set (Node, Integer)) -> Map (Node, Node) Integer -> (Map (Node, Node) Integer, Map Node (Set (Node, Integer)))
        f ns itimdomMultiple cost
           | Set.null ns   = (cost, itimdomMultiple)
           | not succReach = -- traceShow (False, n, mz, ns, cost, itimdomMultiple) $
                             f ns0 itimdomMultiple  cost
           | otherwise     = -- traceShow (True,  n, (m, sm), mz, ns, cost, itimdomMultiple) $
                             f ns' itimdomMultiple' cost'

          where (n, ns0) = Set.deleteFindMin ns
                mz :: Maybe (Node, Integer, Map Node (Set Integer), Set Node, Map Node Integer)
                mz = let succs = nub $ suc g n 
                         nodeCost0 = Map.fromList [ (x, 0) | x <- succs ]
                     in foldM1 lca [ (x, cost ! (n,x), Map.fromList [(x, Set.fromList [cost ! (n,x)])], Set.fromList [x], nodeCost0) | x <- succs]
                lca = lcaTimdomOfTwoFingerFastCost itimdomM
                  where itimdomM = fmap (fromSet) itimdomMultiple

                Just (m, sm, _, _, nodeCost) = mz

                succReach = mz /= Nothing
                influenced = let imdomRev  = (invert'' $ fmap (Set.map fst) itimdomMultiple) in
                             let preds = reachableFrom imdomRev (Set.fromList [n])
                             in  notmissing ∩ (Set.fromList $ [ n0 | n0 <- foldMap prevCondsImmediate preds, n0 /= n])

                itimdomMultiple' = Map.insert n (Set.fromList [(m, sm)]) itimdomMultiple
                cost'            = Map.fromList [ ((n,x), cost ! (n,x) + nodeCostX) | (x, nodeCostX) <- Map.assocs nodeCost ] `Map.union` cost
                ns'
                 | Just (m, sm) /= (fromSet $ itimdomMultiple ! n) = ns0 ∪ influenced
                 | otherwise                                       = ns0

        prevCondsImmediate = prevCondImmediateNodes g

-- timingCorrection :: forall gr a b. DynGraph gr => gr a b -> (Map (Node, Node) Integer, Map Node (Set (Node, Integer)))
-- timingCorrection g = f notsame itimdomMultiple0 cost0

--   where notsame = Set.fromList [ n | (n,Just m) <- Map.assocs $ fmap fromSet imdom, let mMult = fromSet $ Set.map fst (itimdomMultiple0 ! n), mMult == Nothing ∨  (not $ mMult ∈ Map.findWithDefault (Set.fromList [Just m]) m (fmap (Set.map Just) cycleOf))]
--         notmissing  = condNodes ∩ Set.fromList [ n | (n,ms) <- Map.assocs imdom, not $ Set.null ms ]
--           where condNodes = Set.fromList [ n | n <- nodes g, let succs = suc g n, length succs > 1]
--         itimdomMultiple0 = itimdomMultipleOfTwoFinger g
--         cost0 = Map.fromList [ ((n,m), 1) | (n,m) <- edges g ]

--         f :: Set Node -> Map Node (Set (Node, Integer)) -> Map (Node, Node) Integer -> (Map (Node, Node) Integer, Map Node (Set (Node, Integer)))
--         f ns itimdomMultiple cost
--            | Set.null ns   = (cost, itimdomMultiple)
--            | not succReach = traceShow (False, n, m, ns, cost, itimdomMultiple) $
--                              f ns0 itimdomMultiple  cost
--            | otherwise     = traceShow (True,  n, m, ns, cost, itimdomMultiple) $
--                              f ns' itimdomMultiple' cost'

--           where (n, ns0) = Set.deleteFindMin ns
--                 Just m =
--                     id
--                   -- $ assert (      Set.null $ itimdomMultiple ! n)
--                   $ assert (not $ Set.null $ imdom ! n)
--                   $                fromSet $ imdom ! n
--                 succReach = (∀) (suc g n) (\x -> isReachableFromM itimdomM m x)
--                   where itimdomM = (fmap (fromSet . (Set.map fst)) itimdomMultiple)

--                 Just (mMultOld, maxCostOld) = fromSet $ itimdomMultiple ! n

--                 succosts = Map.fromList [ (x, costX) | x <- suc g n, let [path] = minimalPath itimdomMultiple x m, let costX = (sum $ fmap snd $ path) + cost ! (n,x) ]
--                 (maxX, maxCost) = maximumBy (comparing snd) $ Map.assocs succosts

--                 influenced = let imdomRev  = (invert'' $ fmap (Set.map fst) itimdomMultiple) in
--                              let preds = reachableFrom imdomRev (Set.fromList [n])
--                              in  notmissing ∩ (Set.fromList $ [ n0 | n0 <- foldMap prevCondsImmediate preds, n0 /= n {-, isNothing $ imdom ! n -}])

--                 itimdomMultiple' = Map.insert n (Set.fromList [(m, maxCost)]) itimdomMultiple
--                 cost'            = Map.fromList [ ((n,x), (maxCost - costX) + cost ! (n,x)) | (x, costX) <- Map.assocs succosts ] `Map.union` cost
--                 ns'
--                  | Set.null $ itimdomMultiple ! n                = ns0 ∪ influenced
--                  | maxCost < maxCostOld                          = ns0 ∪ influenced
--                  | otherwise                                     = ns0



--         prevCondsImmediate = prevCondImmediateNodes g
--         imdom = imdomOfTwoFinger6 g
--         (cycleOf, cycles) = findCyclesM $ fmap fromSet $ imdom
