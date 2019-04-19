{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE CPP #-}
#define require assert
module Data.Graph.Inductive.Query.TSCD where

import Control.Exception.Base (assert)
import Control.Monad (liftM, liftM2)

import Data.List (nub)
import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd


import Data.Graph.Inductive
import Data.Graph.Inductive.Util (delSuccessorEdges, controlSinks, fromSuccMapWithEdgeAnnotation {-fromSuccMap, toSuccMap-})

import Unicode
import Util(reachableFrom, reachableUpToLength, distancesUpToLength, minimalPath, toSet, fromSet, foldM1, invert'', invert''', restrict, without, findCyclesM)
import IRLSOD(CFGNode)
import Program (Program)

import Data.Graph.Inductive.Query.LCA(lcaTimdomOfTwoFingerFast, lcaTimdomOfTwoFingerFastCost)
import Data.Graph.Inductive.Query.NTICD (prevCondImmediateNodes, combinedBackwardSlice, onedomOf, domsOf, dfFor, anyDFLocalDef, anyDFUpGivenXViaAnydomsDef, anyDFFromUpLocalDefViaAnydoms, imdomOfTwoFinger6, idomToDFFast, isinkDFTwoFinger, xDFcd, cdepGraph, cdepGraphP, ntscdF3, ntscdSlice, ntscdMyDodSliceViaNtscd, TimeDomFunctionalGen, TimeDomFunctional, tdomOfLfp, timdomMultipleOfNaiveLfp)
import Data.Graph.Inductive.Query.Dependence (Dependence)

tscdSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSlice graph =  combinedBackwardSlice graph tscd' w
  where tscd' = invert'' $ tscdOfLfp graph
        w     = Map.empty

tscdCostSlice :: (DynGraph gr) => gr a b ->  (Node -> Node -> Integer) -> Set Node -> Set Node
tscdCostSlice graph cost =  combinedBackwardSlice graph tscd' w
  where tscd' = invert'' $ tscdOfNaiveCostfLfp graph cost 
        w     = Map.empty


tscdSliceViaTimDF :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSliceViaTimDF graph msS = combinedBackwardSlice graph tscd' w msS
  where ms = Set.toList msS
        tscd' = timDFFromFromItimdomMultipleOfFast graph
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

itimdomMultipleOfTwoFingerFor :: forall gr a b. Graph gr => gr a b -> (Node -> Node -> Integer) -> Map Node [Node] -> Map Node [Node] -> Map Node (Maybe (Node, Integer)) -> Map Node (Set (Node)) -> Map Node (Maybe (Node, Integer))
itimdomMultipleOfTwoFingerFor graph cost condNodes worklist0 imdom0  imdom0Rev =
      require (condNodes  == Map.fromList [ (x, succs) | x <- nodes graph, let succs = suc graph x, length succs > 1 ])
    $ require (imdom0Rev  == (invert''' $ fmap noSteps $ imdom0))
    $ twoFinger 0 worklist0 imdom0 imdom0Rev
  where
        noSteps Nothing       = Nothing
        noSteps (Just (z, _)) = Just z
        toMap Nothing  = Map.empty
        toMap (Just (x, sx)) = Map.fromList [(x,sx)]

        prevCondsImmediate = prevCondImmediateNodes graph

        twoFinger :: Integer -> Map Node [Node] ->  Map Node (Maybe (Node, Integer)) -> Map Node (Set Node) -> Map Node (Maybe (Node, Integer))
        twoFinger i worklist imdom imdomRev
            | Map.null worklist = imdom
            | otherwise         =   assert (changed → (       zs /= Nothing)) $
                                    assert (changed → (imdom ! x == Nothing)) $
                                    -- assert (changed → ( case imdom ! x of { Nothing -> True ; Just (z0,k') -> ((z0,k') `elem` distancesUpToLength (fmap toSet $ imdom) k'  z)
                                    --                                                                          ∧ ((z,sz)  `elem` distancesUpToLength (fmap toSet $ imdom) sz  z0) ∧ False } )) $
                                    if (not $ changed) then twoFinger (i+1)                         worklist'                                   imdom                                           imdomRev
                                    else                    twoFinger (i+1) (influenced `Map.union` worklist')  (Map.insert x zs                imdom)  (Map.insertWith (∪) z (Set.singleton x) imdomRev)
          where ((x, succs), worklist')  = Map.deleteFindMin worklist
                mz :: Maybe (Node, Integer, Map Node (Set Integer))
                mz = require (succs == suc graph x) 
                   $ foldM1 lca [ (y, cost x y, Map.fromList [(y, Set.fromList [cost x y])]) | y <- succs]
                Just (z,sz) = zs
                zs = case mz of
                      Just (z,sz,_)  -> Just (z, sz)
                      Nothing ->  Nothing
                changed = zs /= (imdom ! x)
                influenced = assert (imdomRev  == (invert''' $ fmap (liftM fst) imdom)) $
                             let preds = reachableFrom imdomRev (Set.fromList [x])
                             in  restrict condNodes (Set.fromList $ [ n | n <- foldMap prevCondsImmediate preds, n /= x {-, isNothing $ imdom ! n -}])
                lca = lcaTimdomOfTwoFingerFast imdom

itimdomMultipleOfTwoFingerCost :: forall gr a b. Graph gr => gr a b -> (Node -> Node -> Integer) -> Map Node (Set (Node, Integer))
itimdomMultipleOfTwoFingerCost graph cost = fmap toSet $ itimdomMultipleOfTwoFingerFor graph cost condNodes worklist0 imdom0 (invert''' $ fmap (liftM fst) $ imdom0)
  where imdom0   =             Map.fromList [ (x, Just (z, cost x z)) | x <- nodes graph, [z] <- [suc graph x]]
                   `Map.union` Map.fromList [ (x, Nothing   ) | x <- nodes graph]
        condNodes   = Map.fromList [ (x, succs) | x <- nodes graph, let succs = suc graph x, length succs > 1 ]
        worklist0   = condNodes

itimdomMultipleOfTwoFinger :: forall gr a b. Graph gr => gr a b -> Map Node (Set (Node, Integer))
itimdomMultipleOfTwoFinger graph = itimdomMultipleOfTwoFingerCost graph (\_ _ -> 1)

timMultipleDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timMultipleDFTwoFinger graph = idomToDFFast graph $ fmap (Set.map fst) $ itimdomMultipleOfTwoFinger graph

itimdomMultipleTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
itimdomMultipleTwoFingerGraphP = cdepGraphP itimdomMultipleTwoFingerGraph

itimdomMultipleTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
itimdomMultipleTwoFingerGraph = cdepGraph itimdomMultipleTwoFingercd

itimdomMultipleTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
itimdomMultipleTwoFingercd = xDFcd timMultipleDFTwoFinger


tscdSliceFast :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSliceFast graph msS = combinedBackwardSlice graph tscd' w msS
  where ms = Set.toList msS
        toMs   = rdfs ms graph
        graph' = foldr (flip delSuccessorEdges) graph ms
        tscd' =  timMultipleDFTwoFinger graph'
        w     = Map.empty


tscdSliceForTrivialSinks :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
tscdSliceForTrivialSinks graph =  combinedBackwardSlice graph tscd' w
  where tscd' = -- require ((∀) sinks (\sink -> length sink == 1)) $
                timMultipleDFTwoFinger graph
        w     = Map.empty
        sinks = controlSinks graph

timdomsFromItimdomMultipleOfFor :: forall gr a b. DynGraph gr => gr a b -> (Node -> Node -> Integer) -> Map Node (Set (Node, Integer)) -> Map Node (Set Node)
timdomsFromItimdomMultipleOfFor g cost itimdom =
     require (itimdom == itimdomMultipleOfTwoFingerCost g cost) $
     assert ( Set.null $ Map.keysSet forOthers  ∩ Map.keysSet forEntries) $
     assert ( Set.null $ Map.keysSet forOthers  ∩ Map.keysSet forCycles) $
     assert ( Set.null $ Map.keysSet forEntries ∩ Map.keysSet forCycles) $
     forOthers
   ⊔ forEntries
   ⊔ forCycles
  where itimdomFst = fmap (Set.map fst) itimdom 
        valid = validTimdomFor g cost itimdom entries

        entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdom ! n) (\(m,_) -> m ∈ cycleNodes) ]

        (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdom
        cycleNodes = (∐) cycles

        forOthers  = Map.mapWithKey Set.delete $ without itimdomFst (entries ∪ cycleNodes)
        forEntries = Map.mapWithKey (\n fuel -> Set.delete n $ reachableUpToLength itimdom n fuel) valid
        -- forCycles  = Map.mapWithKey (\n n's -> if n's == Set.fromList [n] then Set.empty  else cycleOf ! n) $ restrict itimdomFst cycleNodes
        forCycles  = Map.fromSet (\n -> let cycle = cycleOf ! n in if cycle == Set.fromList [n] then Set.empty  else cycle) $ cycleNodes

timdomsFromItimdomMultipleOf :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timdomsFromItimdomMultipleOf g = timdomsFromItimdomMultipleOfFor g costF itimdom
  where itimdom    = itimdomMultipleOfTwoFinger g
        costF      = cost1F g


timDFFromFromItimdomMultipleOf :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timDFFromFromItimdomMultipleOf graph =
    assert (leafs == leafs') $
    f2 leafs Map.empty
  where leafs = Set.fromList [ n | n <- nodes graph, Map.findWithDefault Set.empty n timdoms' ⊆ timdoms ! n ]
        leafs' = assert (ls == Set.fromList [ n | n <- nodes graph, not $ (∃) (nodes graph) (\m -> n ∈ timdoms ! m)        ] ∩ nonCycleNodes) $
                 assert (ls == Set.fromList [ n | n <- nodes graph, Map.findWithDefault Set.empty n timdoms' ⊆ timdoms ! n ] ∩ nonCycleNodes) $ 
                 assert (rs == Set.fromList [ n | n <- nodes graph, Map.findWithDefault Set.empty n timdoms' ⊆ timdoms ! n ] ∩    cycleNodes) $ 
                 ls ∪ rs
          where ls =  nonCycleNodes ∖ (Map.keysSet timdoms')
                rs = (∐) [ cycle | cycle <- cycles, (∀) cycle (\n -> Map.findWithDefault Set.empty n timdoms' ⊆ cycle)  ]
                (cycleOf, cycles) = findCyclesM $ fmap fromSet $  itimdommultiple 
                  where itimdommultiple = fmap (Set.map fst) $ itimdomMultipleOfTwoFinger graph
                cycleNodes = (∐) cycles
                nonCycleNodes = (Set.fromList $ nodes graph) ∖ cycleNodes
        f2 xs df
           | Set.null xs   = df
           | changed ∨ new = f2 (timdoms ! x ∪ xs')  df'
           | otherwise     = f2                 xs'  df'
          where (x, xs') = Set.deleteFindMin xs
                df' = Map.insert x combined df
                combined = (local ∪ up) ∖ invalid
                local = Set.fromList [ y                | y <- pre graph x ]
                up    = Set.fromList [ y                | z <- Set.toList invalid,
                                                          z /= x,
                                                          y <- Set.toList $ Map.findWithDefault Set.empty z df,
                                                          (not $ z ∈ timdoms ! x) ∨ (∃) (suc graph y) (\y' -> x ∈ timdom ! y')
                        ]
                invalid = Map.findWithDefault Set.empty x timdoms'
                (dfX, new) = case Map.lookup x df of
                  Nothing  -> (Set.empty, True)
                  Just dfX -> (dfX,       False)
                changed = combined /= dfX
        timdoms  = timdomsFromItimdomMultipleOf graph
        timdoms' = invert'' timdoms

        timdom = fmap (Set.map fst) $ timdomOfTwoFinger graph


timDFFromFromItimdomMultipleOfFastComplicated :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timDFFromFromItimdomMultipleOfFastComplicated graph =
    fmap (Map.keysSet) $ f2 zs0 df0
  where df0 = Map.fromList [ (x, Map.fromList [ (y, Nothing) | y <- pre graph x, not $ x ∈ timdoms ! y]) | x <- nodes graph]
        zs0 = Map.keysSet $ Map.filter (not . Map.null) df0
        f2 :: Set Node -> Map Node (Map Node (Maybe Integer)) ->  Map Node (Map Node (Maybe Integer))
        f2 zs df
           | Set.null zs   = df
           | otherwise     = -- traceShow (z, zs, df) $
                             f2 zs' df'
          where (z, zs0) = Set.deleteFindMin zs
                dfZ = df ! z
                xsWithSteps = case Map.lookup z valid  of
                                Just fuel -> distancesUpToLength itimdomMultiple fuel z
                                Nothing   -> Set.toList $ itimdomMultiple ! z
                xs = [ (x,
                        dfx,
                        dfx'
                       )
                     | (x, steps) <- xsWithSteps,
                       let dfx  = df ! x,
                       let dfx' = foldr (\(y, fuel) dfx -> Map.insertWith mmax y fuel dfx)
                                        dfx
                                        [ (y, fuel') | (y, fuel0) <- Map.assocs dfZ, not $ x ∈ timdoms ! y,
                                                       let fuel  = case Map.lookup z valid  of
                                                                     Just fuel -> Just fuel
                                                                     Nothing   -> fuel0,
                                                       let fuel' =  liftM (subtract steps) fuel,
                                                       -- (if z == (-2)  ∧  x == (-4) then traceShow (z,steps,x, fuel0, fuel, fuel') else id) True,
                                                       case fuel' of { Nothing -> True ; Just fuel' -> fuel' >= 0 } ]
                     ]
                  where mmax :: Maybe Integer -> Maybe Integer -> Maybe Integer
                        mmax = liftM2 max
                df'     = Map.fromList [ (x, dfx') | (x,   _, dfx') <- xs              ] `Map.union` df
                zs'     = Set.fromList [  x        | (x, dfx, dfx') <- xs, dfx /= dfx' ] ∪ zs0

        timdoms  = timdomsFromItimdomMultipleOf graph
        itimdomMultiple = itimdomMultipleOfTwoFinger graph
        
        -- itimdomFst = fmap (Set.map fst) itimdom 
        valid = validTimdomFor graph (cost1F graph) itimdomMultiple entries

        entries = Set.fromList [ n | n <- nodes graph, not $ n ∈ cycleNodes, (∃) (itimdomMultiple ! n) (\(m,_) -> m ∈ cycleNodes) ]

        (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdomMultiple
        cycleNodes = (∐) cycles




timDFFromFromItimdomMultipleOfFastCost :: forall gr a b. DynGraph gr => gr a b -> (Node -> Node -> Integer) -> Map Node (Set Node)
timDFFromFromItimdomMultipleOfFastCost graph cost =
    fmap (Map.keysSet) $ f2 zs0 df0
  where df0 = df01 ⊔ df02
        df01 = Map.fromList [ (x, Map.fromList [ (y, True) | y <- pre graph x,                not $ x ∈ timdoms ! y]) | x <- nodes graph]
        df02 = (∐) [ Map.fromList [ (x, Map.fromList [(y, False) ]) ]
                   | cycle <- cycles, Set.size cycle > 1,
                     let entries = Set.toList $ entriesOf ! (Set.findMin cycle),
                     y <- entries,
                     x <- Set.toList $ cycle ∖ (timdoms ! y),
                     (∃) (suc graph y) (\y' -> y' ∈ cycle  ∨  x ∈ timdomFromOutside y')]
            -- ⊔ Map.fromList [ (x, Map.fromList [ (y, False) | y <- Set.toList $ entriesOf ! x, not $ x ∈ timdoms ! y, (∃) (suc graph y) (\y' -> y' ∈ cycle  ∨  x ∈ timdomFromOutside y')]) | (x, cycle) <- Map.assocs cycleOf, Set.size cycle > 1 ]
        zs0 = Map.fromList [ (prio ! x, x) | x <- Map.keys $ Map.filter (not . Map.null) df01 ]

        f2 :: Map Integer Node -> Map Node (Map Node Bool) ->  Map Node (Map Node Bool)
        f2 zs df
           | Map.null zs   = df
           | otherwise     = f2 zs' df'
          where ((_,z), zs0) = Map.deleteFindMin zs
                dfZ = df ! z
                transitive = not $ z ∈ entries
                xs = [ (x, dfx, dfx') | x <- Set.toList $ timdoms ! z,
                                        let dfx  = df ! x,
                                        let dfx' = foldr (\y dfx -> Map.insertWith (∨) y transitive dfx)
                                                   dfx
                                                   [ y | (y, True) <- Map.assocs dfZ, not $ x ∈ timdoms ! y ]
                     ]
                df'     = Map.fromList [ (x, dfx')     | (x,   _, dfx') <- xs              ] `Map.union` df
                zs'     = Map.fromList [ (prio ! x, x) | (x, dfx, dfx') <- xs, dfx /= dfx' ] `Map.union` zs0


        itimdomMultiple = itimdomMultipleOfTwoFingerCost graph cost
        timdoms  = timdomsFromItimdomMultipleOfFor graph cost itimdomMultiple
        timdomFromOutside n = (∐) [ timdoms ! n' | n' <- Set.toList outside  ]
          where outside = reachableFrom itimdomMultipleNoCrossings (Set.singleton n)
        itimdomMultipleNoCrossings = fmap (∖ cycleNodes) $ fmap (Set.map fst) $ itimdomMultiple

        entries = Set.fromList [ n | n <- nodes graph, not $ n ∈ cycleNodes, (∃) (itimdomMultiple ! n) (\(m,_) -> m ∈ cycleNodes) ]
        entriesOf = Map.fromList [ (m, entries) | cycle <- cycles,
                                                  let entries = Set.fromList [ n | n <- nodes graph, not $ n ∈ cycleNodes, (∃) (itimdomMultiple ! n) (\(m,_) -> m ∈ cycle )],
                                                  m <- Set.toList cycle
                    ]
        (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdomMultiple
        cycleNodes = (∐) cycles

        prio = Map.fromList $ zip sorting [0..]
          where sorting = reverse $ rdfs (Set.toList cycleNodes ++ [ n | (n, ms) <- Map.assocs itimdomMultiple, Set.null ms]) (fromSuccMapWithEdgeAnnotation itimdomMultiple :: gr () Integer)
             -- sorting = topsort (fromSuccMapWithEdgeAnnotation itimdomMultiple :: gr () Integer)
             -- sorting = nodes graph

timDFFromFromItimdomMultipleOfFast :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
timDFFromFromItimdomMultipleOfFast graph =
    fmap (Map.keysSet) $ f2 zs0 df0
  where df0 = Map.fromList [ (x, Map.fromList [ (y, True) | y <- pre graph x, not $ x ∈ timdoms ! y]) | x <- nodes graph]
        zs0 = Map.fromList [ (prio ! x, x) | x <- Map.keys $ Map.filter (not . Map.null) df0 ]

        f2 :: Map Integer Node -> Map Node (Map Node Bool) ->  Map Node (Map Node Bool)
        f2 zs df
           | Map.null zs   = df
           | otherwise     = f2 zs' df'
          where ((_,z), zs0) = Map.deleteFindMin zs
                dfZ = df ! z
                transitive = not $ z ∈ entries
                xs = [ (x, dfx, dfx') | x <- Set.toList $ timdoms ! z,
                                        let dfx  = df ! x,
                                        let dfx' = foldr (\y dfx -> Map.insertWith (∨) y transitive dfx)
                                                   dfx
                                                   [ y | (y, True) <- Map.assocs dfZ, not $ x ∈ timdoms ! y ]
                     ]
                df'     = Map.fromList [ (x, dfx')     | (x,   _, dfx') <- xs              ] `Map.union` df
                zs'     = Map.fromList [ (prio ! x, x) | (x, dfx, dfx') <- xs, dfx /= dfx' ] `Map.union` zs0


        itimdomMultiple = itimdomMultipleOfTwoFinger graph
        timdoms  = timdomsFromItimdomMultipleOfFor graph costF itimdomMultiple
          where cost  = cost1 graph
                costF n m = cost ! (n,m)
        
        entries = Set.fromList [ n | n <- nodes graph, not $ n ∈ cycleNodes, (∃) (itimdomMultiple ! n) (\(m,_) -> m ∈ cycleNodes) ]
        (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdomMultiple
        cycleNodes = (∐) cycles

        prio = Map.fromList $ zip sorting [0..]
          where sorting = reverse $ rdfs (Set.toList cycleNodes ++ [ n | (n, ms) <- Map.assocs itimdomMultiple, Set.null ms]) (fromSuccMapWithEdgeAnnotation itimdomMultiple :: gr () Integer)
             -- sorting = topsort (fromSuccMapWithEdgeAnnotation itimdomMultiple :: gr () Integer)
             -- sorting = nodes graph


timdomOfTwoFinger :: Graph gr => gr a b -> Map Node (Set (Node, Integer))
timdomOfTwoFinger g = timdomFrom
  where itimdommultiple = itimdomMultipleOfTwoFinger g
        timdomFrom =  Map.fromList [ (n, Set.fromList [ (m, steps) | m <- nodes g, path <- minimalPath itimdommultiple n m, let steps = sum $ fmap snd path,
                                                                     (∀) (scanl (\(x, steps0) (x',steps) -> (x', steps0 + steps)) (n,0)  path) (\(x',stepsX') ->
                                                                       (not $ x' ∈ entries) ∨ (steps - stepsX' <= (valid ! x'))
                                                                     )
                                         ]) | n <- nodes g ]
        valid = validTimdomFor g (cost1F g) itimdommultiple entries
        entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdommultiple ! n) (\(m,_) -> m ∈ cycleNodes) ]
          where (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdommultiple
                cycleNodes = (∐) cycles


validTimdomLfp :: DynGraph gr => gr a b -> Map Node Integer
validTimdomLfp g = fmap (\(MyInteger n) -> n) $ valid
  where timdommultiple = fmap (Set.map (\(m, steps) -> (m, MyInteger steps))) $ timdomMultipleOfNaiveLfp g
        valid = (㎲⊒) (Map.fromList [ (n, MyInteger 0) | n <- nodes g ]) f 
          where f valid = assert (valid ⊑ valid') valid'
                  where valid' =
                           Map.fromList [ (n, (∐) [fuel' + steps | (m, fuel') <- [ (m, fuel') | (m,fuel') <- Set.toList $ Set.filter (( <= fuel) . snd) $ timdommultiple ! n],
                                                                  (m', steps) <- Set.toList $ timdommultiple ! m,
                                                                  (∀) (Set.filter ((==m') . fst) $ timdommultiple ! m) (\(_,stepss) -> steps <= stepss),
                                                                  m' /= n,
                                                                  let xs = Set.fromList $ suc g n,
                                                                  (∀) xs (\x ->
                                                                     ((m', steps + fuel' - 1) ∈ timdommultiple ! x)
                                                                   ∧ (     steps + fuel' - 1 <= valid ! x)
                                                                  )
                                                                  -- (∀) xs (\x ->
                                                                  --     (∃) (Set.filter ((==m') . fst) $ timdommultiple ! x) (\(_, steps') ->
                                                                  --         (1 + steps' == steps + fuel')
                                                                  --       ∧ (steps' <= valid ! x)
                                                                  --     )
                                                                  -- )
                                             ]
                                         )
                                       | (n,fuel) <- Map.assocs valid]


validTimdomFor :: Graph gr => gr a b -> (Node -> Node -> Integer) -> Map Node (Set.Set (Node, Integer)) -> Set Node -> Map Node Integer
validTimdomFor g cost itimdommultiple relevantNodes =
     require (itimdommultiple == itimdomMultipleOfTwoFingerCost g cost) $
     validFast
  where validFast  = fmap (toInteger.snd) $ fix (Map.fromSet (\n -> (n,0)) relevantNodes ) f
          where fix x f = let x' = f x in if x == x' then x else fix x' f
                f valid = Map.fromList [ (n, (m',fuel + steps)) | (n,(m,fuel)) <- Map.assocs valid,
                                                           assert (Set.size (itimdommultiple ! m) <= 1) True,
                                                                  (m', steps) <- Set.toList $ itimdommultiple ! m,
                                                                  m' /= n,
                                                                  let xs = Set.fromList $ suc g n,
                                                                  (∀) xs (\x ->
                                                                      (not $ List.null $ minimalPath itimdommultiple x m')
                                                                    ∧ (let [path'] = minimalPath itimdommultiple x m'
                                                                           steps' =  sum $ fmap snd path'
                                                                           in   (cost n x) + steps' == steps + fuel
                                                                              ∧ (∀) (scanl (\(x, steps0) (x',steps) -> (x', steps0 + steps)) (x,0)  path') (\(x',stepsX') ->
                                                                                  (not $ x' ∈ relevantNodes ) ∨ (steps' - stepsX' <= (snd $ valid ! x'))
                                                                                )
                                                                      )
                                                                  )
                                       ] `Map.union` valid


timingDependenceViaTwoFinger g =
      invert'' $
      Map.fromList [ (m, Set.fromList [ n | (n, Nothing) <- Map.assocs itimdom ])         | m <- nodes g,
                                                                                            let toM  = reachable m gRev,
                                                                                            let toMS = Set.fromList toM,
                                                                                            let (condNodes', noLongerCondNodes) = Map.partition isCond $ fmap (List.filter (∈ toMS)) $ Map.delete m  $ restrict condNodes toMS,
                                                                                            let usingMS = reachableFrom (fmap toSet itimdom) (Set.fromList [m]),
                                                                                            let imdom0' = id
                                                                                                  $ Map.insert m Nothing
                                                                                                  $ Map.union (Map.mapWithKey (\x [z] ->  assert (z /= x) $ Just (z,1)) noLongerCondNodes)
                                                                                                  $ Map.union (Map.mapMaybeWithKey (\x _ -> case itimdom ! x of { Just (z, _) -> if z ∈ usingMS then Just Nothing else Nothing ; _ -> Nothing }) condNodes')
                                                                                                  $ restrict itimdom toMS,
                                                                                            let g' = (flip delSuccessorEdges m) $ subgraph toM $ g,
                                                                                            let worklist0' = Map.filterWithKey (\x _ -> imdom0' ! x == Nothing) condNodes',
                                                                                            let itimdom = itimdomMultipleOfTwoFingerFor g' defaultCost condNodes' worklist0' imdom0' (invert''' $ fmap (liftM fst) $ imdom0'),
                                                                                        assert (itimdom == (fmap fromSet $ itimdomMultipleOfTwoFinger g')) True
                   ]
                                               
  where defaultCost = \_ _ -> 1
        gRev = grev g
        condNodes = Map.fromList [ (x, succs) | x <- nodes g, let succs = suc g x, length succs > 1 ]
        imdom0 =             Map.fromList [ (x, Just (z,1)) | x <- nodes g, [z] <- [suc g x]]
                 `Map.union` Map.fromList [ (x, Nothing   ) | x <- nodes g]
        itimdom = itimdomMultipleOfTwoFingerFor g defaultCost condNodes condNodes imdom0 (invert''' $ fmap (liftM fst) $ imdom0)

        toSet Nothing = Set.empty
        toSet (Just (z, steps)) = Set.singleton z
        isCond []  = False
        isCond [_] = False
        isCond _   = True


nticdTimingSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdTimingSlice graph =  combinedBackwardSlice graph (nticd' ⊔ timing') w
  where nticd'  = isinkDFTwoFinger graph
        timing' = invert'' $ timingDependenceViaTwoFinger graph
        w     = Map.empty


ntscdTimingSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdTimingSlice graph =  combinedBackwardSlice graph (ntscd' ⊔ timing') w
  where ntscd'  = invert'' $ ntscdF3 graph
        timing' = invert'' $ timingDependenceViaTwoFinger graph
        w     = Map.empty


newtype MyInteger = MyInteger Integer deriving (Show, Eq, Ord, Num, Enum, Real, Integral)
instance JoinSemiLattice MyInteger where
  join = max

instance BoundedJoinSemiLattice MyInteger where
  bottom = 0


cost1 g =  Map.fromList [ ((n,m), 1) | (n,m) <- edges g ]
cost1F g = costF
  where cost = cost1 g
        costF n m = cost ! (n,m)
