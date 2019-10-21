{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Cache where

import Debug.Trace (traceShow, trace)
import Control.Exception.Base (assert)

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map, (!))

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Runners.AntXML

import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, lsuc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph, delEdges, insEdge, newNodes)
import Data.Graph.Inductive.PatriciaTree (Gr)

import Unicode
import Util(sampleFrom, invert'', moreSeeds)

import Program.Properties.Util
import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import IRLSOD(CFGEdge(..), Var(..), Name(..), isGlobalName, globalEmpty, use, def)
import CacheExecution(twoAddressCode, prependInitialization, prependFakeInitialization, initialCacheState, cacheExecution, cacheExecutionLimit, csd''''Of3, csd''''Of4, csdMergeOf, csdMergeDirectOf, cacheCostDecisionGraph, cacheCostDecisionGraphFor, cacheStateGraph, stateSets, cacheOnlyStepFor, costsFor)
import CacheSlice (cacheTimingSliceViaReach)

cache     = defaultMain                               $ testGroup "cache"    [                      mkProp [cacheProps]]
cacheX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "cache"    [                      mkProp [cacheProps]]


cacheProps = testGroup "(concerning cache timing)" [
    testPropertySized 25 "csd only for choice nodes"
                $ \generated ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b'
                          where (a,b) = toCodeSimple generated
                                b' = fmap twoAddressCode b
                        g = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        csdM       = csdMergeDirectOf g n0
                        
                        (cs, es)    = stateSets cacheOnlyStepFor g initialCacheState n0
                        
                        csGraph     = cacheStateGraph g initialCacheState n0
                        costs       = costsFor csGraph
                        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes g]

                        (ccg, cost) = cacheCostDecisionGraphFor g csGraph 
                    in  (∀) (Map.assocs $ invert'' csdM) (\(m, ns) -> 
                          let
                              c = (∃) (lsuc ccg m) (\(n1,l1) ->
                                  (∃) (lsuc ccg m) (\(n2,l2) ->
                                    (l1 == l2) ∧ (not $ n1  == n2              )))
                              d = (∃) (lsuc g m) (\(n,l) -> Set.size (costs ! (m,n,l)) > 1)
                         in let
                                ok3 = (c == d)
                                okc = ((not $ Set.null $ ns) → c)
                                okd = ((not $ Set.null $ ns) → d)
                                ok = ok3 ∧ okc ∧ okd
                            in  if ok then ok else traceShow (ok3, "....", okc, okd) ok
                        ),
    testPropertySized 25 "csd''''Of3 == csd''''Of4"
                $ \generated ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b'
                          where (a,b) = toCodeSimple generated
                                b' = fmap twoAddressCode b
                        g = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        csd'3 = csd''''Of3 g n0
                        csd'4 = csd''''Of4 g n0
                    in  csd'3 == csd'4,
    testPropertySized 25 "csdMergeOf == csdMergeDirectOf"
                $ \generated ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b'
                          where (a,b) = toCodeSimple generated
                                b' = fmap twoAddressCode b
                        g = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        csdM       = csdMergeOf g n0
                        csdMDirect = csdMergeDirectOf g n0
                    in  csdM == csdMDirect,
    testPropertySized 25 "csdMergeOf ⊑ csd''''Of4"
                $ \generated ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b'
                          where (a,b) = toCodeSimple generated
                                b' = fmap twoAddressCode b
                        g = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        csdM  = csdMergeOf g n0
                        csd'4 = csd''''Of4 g n0
                    in  csdM ⊑ csd'4,
    testPropertySized 25 "csd is sound"
                $ \generated seed1 seed2 seed3 seed4 ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b'
                          where (a,b) = toCodeSimpleWithArrays generated
                                b' = fmap twoAddressCode b
                        g0 = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        
                        vars  = Set.fromList [ var | n <- nodes g0, name@(VarName   var) <- Set.toList $ use g0 n ∪ def g0 n, isGlobalName name]
                        varsA = Set.fromList [ arr | n <- nodes g0, name@(ArrayName arr) <- Set.toList $ use g0 n ∪ def g0 n, isGlobalName name]
                        (newN0:new) = (newNodes ((Set.size vars) + (Set.size varsA) + 1) g0)
                        varToNode = Map.fromList $ zip ((fmap VarName $ Set.toList vars) ++ (fmap ArrayName $ Set.toList varsA)) new
                        nodeToVar = Map.fromList $ zip new ((fmap VarName $ Set.toList vars) ++ (fmap ArrayName $ Set.toList varsA))

                        g = prependFakeInitialization g0 n0 newN0 varToNode
                        slicer = cacheTimingSliceViaReach g newN0


                        initialFullState   = ((globalEmpty, Map.empty, ()), initialCacheState, 0)
                        prependActualInitialization = prependInitialization g0 n0 newN0 varToNode

                        initialGlobalState1  = Map.fromList $ zip (Set.toList vars ) (            fmap (`rem` 32)   $ moreSeeds seed1 (Set.size vars))
                        initialGlobalState1A = Map.fromList $ zip (Set.toList varsA) (      fmap (fmap (`rem` 32))  $ vals                           )
                          where aSeeds = moreSeeds seed4 (Set.size varsA)
                                vals = fmap (Map.fromList . zip [0..]) $ fmap (`moreSeeds` 256) aSeeds
                        g1 = prependActualInitialization initialGlobalState1 initialGlobalState1A


                        limit = 9000
                        (execution1, limited1) = assert (length es == 1) $ (head es, (length $ head es) >= limit)
                          where es = cacheExecutionLimit limit g1 initialFullState newN0

                        ms = [ nodes g0 !! (m `mod` (length $ nodes g0)) | m <- moreSeeds seed2 100]
                    in (∀) ms (\m ->
                         let s = slicer (Set.fromList [m])
                             notInS  = (Set.map ((varToNode !) . VarName  ) vars ) ∖ s
                             notInSA = (Set.map ((varToNode !) . ArrayName) varsA) ∖ s
                             initialGlobalState2  = (Map.fromList $ zip [ var | n <- Set.toList notInS,  let VarName   var = nodeToVar ! n] newValues) `Map.union` initialGlobalState1
                               where newValues =       fmap (`rem` 32)  $ moreSeeds (seed3 + m) (Set.size notInS)
                             initialGlobalState2A = (Map.fromList $ zip [ arr | n <- Set.toList notInSA, let ArrayName arr = nodeToVar ! n] newValues) `Map.union` initialGlobalState1A
                               where aSeeds = moreSeeds (seed4 + m) (Set.size notInSA)
                                     newValues = fmap (fmap (`rem` 32)) $ fmap (Map.fromList . zip [0..]) $ fmap (`moreSeeds` 256) aSeeds
                             g2 = prependActualInitialization initialGlobalState2 initialGlobalState2A

                             (execution2, limited2) = assert (length es == 1) $ (head es, (length $ head es) >= limit)
                               where es = cacheExecutionLimit limit g2 initialFullState newN0

                             exec1Obs = filter (\(n,_) -> n ∈ s) $ execution1
                             exec2Obs = filter (\(n,_) -> n ∈ s) $ execution2

                             ok = limited1 ∨ limited2 ∨ (exec1Obs == exec2Obs)
                          in if ok then ok else
                               traceShow ("M:: ", m, "  S::", s) $
                               traceShow ("G0 =====", g0) $
                               traceShow ("G  =====", g ) $
                               traceShow ("G1 =====", g1) $
                               traceShow ("G2 =====", g2) $
                               traceShow (execution1, "=========", execution2) $
                               traceShow (exec1Obs,   "=========", exec2Obs) $
                               traceShow (List.span (\(a,b) -> a == b) (zip exec1Obs exec2Obs)) $
                               ok
                        )
  ]
