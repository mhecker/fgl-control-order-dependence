{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Delay where

import Debug.Trace (traceShow, trace)
import Control.Exception.Base (assert)
import Control.Monad.Random (randomR, getStdRandom)

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
import Data.Graph.Inductive.Arbitrary
import Data.Graph.Inductive.Query.TransClos (trc)

import Unicode
import Util(sampleFrom, invert'', moreSeeds, restrict)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation, removeDuplicateEdges)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (delayedInfinitely, sampleLoopPathsFor, isTracePrefixOf, sampleChoicesFor, Input(..), infinitelyDelays, runInput, observable, allChoices, isAscending, isLowEquivalentFor, isLowTimingEquivalent, isLowEquivalentTimed)
import qualified Data.Graph.Inductive.Query.Slices.OrderDependence as SLICE.ODEP (
    nticdNTIODFastSlice, wodTEILPDomSlice, 
    ntiodFastPDomSimpleHeuristicSlice, ntiodFastSlice, nticdNTIODSlice, wodTEILSlice, ntscdDodSlice, ntscdNTSODSlice, ntscdNTSODFastPDomSlice, 
    wccSliceViaNticdNTIODPDomSimpleHeuristic, nticdNTIODPDomSimpleHeuristic,
  )

delay     = defaultMain                               $ testGroup "delay"    [ mkTest [delayTests], mkProp [delayProps]]
delayX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "delay"    [ mkTest [delayTests], mkProp [delayProps]]

delayProps = testGroup "(concerning inifinte delay)" [
    testPropertySized 25 "ntscdNTSODFastPDomSlice  is sound"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        slicer     = SLICE.ODEP.ntscdNTSODFastPDomSlice g
                        ss         = Set.fromList [ slicer (Set.fromList [m1, m2]) | m1 <- nodes g, m2 <- nodes g ]
                        runInput   = InfiniteDelay.runInput         g
                    in (∀) ss (\s ->
                         let observable   = InfiniteDelay.observable s
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                     in (if not $ different then id else traceShow (s, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                         in not differentobservation
                    ),
    testPropertySized 25 "ntscdNTSODFastPDomSlice  is minimal"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        s = SLICE.ODEP.ntscdNTSODFastPDomSlice g (Set.fromList [m1, m2])
                        runInput         = InfiniteDelay.runInput g
                    in -- traceShow (length $ nodes g, Set.size s, Set.size $ condNodes) $
                       (∀) s (\n -> n == m1  ∨  n == m2  ∨
                         let s' = Set.delete n s
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                    in different
                                  )
                               ))
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            (if differentobservation then id else traceShow (m1, m2, n, differentobservation)) $
                            differentobservation
                       ),
    testPropertySized 25 "infinitelyDelays trace contains trace"
                $ \(ARBITRARY(generatedGraph)) seed seed' ->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        runInput = InfiniteDelay.runInput g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [nSamples] = fmap toInteger $ sampleFrom seed  1        [0.. 4 * (length $ nodes g)]
                        s          =   Set.fromList $ sampleFrom seed' nSamples (nodes g)
                        infinitelyDelays = InfiniteDelay.infinitelyDelays g s
                    in (∀) choices  (\choice ->  (∀) (nodes g) (\startNode -> 
                         let input = InfiniteDelay.Input startNode choice
                             trace    = runInput input
                             traceObs = InfiniteDelay.observable s trace
                             continuations = infinitelyDelays input
                         in    traceObs ∈ continuations
                            ∧ (∀) continuations ( \continuation -> traceObs `InfiniteDelay.isTracePrefixOf` continuation)
                       )),
    testPropertySized 25 "nticdNTIODFastSlice  is minimal"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        s = SLICE.ODEP.nticdNTIODFastSlice g (Set.fromList [m1, m2])
                        runInput         = InfiniteDelay.runInput g
                    in -- traceShow (length $ nodes g, Set.size s, Set.size $ condNodes) $
                       (∀) s (\n -> n == m1  ∨  n == m2  ∨
                         let s' = Set.delete n s
                             infinitelyDelays = InfiniteDelay.infinitelyDelays g s'
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentFor infinitelyDelays runInput observable input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                    in different
                                  )
                               ))
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            (if differentobservation then id else traceShow (m1, m2, n, differentobservation)) $
                            differentobservation
                       ),
    testPropertySized 25 "inifiniteDelays  is unique w.r.t nticdNTIODFastSlice"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                    let g = generatedGraph
                        n = toInteger $ length $ nodes g
                        startNodes =               sampleFrom       seed1 (n `div` 10 + 1) (nodes g)
                        choices    = InfiniteDelay.sampleChoicesFor seed2 (n `div`  2 + 1)        g
                        [m1,m2]    =               sampleFrom       seed3                2 (nodes g)
                        s = SLICE.ODEP.nticdNTIODFastSlice g (Set.fromList [m1, m2])
                        infinitelyDelays = InfiniteDelay.infinitelyDelays g s
                    in -- traceShow ("Graph: ", length $ nodes g) $
                       (∀) choices (\choice -> (∀) startNodes (\startNode  -> 
                         let input = InfiniteDelay.Input startNode choice
                             continuations = infinitelyDelays input
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            let result = InfiniteDelay.isAscending continuations
                            in (if result then id else traceShow (m1, m2, input, g, result)) $ result
                       ))
  ]
delayTests = testGroup "(concerning  inifinite delay)" $
  [  testCase    ( "ntscdNTSODFastPDomSlice  is minimal for " ++ exampleName) $
               let n = toInteger $ length $ nodes g
                   condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                   choices    = InfiniteDelay.allChoices g Map.empty condNodes
                   runInput   = InfiniteDelay.runInput         g
               in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                    let s = SLICE.ODEP.ntscdNTSODFastPDomSlice g (Set.fromList [m1, m2])
                    in -- traceShow (length $ nodes g, Set.size s, Set.size $ condNodes) $
                       (∀) s (\n -> n == m1  ∨  n == m2  ∨
                         let s' = Set.delete n s
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                    in different
                                  )
                               ))
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            (if differentobservation then id else traceShow (m1, m2, n, differentobservation)) $
                            differentobservation
                       )
                  )) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntscdNTSODFastPDomSlice  is sound for " ++ exampleName) $ 
               let n = toInteger $ length $ nodes g
                   condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                   choices    = InfiniteDelay.allChoices g Map.empty condNodes
                   runInput   = InfiniteDelay.runInput         g
               in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                    let s = SLICE.ODEP.ntscdNTSODFastPDomSlice g (Set.fromList [m1, m2])
                        observable       = InfiniteDelay.observable         s
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                     in (if not $ different then id else traceShow (m1,m2, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (if not $ differentobservation then id else traceShow (m1, m2, differentobservation)) $
                       not differentobservation
                  )) @? ""
  | (exampleName, g) <- interestingDodWod, exampleName /= "wodDodInteresting4"
  ] ++
  []

