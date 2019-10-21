{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Nticd where


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

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)


import Data.Graph.Inductive.Query.ControlDependence (controlDependenceGraphP, controlDependence)
import qualified Data.Graph.Inductive.Query.NTICD.Program as PROG (
    sinkDFF2GraphP, sinkDFGraphP, sinkDFFromUpLocalDefGraphP, sinkDFFromUpLocalGraphP,
       mDFF2GraphP,    mDFGraphP,    mDFFromUpLocalDefGraphP,    mDFFromUpLocalGraphP,
    nticdSinkContractionGraphP,
    nticdDefGraphP, ntscdDefGraphP,
    nticdF3GraphP, nticdF3'GraphP, nticdF3'dualGraphP,
    nticdF3WorkListGraphP,
    nticdF3WorkListSymbolicGraphP, nticdF3'dualWorkListSymbolicGraphP, nticdFig5GraphP, nticdF5GraphP,  nticdF3'dualWorkListGraphP,
    ntscdF4GraphP, ntscdF3GraphP, ntscdF4WorkListGraphP,
    ntacdDefGraphP,
  )
import qualified Data.Graph.Inductive.Query.NTICD.GraphTransformations as NTICD.TRANS (nticdSinkContraction)
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (nticdDef)
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, 
    nticdF3'dualWorkList, snmF3'dual,
    ntscdF4, ntscdF3, ntscdF4WorkList
  )

nticd      = defaultMain                               $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]
nticdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]



nticdProps = testGroup "(concerning nticd )" [
    testPropertySized 40  "nticdFig5GraphP               == nticdF5GraphP    for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdFig5GraphP p        == PROG.nticdF5GraphP p,
    testPropertySized 40  "nticdSinkContraction          == nticdF3GraphP   for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdSinkContractionGraphP p == PROG.nticdF3GraphP p,
    testPropertySized 40  "controlDependenceGraphp       == nticdF3GraphP   for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  controlDependenceGraphP p      == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3'GraphP                == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3'GraphP p         == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3'dualGraphP            == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3'dualGraphP p     == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3'dualWorkListGraphP       == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3'dualWorkListGraphP p  == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3WorkListGraphP         == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3WorkListGraphP p  == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3WorkListSymbolicGraphP == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3WorkListSymbolicGraphP p == PROG.nticdF3GraphP p,
    testProperty  "nticdFig5              == nticdF5                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                    in SNM.nticdFig5        g ==
                       SNM.nticdF5          g,
    testProperty  "controlDependence      == nticdF3                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in controlDependence      g exit ==
                       SNM.nticdF3          g,
    testProperty  "nticdSinkContraction   == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.TRANS.nticdSinkContraction  g ==
                       SNM.nticdF3               g,
    testProperty  "nticdDef               == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdDef         g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3'               == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'         g ==
                       SNM.nticdF3          g,
    testProperty  "snmF3'dual           == snmF3 (dual)"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        snmF3      = SNM.snmF3      g
                        snmF3'dual = SNM.snmF3'dual g
                    in (∀) (Map.assocs snmF3) (\((m,p), mp) ->
                         let mp' = snmF3'dual ! (m,p)
                         in  mp == Set.fromList [ (p,x) | x <- suc g p] ∖ mp'
                       ),
    testProperty  "nticdF3'dual           == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'dual     g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3'dualWorkList        == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'dualWorkList  g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3WorkList        == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3WorkList  g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3WorkListSymbolic== nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3WorkListSymbolic g ==
                       SNM.nticdF3                 g,
    testProperty  "nticdF3'dorkListSymbolic  == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'dualWorkListSymbolic g ==
                       SNM.nticdF3                      g
  ]
nticdTests = testGroup "(concerning nticd)" $
  [  testCase    ( "nticdFig5GraphP           ==       nticdF5GraphP for " ++ exampleName)
            $ PROG.nticdFig5GraphP p         == PROG.nticdF5GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdSinkContractionGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdSinkContractionGraphP p == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "controlDependenceGraphP   ==       nticdF3GraphP for " ++ exampleName)
                  $ controlDependenceGraphP p == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFF2GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFF2GraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdDefGraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdDefGraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3'GraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'dualGraphP        ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3'dualGraphP p      == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3WorkListGraphP     ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3WorkListGraphP p   == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3WorkListSymbolicGraphP     ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3WorkListSymbolicGraphP p   == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'dualWorkListSymbolicGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3'dualWorkListSymbolicGraphP p   == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []

