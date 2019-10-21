{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Ntscd where


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


import Data.Graph.Inductive.Arbitrary.Reducible
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
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (ntscdDef, ntscdViaMDom)
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, 
    nticdF3'dualWorkList, snmF3'dual,
    ntscdF4, ntscdF3, ntscdF4WorkList
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (wodFast)

ntscd      = defaultMain                               $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]
ntscdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]


ntscdProps = testGroup "(concerning ntscd )" [
    testPropertySized 35 "wod ⊆ ntscd^* for reducible graphs"
                $ \(REDUCIBLE(g)) ->
                                let
                                     wod = ODEP.wodFast g
                                     ntscd = NTICD.ntscdViaMDom g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ),
    testPropertySized 4 "wod ⊆ ntscd^* for For-Programs, which by construction are reducible"
                $ \generated -> let  p :: Program Gr = toProgram generated
                                     g = tcfg p
                                     wod = ODEP.wodFast g
                                     ntscd = NTICD.ntscdViaMDom g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ),
    testProperty  "ntscdF4GraphP          == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.ntscdF4GraphP p         == PROG.ntscdF3GraphP p,
                
    testProperty  "ntscdF4WorkListGraphP  == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.ntscdF4WorkListGraphP p == PROG.ntscdF3GraphP p,
    testProperty  "ntscdF4WorkList == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       SNM.ntscdF4WorkList g ==
                       SNM.ntscdF3         g,
    testProperty  "ntscdF4         == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       SNM.ntscdF4         g ==
                       SNM.ntscdF3         g,
    testPropertySized 60  "ntscdDef        == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       NTICD.ntscdDef        g ==
                       SNM.ntscdF3         g
  ]

ntscdTests = testGroup "(concerning ntscd)" $
  [  testCase    ( "wod ⊆ ntscd^* for                                   " ++ exampleName)
            $                   let  g = tcfg p
                                     wod = ODEP.wodFast g
                                     ntscd = NTICD.ntscdViaMDom g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ) @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdF4GraphP            ==       ntscdF3GraphP for " ++ exampleName)
            $ PROG.ntscdF4GraphP p          == PROG.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdF4WorkListGraphP    ==       ntscdF3GraphP for " ++ exampleName)
            $ PROG.ntscdF4WorkListGraphP p  == PROG.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdDefGraphP           ==       ntscdF3GraphP for " ++ exampleName)
            $ PROG.ntscdDefGraphP p         == PROG.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []

