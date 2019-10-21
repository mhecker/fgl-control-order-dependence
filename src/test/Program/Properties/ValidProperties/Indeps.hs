{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Indeps where


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

import Program.Examples (testsuite, interproceduralTestSuit, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)

import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.DataDependence (dataDependenceGraphP, dataDependenceGraphViaIndependenceP, withParameterNodes, dataDependence)
import Data.Graph.Inductive.Query.ProgramDependence (programDependenceGraphP, addSummaryEdges, addSummaryEdgesLfp, addSummaryEdgesGfpLfp, addSummaryEdgesGfpLfpWorkList, summaryIndepsPropertyViolations, implicitSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdges, addImplicitAndTrivialSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdgesGfpLfp)


indeps     = defaultMain                               $ testGroup "indeps"    [ mkTest [indepsTests], mkProp [indepsProps]]
indepsX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "indeps"    [ mkTest [indepsTests], mkProp [indepsProps]]



indepsProps = testGroup "(concerning dependencey graph representations using independencies)" [
    testPropertySized 25 "addNonImplicitNonTrivialSummaryEdgesGfpLfp  =~   addNonImplicitNonTrivialSummaryEdges"
                $ \generated ->
                  let p :: Program Gr = toProgram generated
                      (_, parameterMaps) = withParameterNodes p
                      pdg = programDependenceGraphP p
                      (nonImplicitNonTrivialSdg , summaryIndependencies , formalInActualInIndependencies , actualOutFormalOutIndependencies ) = addNonImplicitNonTrivialSummaryEdges       p parameterMaps pdg
                      (nonImplicitNonTrivialSdg', summaryIndependencies', formalInActualInIndependencies', actualOutFormalOutIndependencies') = addNonImplicitNonTrivialSummaryEdgesGfpLfp p parameterMaps pdg

                      sdg  = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps  summaryIndependencies  formalInActualInIndependencies  actualOutFormalOutIndependencies  nonImplicitNonTrivialSdg 
                      sdg' = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps  summaryIndependencies' formalInActualInIndependencies' actualOutFormalOutIndependencies' nonImplicitNonTrivialSdg'
                      
                      baseSummaries  = Set.fromList [ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSdg ]
                      baseSummaries' = Set.fromList [ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSdg']
                    in   baseSummaries                    ⊇                     baseSummaries'
                       ∧                              sdg ==                              sdg'
                       ∧            summaryIndependencies ==            summaryIndependencies'
                       ∧   formalInActualInIndependencies ==   formalInActualInIndependencies'
                       ∧ actualOutFormalOutIndependencies == actualOutFormalOutIndependencies',
    testPropertySized 50 "nonImplicitSummaryComputation is correct"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        pdg = programDependenceGraphP p
                        (cfg, parameterMaps) = withParameterNodes p
                        sdg                     = addSummaryEdges              parameterMaps pdg
                        (nonImplicitNonTrivialSummariesSdg, summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)  = addNonImplicitNonTrivialSummaryEdges p parameterMaps pdg
                        sdg'                    = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps summaryIndependencies formalInActualInInIndependencies actualOutFormalOutIndependencies nonImplicitNonTrivialSummariesSdg
                        summaries                       = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges sdg                              ]
                        summariesNonImplicitNonTrivial  = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSummariesSdg]
                    in -- traceShow ("SummaryGraph: ", Set.size summaries, "\t\t", "NonImplicitSummaryGraph: ", Set.size summariesNonImplicitNonTrivial) $
                       sdg == sdg',
    -- testProperty "implicitSummaryEdgesLfp are valid"
    --             $ \generated ->
    --                 let p   :: Program Gr = toProgram generated
    --                     pdg = programDependenceGraphP p
    --                     (cfg, parameterMaps) = withParameterNodes p
    --                     sdg = addSummaryEdges  parameterMaps pdg
    --                     implicitSummaries = implicitSummaryEdgesLfp p parameterMaps sdg 
    --                     allSummaries = Set.fromList [ (actualIn, actualOut)  | (actualIn, actualOut, SummaryDependence) <-  labEdges sdg]
    --                 in traceShow ("Implicit Summary Edges:", Set.size implicitSummaries, " of ", Set.size allSummaries) $
    --                    implicitSummaries ⊆ allSummaries,
    testPropertySized 50 "summaryIndepsProperty"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                    in summaryIndepsPropertyViolations p == [],
    testPropertySized 50 "summaryComputation                      =~  summaryComputationGfpLfpWorkList"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        (cfg, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                        sdg               = addSummaryEdges                 parameterMaps pdg
                        sdgGfpLfpWorkList = addSummaryEdgesGfpLfpWorkList p parameterMaps pdg
                    in -- traceShow (length $ nodes $ tcfg p, length $ nodes cfg, length $ [ () | (_,_,SummaryDependence) <- labEdges sdg]) $
                                                      sdg == sdgGfpLfpWorkList,
    testPropertySized 50 "summaryComputation                      =~  summaryComputationGfpLfp"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        (_, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                    in addSummaryEdges parameterMaps pdg  == addSummaryEdgesGfpLfp p parameterMaps pdg,
    testPropertySized 50 "summaryComputation                      =~  summaryComputationLfp"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        (_, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                    in addSummaryEdges parameterMaps pdg  == addSummaryEdgesLfp parameterMaps pdg,
    testPropertySized 50 "dataDependenceGraphViaIndependenceP     == dataDependenceGraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  dataDependenceGraphViaIndependenceP p   == dataDependenceGraphP p
  ]
indepsTests = testGroup "(concerning dependencey graph representations using independencies)" $
  [  testCase  ( "addNonImplicitNonTrivialSummaryEdgesGfpLfp  =~   addNonImplicitNonTrivialSummaryEdges for " ++ exampleName)
                $ let (_, parameterMaps) = withParameterNodes p
                      pdg = programDependenceGraphP p
                      (nonImplicitNonTrivialSdg , summaryIndependencies , formalInActualInIndependencies , actualOutFormalOutIndependencies ) = addNonImplicitNonTrivialSummaryEdges       p parameterMaps pdg
                      (nonImplicitNonTrivialSdg', summaryIndependencies', formalInActualInIndependencies', actualOutFormalOutIndependencies') = addNonImplicitNonTrivialSummaryEdgesGfpLfp p parameterMaps pdg

                      sdg  = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps  summaryIndependencies  formalInActualInIndependencies  actualOutFormalOutIndependencies  nonImplicitNonTrivialSdg 
                      sdg' = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps  summaryIndependencies' formalInActualInIndependencies' actualOutFormalOutIndependencies' nonImplicitNonTrivialSdg'
                      
                      baseSummaries  = Set.fromList [ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSdg ]
                      baseSummaries' = Set.fromList [ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSdg']
                    in                      baseSummaries ⊇                    baseSummaries'
                       ∧                              sdg ==                              sdg'
                       ∧            summaryIndependencies ==            summaryIndependencies'
                       ∧   formalInActualInIndependencies ==   formalInActualInIndependencies'
                       ∧ actualOutFormalOutIndependencies == actualOutFormalOutIndependencies'
                       @? ""
  | (exampleName, p) <- testsuite ++ interproceduralTestSuit
  ] ++
  [  testCase  ( "nonImplicitSummaryComputation is correct  for " ++ exampleName)
                $   let pdg = programDependenceGraphP p
                        (cfg, parameterMaps)   = withParameterNodes p
                        sdg                     = addSummaryEdges              parameterMaps pdg
                        (nonImplicitNonTrivialSummariesSdg, summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)  = addNonImplicitNonTrivialSummaryEdges p parameterMaps pdg
                        sdg'                    = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps summaryIndependencies formalInActualInInIndependencies actualOutFormalOutIndependencies  nonImplicitNonTrivialSummariesSdg
                        summaries                      = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges sdg                              ]
                        summariesNonImplicitNonTrivial = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSummariesSdg]
                    in sdg == sdg'  @? ""
  | (exampleName, p) <- testsuite ++ interproceduralTestSuit
  ] ++
  [  testCase  ( "summaryComputation                      =~  summaryComputationGfpLfpWorkList for " ++ exampleName)
                $   let (_, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                    in addSummaryEdges parameterMaps pdg  == addSummaryEdgesGfpLfpWorkList p parameterMaps pdg @? ""
  | (exampleName, p) <- testsuite ++ interproceduralTestSuit
  ] ++
  [  testCase  ( "summaryComputation                      =~  summaryComputationGfpLfp for " ++ exampleName)
                $   let (_, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                    in addSummaryEdges parameterMaps pdg  == addSummaryEdgesGfpLfp p parameterMaps pdg @? ""
  | (exampleName, p) <- testsuite ++ interproceduralTestSuit
  ] ++
  [  testCase  ( "summaryComputation                      =~  summaryComputationLfp for " ++ exampleName)
                $   let (_, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                    in addSummaryEdges parameterMaps pdg  == addSummaryEdgesLfp parameterMaps pdg @? ""
  | (exampleName, p) <- testsuite ++ interproceduralTestSuit
  ] ++
  [  testCase  ( "dataDependenceGraphViaIndependenceP     == dataDependenceGraphP for " ++ exampleName)
                $ dataDependenceGraphViaIndependenceP p   == dataDependenceGraphP p @? ""
  | (exampleName, p) <- testsuite ++ interproceduralTestSuit
  ] ++
  []
