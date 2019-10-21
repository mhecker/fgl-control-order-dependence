{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Giffhorn where


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

import Program.DynamicAnalysis (isSecureEmpirically, isLSODEmpirically)
import Program.Analysis

giffhorn   = defaultMain                               $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]
giffhornX  = defaultMainWithIngredients [antXMLRunner] $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]

giffhornProps = testGroup "(concerning Giffhorns LSOD)" [
    testPropertySized 20  "isSecureGiffhornClassification2 isAtLeastAsPreciceAs isSecureGiffhornClassification for procedure-less programs"
                $ \generated ->
                    let  p :: Program Gr = toProgramIntra generated
                         pc = precomputedUsing undefined p
                    in isSecureGiffhornClassificationUsing pc p ⊑ isSecureGiffhornClassification2Using pc p,
    testPropertySized 10  "isSecureGiffhornClassification2 isAtLeastAsPreciceAs isSecureGiffhornClassification"
                $ \generated ->
                    let  p :: Program Gr = toProgram      generated
                         pc = precomputedUsing undefined p
                    in isSecureGiffhornClassificationUsing pc p ⊑ isSecureGiffhornClassification2Using pc p,
    testPropertySized 25  "isSecureGiffhornClassification2 is sound for procedure-less programs"
                $ \generated ->
                    let  p :: Program Gr = toProgramIntra generated
                         pc = precomputedUsing undefined p
                    in isSecureGiffhornClassification2Using pc p ==>  isLSODEmpirically p,
    -- cannot use isLSODEmpirically, since such programs may contain nonterminating recursion
    testPropertySized 10  "isSecureGiffhornClassification2 isAtMostAsPreciceAs isSecureTimingClassificationAtUses"
                $ \generated ->
                    let  p :: Program Gr = toProgram      generated
                         pc = precomputedUsing undefined p
                    in isSecureGiffhornClassification2Using pc p ⊑ isSecureTimingClassificationAtUses p,
    testPropertySized 25  "isSecureGiffhornClassification is sound for procedure-less programs"
                $ \generated ->
                    let  p :: Program Gr = toProgramIntra generated
                         pc = precomputedUsing undefined p
                    in isSecureGiffhornClassificationUsing pc p ==>  isLSODEmpirically p,
    -- cannot use isLSODEmpirically, since such programs may contain nonterminating recursion
    testPropertySized 10  "isSecureGiffhornClassification  isAtMostAsPreciceAs isSecureTimingClassificationAtUses"
                $ \generated ->
                    let  p :: Program Gr = toProgram      generated
                         pc = precomputedUsing undefined p
                    in isSecureGiffhornClassificationUsing  pc p ⊑ isSecureTimingClassificationAtUses p,
    testPropertySized 25  "giffhornLSOD == isSecureGiffhornClassification for procedure-less programs"
                $ \generated ->
                    let  p :: Program Gr = toProgramIntra generated
                         pc = precomputedUsing undefined p
                    in giffhornLSODUsing pc p == isSecureGiffhornClassificationUsing pc p,
    testPropertySized 10  "giffhornLSOD == isSecureGiffhornClassification "
                $ \generated ->
                    let  p :: Program Gr = toProgram      generated
                         pc = precomputedUsing undefined p
                    in giffhornLSODUsing pc p == isSecureGiffhornClassificationUsing pc p
  ]
giffhornTests = testGroup "(concerning Giffhorns LSOD)" $
  [  testCase    ("isSecureGiffhornClassification2 is sound for " ++ exampleName)
                $ isSecureGiffhornClassification2 p → isLSODEmpirically p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ("isSecureGiffhornClassification is sound for " ++ exampleName)
                $ isSecureGiffhornClassification p → isLSODEmpirically p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ("giffhornLSOD == isSecureGiffhornClassification for " ++ exampleName)
                $ giffhornLSOD p == isSecureGiffhornClassification p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []
