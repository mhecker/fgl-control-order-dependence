{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Soundness where


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

import Program.Examples (testsuite, interestingDodWod, insecure, syntacticCodeExamples, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)

import Program.DynamicAnalysis (isSecureEmpirically, isLSODEmpirically)

import Program.Properties.Analysis
import Program.Analysis
import Program.Typing.ResumptionBasedSecurity (Criterion(..), isSecureResumptionBasedSecurity, isSecureResumptionBasedSecurityFor)

soundness  = defaultMain                               $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]
soundnessX = defaultMainWithIngredients [antXMLRunner] $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]

soundnessProps =  testGroup "(concerning soundness)" [
    testPropertySized 3
     ("isSound  isSecureResumptionBasedSecurity")
     (isSoundPartialGen $ isSecureResumptionBasedSecurity ZeroOneBisimilarity),
    testPropertySized 15
         ("allSoundIntraMulti [isSecureTimingClassificationAtUses, isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureTimingClassificationIdomBischof, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification, isSecureGiffhornClassification2] ")
         ( allSoundIntraMulti [isSecureTimingClassificationAtUses, isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureTimingClassificationIdomBischof, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification, isSecureGiffhornClassification2] )
  ]

soundnessTests =  testGroup "(concerning soundness)" $
  [ testCase      ("allSoundP [isSecureTimingClassificationAtUses, isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureTimingClassificationIdomBischof, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification, isSecureGiffhornClassification2] for " ++ exampleName)
                  ( allSoundP [isSecureTimingClassificationAtUses, isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureTimingClassificationIdomBischof, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification, isSecureGiffhornClassification2] example @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase      ("insecure example programs are  identified as such by the empiric test for " ++ exampleName)
                  ( (not $ isSecureEmpirically example) @? "")
  | (exampleName, example) <- insecure
  ] ++
  [ testCase      ("isSound  isSecureResumptionBasedSecurity for " ++ exampleName)
                  ( (isSecureResumptionBasedSecurityFor ZeroOneBisimilarity forExample)
                    →
                    (isSecureEmpirically $ code2Program example)  @? "")
  | (exampleName, example) <- syntacticCodeExamples, Just forExample <- [code2ResumptionForProgram example]
  ] ++
  []
