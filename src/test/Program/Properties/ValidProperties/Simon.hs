{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Simon where


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

import Program.Properties.Analysis (isAtLeastAsPreciseAs)
import Program.Analysis

simon      = defaultMain                               $ testGroup "simon"     [ mkTest [simonClassificationTests],                                       mkProp [simonClassificationProps] ]
simonX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "simon"     [ mkTest [simonClassificationTests],                                       mkProp [simonClassificationProps] ]


simonClassificationProps = testGroup "(concerning simonClassification)" [
    testPropertySized 20  "simonClassification is at least as precise as minimalClassification"
                $ isSecureSimonClassification `isAtLeastAsPreciseAs` isSecureMinimalClassification
  ]

simonClassificationTests = testGroup "(concerning simonClassification)" $
  [ testCase     ("simonClassification is at least as precise as minimalClassification for " ++ exampleName)
                ((isSecureSimonClassification example ⊒ isSecureMinimalClassification example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  []
