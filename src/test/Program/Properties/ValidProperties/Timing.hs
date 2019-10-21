{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Timing where

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


import Program.MHP (mhpSetFor, mhpDifferent, mhpDifferentSlow)
import Program.Properties.Analysis
import Program.Analysis
import Program.Typing.FlexibleSchedulerIndependentChannels (isSecureFlexibleSchedulerIndependentChannel)

timing     = defaultMain                               $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests], mkProp [timingClassificationDomPathsProps] ]
timingX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests], mkProp [timingClassificationDomPathsProps] ]

timingClassificationDomPathsProps = testGroup "(concerning timingClassificationDomPaths)" [
    testPropertySized 30  "cl timing ⊑ cl minimal"
                $ \generated -> let p :: Program Gr = toProgramIntra generated
                                    pc = precomputedUsing idomDefaultFor p
                                    clMinimal            = minimalClassificationFor   pc p
                                    (clTiming,clTiming2) = timingClassificationAtUses pc p
                                in   (clTiming ⊑ clMinimal)
                                   ∧ (∀) (Map.assocs clTiming2) (\((m1,m2), clTiming2) -> (clTiming2 ⊑ (clMinimal ! m1))  ∨  (clTiming2 ⊑ (clMinimal ! m2))),
    testPropertySized 20  "cl timing ⊑ cl minimal w.r.t. node sets"
                $ \generated -> let p :: Program Gr = toProgramIntra generated
                                    pc = precomputedUsing idomDefaultFor p
                                    clMinimal            = minimalClassificationNodes   pc p
                                    (clTiming,clTiming2) = timingClassificationAtUsesNodes pc p
                                in   (clTiming ⊑ clMinimal)
                                   ∧ (∀) (Map.assocs clTiming2) (\((m1,m2), clTiming2) ->  clTiming2  ⊆  clMinimal ! m1 ∪ clMinimal ! m2),
    testPropertySized 30  "mhpDifferent == mhpDifferentSlow in non-procedural programs"
                $ \generated -> let p :: Program Gr = toProgramIntra generated in mhpDifferent p == mhpDifferentSlow p,
    testPropertySized 12  "mhpDifferent == mhpDifferentSlow in     procedural programs"
                $ \generated -> let p :: Program Gr = toProgram      generated in mhpDifferent p == mhpDifferentSlow p,
    testPropertySized 30  "mhpSetFor    == mhpDifferent     in non-procedural programs"
                $ \generated -> let p :: Program Gr = toProgramIntra generated in mhpSetFor p == mhpDifferent p,
    testPropertySized 30  "timingClassificationAtUses is at least as precise as FlexibleSchedulerIndependence"
                $ \generated -> let  p :: Program Gr = toProgramIntra generated in
                isSecureTimingClassificationAtUses p ⊒ isSecureFlexibleSchedulerIndependentChannel generated,
    testPropertySized 30  "timingClassificationDomPaths is at least as precise as timingClassificationSimple"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureTimingClassificationSimple,
    testPropertySized 30  "timingClassificationAtUses is at least as precise as minimalClassification"
                $ \generated -> let isAtLeastAsPreciseAs = isAtLeastAsPreciseAsPC generated in isSecureTimingClassificationAtUsesFor `isAtLeastAsPreciseAs` isSecureMinimalClassificationFor,
    testPropertySized 30  "timingClassificationAtUses is at least as precise as timingClassificationDomPaths"
                $ isSecureTimingClassificationAtUses `isAtLeastAsPreciseAs` isSecureTimingClassificationDomPaths,
    testPropertySized 30  "timingClassificationDomPaths is at least as precise as giffhornLSOD"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` giffhornLSOD
  ]

timingClassificationDomPathsTests = testGroup "(concerning timingClassificationDomPaths)" $
  [ testCase     ("timingClassificationDomPaths is at least as precise as timingClassificationSimple for " ++ exampleName)
                ((isSecureTimingClassificationDomPaths example ⊒ isSecureTimingClassificationSimple example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase     ("timingClassificationAtUses is at least as precise as minimalClassification for " ++ exampleName)
                ((isSecureTimingClassificationAtUses example ⊒ isSecureMinimalClassification example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase     ("timingClassificationAtUses is at least as precise as TimingClassificationDomPaths for " ++ exampleName)
                ((isSecureTimingClassificationAtUses example ⊒ isSecureTimingClassificationDomPaths example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase     ("timingClassificationDomPaths is at least as precise as giffhornLSOD for " ++ exampleName)
                ((isSecureTimingClassificationDomPaths example ⊒ giffhornLSOD example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  []
