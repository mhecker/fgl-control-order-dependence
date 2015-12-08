{-# LANGUAGE ScopedTypeVariables #-}
module Program.Properties.ValidProperties where

import Algebra.Lattice
import Unicode

import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Data.List
import Data.Ord

import Data.Graph.Inductive.PatriciaTree (Gr)

import Program (Program)
import Program.Properties.Analysis
import Program.Examples (testsuite, ijisLSODistkaputt)
import Program.Analysis
import Program.Generator (toProgram)

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [properties, unitTests]

properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps ]

timingClassificationDomPathsProps = testGroup "(concerning timingClassificationDomPaths)" [
    testProperty  "timingClassificationDomPaths == timingClassification"
                  timingDDomPathsIsTiming,
    testProperty  "timingClassificationDomPaths is at least as precise as timingClassificationSimple"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureTimingClassificationSimple,
    testProperty  "timingClassificationDomPaths is at least as precise as minimalClassification"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureMinimalClassification,
    testProperty  "timingClassificationDomPaths is at least as precise as giffhornLSOD"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` giffhornLSOD
  ]

unitTests = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests ]

timingClassificationDomPathsTests = testGroup "(concerning timingClassificationDomPaths)" $
  [  testCase     ("timingClassificationDomPaths == timingClassificationDomPaths for " ++ exampleName)
                 (timingDDomPathsIsTiming example @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase     ("timingClassificationDomPaths is at least as precise as timingClassificationSimple for " ++ exampleName)
                ((isSecureTimingClassificationDomPaths example ⊒ isSecureTimingClassificationSimple example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase     ("timingClassificationDomPaths is at least as precise as minimalClassification for " ++ exampleName)
                ((isSecureTimingClassificationDomPaths example ⊒ isSecureMinimalClassification example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase     ("timingClassificationDomPaths is at least as precise as giffhornLSOD for " ++ exampleName)
                ((isSecureTimingClassificationDomPaths example ⊒ giffhornLSOD example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  []



giffhornProps = testGroup "(concerning Giffhorns LSOD)" [
    testProperty  "giffhornLSOD == isSecureGiffhornClassification "
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  giffhornLSOD p == isSecureGiffhornClassification p
  ]
giffhornTests = testGroup "(concerning Giffhorns LSOD)" $
  [  testCase    ("giffhornLSOD == isSecureGiffhornClassification for " ++ exampleName)
                $ giffhornLSOD p == isSecureGiffhornClassification p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []
