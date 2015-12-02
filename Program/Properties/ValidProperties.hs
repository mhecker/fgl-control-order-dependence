module Program.Properties.ValidProperties where

import Algebra.Lattice
import Unicode

import Test.Tasty
import Test.Tasty.SmallCheck as SC
import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Data.List
import Data.Ord

import Program.Properties.Analysis
import Program.Examples (testsuite)
import Program.Analysis

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [properties, unitTests]

properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps ]

timingClassificationDomPathsProps = testGroup "(concerning timingClassificationDomPaths)" [
    QC.testProperty  "timingClassificationDomPaths == timingClassificationDomPaths"
                     timingDDomPathsIsTiming,
    QC.testProperty  "timingClassificationDomPaths is at least as precise as minimalClassification"
                   $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureMinimalClassification,
    QC.testProperty  "timingClassificationDomPaths is at least as precise as giffhornLSOD"
                   $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` giffhornLSOD
  ]

unitTests = testGroup "Unit tests" [ timingClassificationDomPathsTests ]
timingClassificationDomPathsTests = testGroup "(concerning timingClassificationDomPaths)" $
  [  testCase        ("timingClassificationDomPaths == timingClassificationDomPaths for " ++ exampleName)
                    (timingDDomPathsIsTiming example @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase        ("timingClassificationDomPaths is at least as precise as minimalClassification for " ++ exampleName)
                   ((isSecureTimingClassificationDomPaths example ⊒ isSecureMinimalClassification example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  []
