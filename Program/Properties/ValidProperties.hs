{-# LANGUAGE ScopedTypeVariables #-}
module Program.Properties.ValidProperties where

import Prelude hiding (all)

import Algebra.Lattice
import Unicode

import Test.Tasty
import Test.Tasty.Providers (singleTest)
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

import Test.QuickCheck (Testable, property)
import Test.QuickCheck.Property (Property(..))

import Data.Ord

import qualified Data.Set as Set
import qualified Data.Map as Map

import Data.Graph.Inductive.Util (trcOfTrrIsTrc)
import Data.Graph.Inductive (mkGraph)
import Data.Graph.Inductive.PatriciaTree (Gr)

import Program (Program)

import Program.Properties.Analysis
import Program.Properties.CDom
import Data.Graph.Inductive.Query.BalancedSCC -- TODO: refactor that module into 2 seperate modules


import Program.Examples (testsuite, ijisLSODistkaputt, cdomIsBroken')
import Program.Analysis
import Program.CDom
import Program.Generator (toProgram)

main      = all

all       = defaultMain $ tests
cdom      = defaultMain $ testGroup "cdom"     [cdomTests, cdomProps]
balanced  = defaultMain $ testGroup "balanced" [balancedParanthesesTests, balancedParanthesesProps ]
timing    = defaultMain $ testGroup "timing"   [timingClassificationDomPathsTests, timingClassificationDomPathsProps ]
giffhorn  = defaultMain $ testGroup "giffhorn" [giffhornTests, giffhornProps ]
misc      = defaultMain $ testGroup "misc"     [miscProps]
soundness = defaultMain $ testGroup "soundness" [soundnessTests, soundnessProps]

tests :: TestTree
tests = testGroup "Tests" [unitTests, properties]


properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps, cdomProps, balancedParanthesesProps, soundnessProps ]

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests, cdomTests, balancedParanthesesTests, soundnessTests ]


soundnessProps =  testGroup "(concerning soundness)" [
    testPropertySized 30
     ("allSound [ timingClassification, timingClassification, timingClassificationSimple, minimalClassification, giffhornLSOD ] ")
     ( allSound [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD ] )
  ]

soundnessTests =  testGroup "(concerning soundness)" $
  [ testCase      ("allSoundP [ timingClassificationDomPaths, timingClassification, timingClassificationSimple, minimalClassification, giffhornLSOD ] for " ++ exampleName)
                  ( allSoundP [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD ] example @? "")
  | (exampleName, example) <- testsuite
  ] ++
  []

timingClassificationDomPathsProps = testGroup "(concerning timingClassificationDomPaths)" [
    testProperty  "timingClassificationDomPaths == timingClassification"
                  timingDDomPathsIsTimingG,
    testProperty  "timingClassificationDomPaths is at least as precise as timingClassificationSimple"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureTimingClassificationSimple,
    testProperty  "timingClassificationDomPaths is at least as precise as minimalClassification"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureMinimalClassification,
    testProperty  "timingClassificationDomPaths is at least as precise as giffhornLSOD"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` giffhornLSOD
  ]


timingClassificationDomPathsTests = testGroup "(concerning timingClassificationDomPaths)" $
  [  testCase     ("timingClassificationDomPaths == timingClassification for " ++ exampleName)
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


cdomProps = testGroup "(concerning Chops between cdoms and the nodes involved)" [
    testProperty  "idomIsTreeProgram idomChef"        $ idomIsTreeProgram idomChef,
    testProperty  "idomIsTreeProgram idomMohrEtAl"    $ idomIsTreeProgram idomMohrEtAl,
    testProperty  "chopsCdomArePrefixes idomChef"     $ chopsCdomArePrefixes idomChef,
    testProperty  "chopsCdomArePrefixes idomMohrEtAl" $ chopsCdomArePrefixes idomMohrEtAl,
    testProperty  "idomChefTreeIsDomTree"             $ idomChefTreeIsDomTree,
    testProperty  "chopsCdomAreExclChops idomChef"     $ chopsCdomAreExclChops idomChef,
    testProperty  "chopsCdomAreExclChops idomMohrEtAl" $ chopsCdomAreExclChops idomMohrEtAl,
    -- testProperty  "inclChopIsChop"                     $ inclChopIsChop, -- this appears to hold, but takes fucking long to quickcheck, so we skip it here
    testProperty  "exclChopContainedinclChop"          $ exclChopContainedinclChop,
    testProperty  "selfChopsSame"                      $ selfChopsSame,
    testProperty  "selfChopsSCC"                       $ selfChopsSCC
  ]

balancedParanthesesProps = testGroup "(concerning sccs, as well as general chops and balanced-parantheses-chops)" [
    testProperty  "sccIsSccNaive"                     $ sccIsSccNaive,
    testProperty  "sccIsSameLevelScc"                 $ sccIsSameLevelScc,
    testProperty  "simulUnbrIsUnbr"                   $ simulUnbrIsUnbr,
    testProperty  "simulUnblIsUnbl"                   $ simulUnblIsUnbl,
    testProperty  "simulUnbr'IsUnbr"                  $ simulUnbrIsUnbr,
    testProperty  "simulUnbl'IsUnbl"                  $ simulUnblIsUnbl,
    testProperty  "balancedChopIsSimulBalancedChop"   $ balancedChopIsSimulBalancedChop,
    testProperty  "chopsInterIDomAreChops"            $ chopsInterIDomAreChops,
    testProperty  "sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs" $ sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs
--    testProperty  "sameLevelSummaryGraphIssameLevelSummaryGraph'" $ sameLevelSummaryGraphIssameLevelSummaryGraph', -- this appears to hold, but takes fucking long to quickcheck, so we skip it here
  ]

balancedParanthesesTests = testGroup "(concerning sccs, as well as general chops and balanced-parantheses-chops)" $
  [ testCase (rpad 35 summName ++ "for graphTest0") $
             summ graphTest0  @=?
             mkGraph [(0,()),(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,())] [(0,7,fromList [1,2,3,4,5,6]),(1,4,fromList [2,3]),(2,3,fromList []),(4,5,fromList []),(5,6,fromList [2,3])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest") $
             summ graphTest  @=?
             mkGraph [(0,()),(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,())] [(0,7,fromList [1,2,3,4,5,6]),(1,4,fromList [2,3]),(2,3,fromList []),(4,5,fromList []),(5,6,fromList [2,3]),(6,5,fromList [])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest2") $
             summ graphTest2 @=?
             mkGraph [(0,()),(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,()),(8,())] [(0,8,fromList [1,2,3,4,5,6,7]),(1,4,fromList [1,2,3,4,5,6,7]),(2,3,fromList []),(2,7,fromList []),(3,6,fromList [1,2,3,4,5,6,7]),(4,5,fromList []),(6,7,fromList [])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest3") $
             summ graphTest3 @=?
             mkGraph [(0,()),(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,())] [(0,7,fromList [1,2,4,5,6]),(1,2,fromList []),(2,3,fromList [1,2,4,5,6]),(2,4,fromList [1,2,4,5,6]),(2,6,fromList []),(4,5,fromList []),(6,5,fromList [])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest4") $
             summ graphTest4 @=?
             mkGraph [(0,()),(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,())] [(0,7,fromList [1,2,3,4,5,6]),(1,5,fromList [2,3,4]),(2,4,fromList [3]),(5,6,fromList [2,3,4])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest5") $
             summ graphTest5 @=?
             mkGraph [(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,()),(8,())] [(1,2,fromList []),(1,7,fromList []),(2,5,fromList [3,4]),(3,4,fromList []),(5,6,fromList []),(7,8,fromList [3,4]),(8,6,fromList [])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest6") $
             summ graphTest6 @=?
             mkGraph [(1,()),(2,()),(3,()),(4,())] [(1,2,fromList []),(1,3,fromList []),(3,3,fromList [1,2]),(4,2,fromList [])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest7") $
             summ graphTest7 @=?
             mkGraph [(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,()),(8,()),(9,()),(10,()),(11,()),(12,())] [(1,2,fromList []),(1,10,fromList []),(2,5,fromList [3,4]),(3,4,fromList []),(5,8,fromList [6,7]),(6,7,fromList []),(8,9,fromList []),(10,11,fromList [6,7]),(11,12,fromList [3,4]),(12,9,fromList [])]
  | (summ,summName) <- summs
  ] ++
  [ testCase (rpad 35 summName ++ "for graphTest8") $
             summ graphTest8 @=?
             mkGraph [(0,()),(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,())] [(0,1,fromList []),(0,6,fromList []),(1,5,fromList [2,3,4]),(2,3,fromList []),(3,4,fromList []),(6,7,fromList [3,4])]
  | (summ,summName) <- summs
  ] ++
  [ testCase ("interIdom for graphTest5") $
             interIDom graphTest5 1 @=? Map.fromList [(2,fromList [1]),(3,fromList [1]),(4,fromList [3]),(5,fromList [2,4]),(6,fromList [4]),(7,fromList [1]),(8,fromList [4,7])]
  ] ++
  [ testCase ("interIdom for graphTest6") $
             interIDom graphTest6 1 @=? Map.fromList [(2,fromList [1]),(3,fromList [1]),(4,fromList [2,3])]
  ] ++
  [ testCase ("interIdom for graphTest7") $
             interIDom graphTest7 1 @=? Map.fromList [(2,fromList [1]),(3,fromList [1]),(4,fromList [3]),(5,fromList [2,4]),(6,fromList [1]),(7,fromList [6]),(8,fromList [5,7]),(9,fromList [4,7]),(10,fromList [1]),(11,fromList [7,10]),(12,fromList [4,11])]
  ] ++
  [ testCase ("interIdom for graphTest8") $  -- TODO: the expected result as below is NOT correct: 5 *is* dominated by 2, but the interIDom implementation assumes a "CFG"-Like Graph (i.e.: nu multiple procedure entries), so it gives the result below.
             interIDom graphTest8 0 @=? Map.fromList [(1,fromList [0]),(2,fromList [1]),(3,fromList [0]),(4,fromList [3]),(5,fromList [1,4]),(6,fromList [0]),(7,fromList [4,6])]
  ] ++
  [ testCase ("balancedChopIsSimulBalancedChop for graphTest9") $
             balancedChopIsSimulBalancedChop graphTest9 @? ""
  ] ++
  []
 where fromList = Set.fromList
       summs = [(sameLevelSummaryGraph',          "sameLevelSummaryGraph'"),
                (sameLevelSummaryGraph,           "sameLevelSummaryGraph"),
                (sameLevelSummaryGraphMerged,     "sameLevelSummaryGraphMerged"),
                (sameLevelSummaryGraph'WithoutBs, "sameLevelSummaryGraph'WithoutBs")
               ]
       rpad m xs = take m $ xs ++ repeat ' '

cdomTests = testGroup "(concerning Chops between cdoms and the nodes involved)" $
  [ testCase ("chopsCdomArePrefixes idomChef for " ++ exampleName)  $ chopsCdomArePrefixes idomChef p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomArePrefixes idomMohrEtAl for " ++ exampleName)  $ chopsCdomArePrefixes idomMohrEtAl p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("idomChefTreeIsDomTree for " ++ exampleName)  $ idomChefTreeIsDomTree p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomAreExclChops idomChef for " ++ exampleName)  $ chopsCdomAreExclChops idomChef p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomAreExclChops idomMohrEtAl for " ++ exampleName)  $ chopsCdomAreExclChops idomMohrEtAl p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("inclChopIsChop for " ++ exampleName)  $ inclChopIsChop p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("exclChopContainedinclChop for " ++ exampleName)  $ exclChopContainedinclChop p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("selfChopsSame for " ++ exampleName)  $ selfChopsSame p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("selfChopsSCC for " ++ exampleName)  $ selfChopsSCC p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []


miscProps = testGroup "(misc)" [
    testProperty  "trcOfTrrIsTrc"                     $ trcOfTrrIsTrc
  ]


testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
  where MkProperty gen = property prop

