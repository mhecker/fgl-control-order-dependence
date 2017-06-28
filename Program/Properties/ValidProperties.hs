{-# LANGUAGE ScopedTypeVariables #-}
module Program.Properties.ValidProperties where

import Prelude hiding (all)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)

import Algebra.Lattice
import Unicode

import Test.Tasty
import Test.Tasty.Providers (singleTest)
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

import Test.Tasty.Runners.AntXML
import Test.Tasty.Ingredients.Basic

import Test.QuickCheck (Testable, property)
import Test.QuickCheck.Property (Property(..))

import Data.Ord

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe(fromJust)

import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trcOfTrrIsTrc, withUniqueEndNode, fromSuccMap)
import Data.Graph.Inductive (mkGraph, nodes, pre, suc)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.ControlDependence (controlDependenceGraphP, controlDependence)
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    isinkdomOf, isinkdomOfGfp2, isinkdomOfTwoFinger6, joinUpperBound, controlSinks, sinkdomOfJoinUpperBound,
    sinkdomOf, mdomOf, sinkdomOfGfp, mdomOfLfp, sinkdomOfLfp, sinkDFF2cd, sinkDFF2GraphP, sinkDFcd, sinkDFGraphP, sinkDFFromUpLocalDefcd, sinkDFFromUpLocalDefGraphP, sinkDFFromUpLocalcd, sinkDFFromUpLocalGraphP, sinkdomOfisinkdomProperty,
    sinkDFUp, sinkDFUpDef,
    sinkDFLocal, sinkDFLocalDef, sinkDFUpGivenX,    nticdF3GraphP, nticdF3'GraphP, nticdF3'dualGraphP, nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, nticdF3WorkListGraphP, nticdDef, nticdDefGraphP, nticdF3WorkListSymbolicGraphP, nticdF3'dualWorkListSymbolicGraphP, nticdFig5GraphP, nticdF5GraphP,
    ntscdF4GraphP, ntscdF3GraphP, ntscdF4WorkListGraphP,                                                                        ntscdF4, ntscdF3, ntscdF4WorkList,                      ntscdDef, ntscdDefGraphP
  ) 


import Data.Graph.Inductive.Arbitrary


import Program (Program)

import Program.Properties.Analysis
import Program.Properties.CDom
import Data.Graph.Inductive.Query.BalancedSCC -- TODO: refactor that module into 2 seperate modules

import Execution (allFinishedExecutionTraces, someFinishedAnnotatedExecutionTraces)
import Program.Examples (testsuite, precisionCounterExamples)
import Program.Defaults (defaultInput)
import Program.Analysis
import Program.Typing.FlexibleSchedulerIndependentChannels (isSecureFlexibleSchedulerIndependentChannel)
import Program.CDom
import Program.Generator (toProgram, GeneratedProgram)

main      = all

all        = defaultMain                               $ tests
allX       = defaultMainWithIngredients [antXMLRunner] $ tests
cdom       = defaultMain                               $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
cdomX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
balanced   = defaultMain                               $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
balancedX  = defaultMainWithIngredients [antXMLRunner] $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
timing     = defaultMain                               $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
timingX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
simon      = defaultMain                               $ testGroup "simon"     [ mkTest [simonClassificationTests],                                       mkProp [simonClassificationProps] ]
simonX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "simon"     [ mkTest [simonClassificationTests],                                       mkProp [simonClassificationProps] ]
giffhorn   = defaultMain                               $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]
giffhornX  = defaultMainWithIngredients [antXMLRunner] $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]
soundness  = defaultMain                               $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]
soundnessX = defaultMainWithIngredients [antXMLRunner] $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]
preccex    = defaultMain                               $ testGroup "preccex"   [ mkTest [precisionCounterExampleTests] ]
preccexX   = defaultMainWithIngredients [antXMLRunner] $ testGroup "preccex"   [ mkTest [precisionCounterExampleTests] ]
nticd      = defaultMain                               $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]
nticdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]
ntscd      = defaultMain                               $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]
ntscdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]

insensitiveDom    = defaultMain                               $ testGroup "insensitiveDom"   [ mkTest [insensitiveDomTests], mkProp [insensitiveDomProps]]
insensitiveDomX   = defaultMainWithIngredients [antXMLRunner] $ testGroup "insensitiveDom"   [ mkTest [insensitiveDomTests], mkProp [insensitiveDomProps]]
sensitiveDom      = defaultMain                               $ testGroup "sensitiveDom"     [ {- mkTest [sensitiveDomTests], -} mkProp [sensitiveDomProps]]
sensitiveDomX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "sensitiveDom"     [ {- mkTest [sensitiveDomTests], -} mkProp [sensitiveDomProps]]



misc       = defaultMain                               $ testGroup "misc"      [ mkProp [miscProps] ]
miscX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "misc"      [ mkProp [miscProps] ]

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"


tests :: TestTree
tests = testGroup "Tests" [unitTests, properties]


properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps, cdomProps, cdomCdomProps, balancedParanthesesProps, soundnessProps                              , nticdProps, ntscdProps, insensitiveDomProps, sensitiveDomProps]

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests, cdomTests, cdomCdomTests, balancedParanthesesTests, soundnessTests, precisionCounterExampleTests, nticdTests, ntscdTests, insensitiveDomTests]


soundnessProps =  testGroup "(concerning soundness)" [
    testPropertySized 3
     ("allSound [ timingClassification, timingClassification, timingClassificationSimple, minimalClassification, giffhornLSOD, simonClassification ] ")
     ( allSound [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification ] )
  ]

soundnessTests =  testGroup "(concerning soundness)" $
  [ testCase      ("allSoundP [ timingClassificationDomPaths, timingClassification, timingClassificationSimple, minimalClassification, giffhornLSOD, simonClassification ] for " ++ exampleName)
                  ( allSoundP [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification ] example @? "")
  | (exampleName, example) <- testsuite
  ] ++
  []


precisionCounterExampleTests = testGroup "(counterxamples to: timingClassification(-DomPaths) is at least as precise as minimalClassification)" $
  [ testCase     ("timingClassificationAtUses *is*  at least as precise as minimalClassification for " ++ exampleName)
                ((      isSecureTimingClassificationAtUses example ⊒ isSecureMinimalClassification example) @? "")
  | (exampleName, example) <- precisionCounterExamples
  ] ++
  [ testCase     ("timingClassification is *not* at least as precise as minimalClassification for " ++ exampleName)
                ((not $ isSecureTimingClassification       example ⊒ isSecureMinimalClassification example) @? "")
  | (exampleName, example) <- precisionCounterExamples
  ] ++
  []


timingClassificationDomPathsProps = testGroup "(concerning timingClassificationDomPaths)" [
    testProperty  "timingClassificationAtUses is at least as precise as FlexibleSchedulerIndependence"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                isSecureTimingClassificationAtUses p ⊒ isSecureFlexibleSchedulerIndependentChannel generated,
    testProperty  "timingClassificationDomPaths == timingClassification"
                  timingDDomPathsIsTimingG,
    testProperty  "timingClassificationDomPaths is at least as precise as timingClassificationSimple"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureTimingClassificationSimple,
    testProperty  "timingClassificationAtUses is at least as precise as minimalClassification"
                $ isSecureTimingClassificationAtUses `isAtLeastAsPreciseAs` isSecureMinimalClassification,
    testProperty  "timingClassificationAtUses is at least as precise as timingClassificationDomPaths"
                $ isSecureTimingClassificationAtUses `isAtLeastAsPreciseAs` isSecureTimingClassificationDomPaths,
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




simonClassificationProps = testGroup "(concerning simonClassification)" [
    testProperty  "simonClassification is at least as precise as minimalClassification"
                $ isSecureSimonClassification `isAtLeastAsPreciseAs` isSecureMinimalClassification
  ]

simonClassificationTests = testGroup "(concerning timingClassificationDomPaths)" $
  [ testCase     ("simonClassification is at least as precise as minimalClassification for " ++ exampleName)
                ((isSecureSimonClassification example ⊒ isSecureMinimalClassification example) @? "")
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


insensitiveDomProps = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" [
    testProperty   "joinUpperBound always computes an upper bound"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                        sinks = NTICD.controlSinks g
                    in (∀) (Map.assocs $ NTICD.joinUpperBound g) (\(n,maybeNs) -> maybeNs /= Nothing ∨   (∃) (sinks) (\sink -> n ∈ sink)),
    testProperty   "isinkdomOf^*          == sinkdomOfJoinUpperBound^*"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in (trc $ NTICD.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              NTICD.sinkdomOfJoinUpperBound g),
    -- testProperty   "isinkdomOf^*          == isinkdomOfTwoFinger6^*"
    --             $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
    --                 let (exit, g) = (entry, generatedGraph)
    --                 in (trc $ NTICD.isinkdomOf                 g :: Gr () ()) ==
    --                    (trc $ fromSuccMap $
    --                     NTICD.isinkdomOfTwoFinger6             g)
    testProperty   "isinkdomOf^*          == isinkdomOfGfp2^*"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in (trc $ NTICD.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        NTICD.isinkdomOfGfp2             g),
    testProperty   "sinkdomOf reduces, in some sense,  to a multi-rooted tree"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                        isinkdom = NTICD.isinkdomOf g :: Gr () ()
                    in   (∀) (nodes isinkdom) (\n -> length (suc isinkdom n) <= 1),
    testProperty   "sinkdomOf             == sinkdomOfisinkdomProperty"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.sinkdomOf                  g ==
                       NTICD.sinkdomOfisinkdomProperty  g,
    testProperty   "sinkdomOf             == sinkdomOfLfp "
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.sinkdomOf              g ==
                       NTICD.sinkdomOfLfp           g,
    testProperty   "sinkdomOf             == sinkdomOfGfp "
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.sinkdomOf              g ==
                       NTICD.sinkdomOfGfp           g,
    testProperty   "sinkDFUpGivenX ! (x,z) is independent of choice of x for given z"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                    let sinkDFUp = NTICD.sinkDFUpGivenX g
                    in (∀) (Map.assocs sinkDFUp) (\((x,z), dfUp) ->
                         (∀) (Map.assocs sinkDFUp) (\((x',z'), dfUp') ->
                           (z == z') → (dfUp == dfUp')
                         )
                       ),
    testProperty   "sinkDFUp              == sinkDFUpDef"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                       NTICD.sinkDFUp                g ==
                       NTICD.sinkDFUpDef             g,
    testProperty   "sinkDFLocal           == sinkDFLocalDef"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                       NTICD.sinkDFLocal             g ==
                       NTICD.sinkDFLocalDef          g,
    testProperty   "sinkDFcd              == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.sinkDFcd         g entry () exit ==
                       NTICD.nticdF3          g entry () exit,
    testProperty   "sinkDFFromUpLocalDefcd== nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.sinkDFFromUpLocalDefcd  g entry () exit ==
                       NTICD.nticdF3                 g entry () exit,
    testProperty   "sinkDFFromUpLocalcd   == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.sinkDFFromUpLocalcd     g entry () exit ==
                       NTICD.nticdF3                 g entry () exit,
    testProperty   "sinkDFF2cd            == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.sinkDFF2cd       g entry () exit ==
                       NTICD.nticdF3          g entry () exit
  ]

insensitiveDomTests = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" $
  [  testCase    ( "sinkDFGraphP              ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.sinkDFGraphP p            == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFFromUpLocalGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.sinkDFFromUpLocalGraphP p == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFFromUpLocalDefGraphP==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.sinkDFFromUpLocalDefGraphP p
                                              ==
                                                 NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFF2GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.sinkDFF2GraphP p          == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []



sensitiveDomProps = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" [
    testProperty  "mdomOf              == mdomOfLfp "
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.mdomOf                 g ==
                       NTICD.mdomOfLfp              g
  ]



nticdProps = testGroup "(concerning nticd )" [
    testProperty  "nticdFig5GraphP               == nticdF5GraphP    for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdFig5GraphP p        == NTICD.nticdF5GraphP p,
    testProperty  "controlDependenceGraphp       == nticdF3GraphP   for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  controlDependenceGraphP p      == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3'GraphP                == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3'GraphP p         == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3'dualGraphP            == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3'dualGraphP p     == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3WorkListGraphP         == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3WorkListGraphP p  == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3WorkListSymbolicGraphP == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3WorkListSymbolicGraphP p == NTICD.nticdF3GraphP p,
    testProperty  "nticdFig5              == nticdF5                for graphs with unique end node property"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in NTICD.nticdFig5        g entry () exit ==
                       NTICD.nticdF5          g entry () exit,
    testProperty  "controlDependence      == nticdF3                for graphs with unique end node property"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in controlDependence      g entry () exit ==
                       NTICD.nticdF3          g entry () exit,
    testProperty  "nticdDef               == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.nticdDef         g entry () exit ==
                       NTICD.nticdF3          g entry () exit,
    testProperty  "nticdF3'               == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.nticdF3'         g entry () exit ==
                       NTICD.nticdF3          g entry () exit,
    testProperty  "nticdF3'dual           == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.nticdF3'dual     g entry () exit ==
                       NTICD.nticdF3          g entry () exit,
    testProperty  "nticdF3WorkList        == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.nticdF3WorkList  g entry () exit ==
                       NTICD.nticdF3          g entry () exit,
    testProperty  "nticdF3WorkListSymbolic== nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.nticdF3WorkListSymbolic g entry () exit ==
                       NTICD.nticdF3                 g entry () exit,
    testProperty  "nticdF3'dorkListSymbolic  == nticdF3"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = (entry, generatedGraph)
                    in NTICD.nticdF3'dualWorkListSymbolic g entry () exit ==
                       NTICD.nticdF3                      g entry () exit
  ]
nticdTests = testGroup "(concerning nticd)" $
  [  testCase    ( "nticdFig5GraphP           ==       nticdF5GraphP for " ++ exampleName)
            $ NTICD.nticdFig5GraphP p         == NTICD.nticdF5GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "controlDependenceGraphP   ==       nticdF3GraphP for " ++ exampleName)
                  $ controlDependenceGraphP p == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFF2GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.sinkDFF2GraphP p          == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdDefGraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.nticdDefGraphP p          == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.nticdF3'GraphP p          == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'dualGraphP        ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.nticdF3'dualGraphP p      == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3WorkListGraphP     ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.nticdF3WorkListGraphP p   == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3WorkListSymbolicGraphP     ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.nticdF3WorkListSymbolicGraphP p   == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'dualWorkListSymbolicGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.nticdF3'dualWorkListSymbolicGraphP p   == NTICD.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []


ntscdProps = testGroup "(concerning ntscd )" [
    testProperty  "ntscdF4GraphP          == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.ntscdF4GraphP p         == NTICD.ntscdF3GraphP p,
                
    testProperty  "ntscdF4WorkListGraphP  == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.ntscdF4WorkListGraphP p == NTICD.ntscdF3GraphP p,
    testProperty  "ntscdF4WorkList == ntscdF3"
                $ \((CG entry g) :: (Connected Gr () ())) ->
                    let exit = entry -- all this does is add a self-loop to entry
                    in NTICD.ntscdF4WorkList g entry () exit ==
                       NTICD.ntscdF3         g entry () exit,
    testProperty  "ntscdF4         == ntscdF3"
                $ \((CG entry g) :: (Connected Gr () ())) ->
                    let exit = entry -- all this does is add a self-loop to entry
                    in NTICD.ntscdF4         g entry () exit ==
                       NTICD.ntscdF3         g entry () exit,
    testProperty  "ntscdDef        == ntscdF3"
                $ \((CG entry g) :: (Connected Gr () ())) ->
                    let exit = entry -- all this does is add a self-loop to entry
                    in NTICD.ntscdDef        g entry () exit ==
                       NTICD.ntscdF3         g entry () exit
  ]

ntscdTests = testGroup "(concerning ntscd)" $
  [  testCase    ( "ntscdF4GraphP            ==       ntscdF3GraphP for " ++ exampleName)
            $ NTICD.ntscdF4GraphP p          == NTICD.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdF4WorkListGraphP    ==       ntscdF3GraphP for " ++ exampleName)
            $ NTICD.ntscdF4WorkListGraphP p  == NTICD.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdDefGraphP           ==       ntscdF3GraphP for " ++ exampleName)
            $ NTICD.ntscdDefGraphP p         == NTICD.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []





cdomCdomProps = testGroup "(concerning cdoms)" $
  [ testPropertySized 3 ("cdomIsCdom idomChef")
                $ \generated -> let  p :: Program Gr = toProgram generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations p execs idomChef == []
  ] ++
  [ testPropertySized 3 ("cdomIsCdom' idomMohrEtAl")
                $ \generated -> let  p :: Program Gr = toProgram generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations' p execs idomMohrEtAl == []
  ] ++
  [ testPropertySized 3 ("cdomIsCdom idomMohrEtAl")
                $ \generated -> let  p :: Program Gr = toProgram generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations p execs idomMohrEtAl == []
  ] ++
  []


cdomCdomTests = testGroup "(concerning cdoms)" $
  [ testCase ("cdomIsCdom idomChef for " ++ exampleName)  $ (cdomIsCdomViolations p execs idomChef) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  [ testCase ("cdomIsCdom' idomMohrEtAl for " ++ exampleName)  $ (cdomIsCdomViolations' p execs idomMohrEtAl) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  [ testCase ("cdomIsCdom idomMohrEtAl for " ++ exampleName)  $ (cdomIsCdomViolations p execs idomMohrEtAl) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
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
