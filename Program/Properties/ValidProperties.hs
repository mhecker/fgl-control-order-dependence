{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

-- #define UNCONNECTED
#ifdef UNCONNECTED
#define ARBITRARY(g) (g) :: (Gr () ())
#else
#define ARBITRARY(g) (CG _ g) :: (Connected Gr () ())
#endif
#define REDUCIBLE(g) (RedG g) :: (Reducible Gr () ())
#define INTER(g) (InterGraph g) :: (InterGraph () String)
#define INTERCFG(g) (InterCFG _ g) :: (InterCFG (Node) (Node, Node))


module Program.Properties.ValidProperties where

import Prelude hiding (all)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)
import Control.Exception.Base (assert)

import Algebra.Lattice
import Unicode

import Util(the, reachableFromIn, sampleFrom)
import Test.Tasty
import Test.Tasty.Providers (singleTest)
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)

import Test.Tasty.Runners.AntXML
import Test.Tasty.Ingredients.Basic

import Test.QuickCheck (Testable, property)
import Test.QuickCheck.Property (Property(..))

import Data.Ord

import Debug.Trace (traceShow)


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Map ( Map, (!) )
import Data.Maybe(fromJust)

import IRLSOD(CFGEdge(..))

import Data.Graph.Inductive.Arbitrary.Reducible
import Data.Graph.Inductive.Query.DFS (scc)
import Data.Graph.Inductive.Query.TimingDependence (timingDependence)
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trcOfTrrIsTrc, withUniqueEndNode, fromSuccMap)
import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.ControlDependence (controlDependenceGraphP, controlDependence)
import Data.Graph.Inductive.Query.DataDependence (dataDependenceGraphP, dataDependenceGraphViaIndependenceP, withParameterNodes)
import Data.Graph.Inductive.Query.ProgramDependence (programDependenceGraphP, addSummaryEdges, addSummaryEdgesLfp, addSummaryEdgesGfpLfp, addSummaryEdgesGfpLfpWorkList, summaryIndepsPropertyViolations, implicitSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdges, addImplicitAndTrivialSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdgesGfpLfp)

import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    pathsBetweenBFS, pathsBetweenUpToBFS,
    pathsBetween,    pathsBetweenUpTo,
    prevCondsWithSuccNode, prevCondsWithSuccNode', 
    alternativeTimingSolvedF3dependence, timingSolvedF3dependence, timingF3dependence, timingF3EquationSystem', timingF3EquationSystem, snmTimingEquationSystem, timingSolvedF3sparseDependence, timingSnSolvedDependence, timingSnSolvedDependenceWorklist, timingSnSolvedDependenceWorklist2, enumerateTimingDependence,
    solveTimingEquationSystem, timdomOfTwoFinger, timdomOfLfp, Reachability(..), timmaydomOfLfp,
    Color(..), smmnFMustDod, smmnFMustWod,
    colorLfpFor, colorFor,
    possibleIntermediateNodesFromiXdom, withPossibleIntermediateNodesFromiXdom,
    nticdMyWodSlice, wodTEILSlice, ntscdDodSlice, ntscdMyDodSlice, 
    smmnGfp, smmnLfp, fMust, fMustNoReachCheck, dod, dodDef, dodFast, myWod, myWodFast, dodColoredDagFixed, dodColoredDagFixedFast, myDod, myDodFast, wodTEIL', wodDef, wodFast, fMay, fMay',
    ntacdDef, ntacdDefGraphP,     ntbcdDef, ntbcdDefGraphP,
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    isinkdomOf, isinkdomOfGfp2, joinUpperBound, controlSinks, sinkdomOfJoinUpperBound, isinkdomOfSinkContraction, isinkdomOfTwoFinger8,
    nticdSinkContraction, nticdSinkContractionGraphP,
    sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkDFF2cd, sinkDFF2GraphP, sinkDFcd, sinkDFGraphP, sinkDFFromUpLocalDefcd, sinkDFFromUpLocalDefGraphP, sinkDFFromUpLocalcd, sinkDFFromUpLocalGraphP, sinkdomOfisinkdomProperty, sinkdomNaiveGfp,
    sinkDFUp, sinkDFUpDef, sinkDFUpDefViaSinkdoms, imdomOfTwoFinger6, imdomOfTwoFinger7,
    sinkDFLocal, sinkDFLocalDef, sinkDFLocalViaSinkdoms, sinkDFUpGivenX, sinkDFUpGivenXViaSinkdoms,
    sinkDFFromUpLocalDefViaSinkdoms, sinkDF,
    idomToDF, idomToDFFast,
    imdomOf, imdomOfLfp,
    mdomOf,                   mdomOfLfp,   mDFF2cd,    mDFF2GraphP,    mDFcd,    mDFGraphP,   mDFFromUpLocalDefcd,     mDFFromUpLocalDefGraphP,    mDFFromUpLocalcd,    mDFFromUpLocalGraphP,    mdomOfimdomProperty, imdomTwoFingercd, mdomNaiveLfp,
    mDFUp, mDFUpDef, mDFUpDefViaMdoms, mDFUpGivenXViaMdoms,
    mDFLocal, mDFLocalDef, mDFLocalViaMdoms, mDFUpGivenX, 
    mDFFromUpLocalDefViaMdoms, mDF,
    nticdF3GraphP, nticdF3'GraphP, nticdF3'dualGraphP, nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, nticdF3WorkListGraphP, nticdDef, nticdDefGraphP, nticdF3WorkListSymbolicGraphP, nticdF3'dualWorkListSymbolicGraphP, nticdFig5GraphP, nticdF5GraphP, nticdF3'dualWorkList, snmF3'dual, nticdF3'dualWorkListGraphP,
    ntscdF4GraphP, ntscdF3GraphP, ntscdF4WorkListGraphP,                                                                        ntscdF4, ntscdF3, ntscdF4WorkList,                      ntscdDef, ntscdDefGraphP
  ) 
import qualified Data.Graph.Inductive.FA as FA


import Data.Graph.Inductive.Arbitrary


import Program (Program, tcfg)
import Program.Tests (isSecureEmpirically)

import Program.Properties.Analysis
import Program.Properties.CDom
import Data.Graph.Inductive.Query.BalancedSCC -- TODO: refactor that module into 2 seperate modules

import Execution (allFinishedExecutionTraces, someFinishedAnnotatedExecutionTraces)
import Program.Examples (testsuite, interproceduralTestSuit, precisionCounterExamples, interestingDodWod, interestingTimingDep, syntacticCodeExamples, code2ResumptionForProgram, code2Program, interestingIsinkdomTwoFinger)
import Program.Defaults (defaultInput)
import Program.Analysis
import Program.Typing.FlexibleSchedulerIndependentChannels (isSecureFlexibleSchedulerIndependentChannel)
import Program.Typing.ResumptionBasedSecurity (Criterion(..), isSecureResumptionBasedSecurity, isSecureResumptionBasedSecurityFor)
import Program.CDom
import Program.Generator (toProgram, toProgramIntra, GeneratedProgram)

main      = all

all        = defaultMain                               $ tests
allX       = defaultMainWithIngredients [antXMLRunner] $ tests
cdom       = defaultMain                               $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
cdomX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
balanced   = defaultMain                               $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
balancedX  = defaultMainWithIngredients [antXMLRunner] $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
timing     = defaultMain                               $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
timingX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
timingDep  = defaultMain                               $ testGroup "timingDep" [ mkTest [timingDepTests], mkProp [timingDepProps] ]
timingDepX = defaultMainWithIngredients [antXMLRunner] $ testGroup "timingDep" [ mkTest [timingDepTests], mkProp [timingDepProps] ]
simon      = defaultMain                               $ testGroup "simon"     [ mkTest [simonClassificationTests],                                       mkProp [simonClassificationProps] ]
simonX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "simon"     [ mkTest [simonClassificationTests],                                       mkProp [simonClassificationProps] ]
giffhorn   = defaultMain                               $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]
giffhornX  = defaultMainWithIngredients [antXMLRunner] $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]
soundness  = defaultMain                               $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]
soundnessX = defaultMainWithIngredients [antXMLRunner] $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]
preccex    = defaultMain                               $ testGroup "preccex"   [ mkTest [precisionCounterExampleTests] ]
preccexX   = defaultMainWithIngredients [antXMLRunner] $ testGroup "preccex"   [ mkTest [precisionCounterExampleTests] ]
nticd      = defaultMain                               $ testGroup "nticd"     [ mkTest [{-nticdTests-}], mkProp [nticdProps]]
nticdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]
ntscd      = defaultMain                               $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]
ntscdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]
newcd      = defaultMain                               $ testGroup "newcd"     [ mkTest [newcdTests], mkProp [newcdProps]]
newcdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "newcd"     [ mkTest [newcdTests], mkProp [newcdProps]]
dod        = defaultMain                               $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]
dodX       = defaultMainWithIngredients [antXMLRunner] $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]
wod        = defaultMain                               $ testGroup "wod"       [ mkTest [wodTests], mkProp [wodProps]]
wodX       = defaultMainWithIngredients [antXMLRunner] $ testGroup "wod"       [ mkTest [wodTests], mkProp [wodProps]]
color      = defaultMain                               $ testGroup "color"     [ mkTest [colorTests], mkProp [colorProps]]
colorX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "color"     [ mkTest [colorTests], mkProp [colorProps]]
reducible  = defaultMain                               $ testGroup "reducible" [                      mkProp [reducibleProps]]
reducibleX = defaultMainWithIngredients [antXMLRunner] $ testGroup "reducible" [                      mkProp [reducibleProps]]
indeps     = defaultMain                               $ testGroup "indeps"    [ mkTest [indepsTests], mkProp [indepsProps]]
indepsX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "indeps"    [ mkTest [indepsTests], mkProp [indepsProps]]



insensitiveDom    = defaultMain                               $ testGroup "insensitiveDom"   [ mkTest [insensitiveDomTests],  mkProp [insensitiveDomProps]]
insensitiveDomX   = defaultMainWithIngredients [antXMLRunner] $ testGroup "insensitiveDom"   [ mkTest [insensitiveDomTests],  mkProp [insensitiveDomProps]]
sensitiveDom      = defaultMain                               $ testGroup "sensitiveDom"     [ mkTest [sensitiveDomTests],  mkProp [sensitiveDomProps]]
sensitiveDomX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "sensitiveDom"     [ mkTest [sensitiveDomTests],  mkProp [sensitiveDomProps]]



misc       = defaultMain                               $ testGroup "misc"      [ mkProp [miscProps] ]
miscX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "misc"      [ mkProp [miscProps] ]

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"


tests :: TestTree
tests = testGroup "Tests" [unitTests, properties]


properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps, cdomProps, cdomCdomProps, balancedParanthesesProps, soundnessProps                              , nticdProps, ntscdProps, insensitiveDomProps, sensitiveDomProps, timingDepProps, dodProps, wodProps, colorProps, reducibleProps, indepsProps]

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests, cdomTests, cdomCdomTests, balancedParanthesesTests, soundnessTests, precisionCounterExampleTests, nticdTests, ntscdTests, insensitiveDomTests, sensitiveDomTests, timingDepTests, dodProps, wodProps, colorProps                , indepsTests]


soundnessProps =  testGroup "(concerning soundness)" [
    testPropertySized 3
     ("isSound  isSecureResumptionBasedSecurity")
     (isSoundPartialGen $ isSecureResumptionBasedSecurity ZeroOneBisimilarity),
    testPropertySized 3
     ("allSound [ timingClassification, timingClassification, timingClassification, timingClassificationSimple, minimalClassification, giffhornLSOD, simonClassification ] ")
     ( allSound [ isSecureTimingClassificationAtUses, isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification ] )
  ]

soundnessTests =  testGroup "(concerning soundness)" $
  [ testCase      ("allSoundP [ timingClassificationDomPaths, timingClassification, timingClassificationSimple, minimalClassification, giffhornLSOD, simonClassification ] for " ++ exampleName)
                  ( allSoundP [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification ] example @? "")
  | (exampleName, example) <- testsuite
  ] ++
  [ testCase      ("isSound  isSecureResumptionBasedSecurity for " ++ exampleName)
                  ( (isSecureResumptionBasedSecurityFor ZeroOneBisimilarity forExample)
                    →
                    (isSecureEmpirically $ code2Program example)  @? "")
  | (exampleName, example) <- syntacticCodeExamples, Just forExample <- [code2ResumptionForProgram example]
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
    testProperty  "timingClassificationAtUses is at least as precise as resumptionBasedSecurity"
                $ isSecureTimingClassificationAtUses `isAtLeastAsPreciseAsPartialGen`  (isSecureResumptionBasedSecurity ZeroOneBisimilarity),
    testProperty  "timingClassificationAtUses is at least as precise as FlexibleSchedulerIndependence"
                $ \generated -> let  p :: Program Gr = toProgramIntra generated in
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
    -- testProperty   "idomToDFFast _ isinkdom == sinkDF _"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     isinkdom1 = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
    --                     isinkdom2 = fromSuccMap $ NTICD.isinkdomOfTwoFinger8      g :: Gr () ()
    --                 in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
    --                    NTICD.idomToDFFast g isinkdom ==
    --                    NTICD.sinkDF       g),
    -- testProperty   "idomToDFFast _ isinkdom == idomToDF _ isinkdom"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     isinkdom1 = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
    --                     isinkdom2 = fromSuccMap $ NTICD.isinkdomOfTwoFinger8      g :: Gr () ()
    --                 in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
    --                    NTICD.idomToDFFast g isinkdom ==
    --                    NTICD.idomToDF     g isinkdom),
    -- testProperty   "DF of isinkdom Cycles are all the same"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     isinkdom1 = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
    --                     isinkdom2 = fromSuccMap $ NTICD.isinkdomOfTwoFinger8      g :: Gr () ()
    --                     df1    = NTICD.idomToDF g isinkdom1
    --                     idomSccs1 = scc isinkdom1
    --                     cycles1 = [ cycle | cycle <- idomSccs1, length cycle > 1 ]
    --                     df2    = NTICD.idomToDF g isinkdom2
    --                     idomSccs2 = scc isinkdom2
    --                     cycles2 = [ cycle | cycle <- idomSccs2, length cycle > 1 ]
    --                 in (∀) [(isinkdom1, cycles1, df1), (isinkdom2, cycles2, df2)] (\(isinkdom, cycles, df) ->
    --                    (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))),
    -- testProperty   "isinkdomOfSinkContraction is intransitive"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     isinkdom1 = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
    --                     isinkdom2 = fromSuccMap $ NTICD.isinkdomOfTwoFinger8      g :: Gr () ()
    --                 in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
    --                      (∀) (nodes isinkdom) (\n -> length (suc isinkdom n) <= 1)),
    testProperty   "isinkdomOf^*          == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ NTICD.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              NTICD.isinkdomOfTwoFinger8       g)
    -- testProperty   "isinkdomOf^*          == isinkdomOfSinkContraction^*"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in (trc $ NTICD.isinkdomOf                 g :: Gr () ()) ==
    --                    (trc $ fromSuccMap $
    --                           NTICD.isinkdomOfSinkContraction g),
    -- testProperty   "joinUpperBound always computes an upper bound"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     sinks = NTICD.controlSinks g
    --                 in (∀) (Map.assocs $ NTICD.joinUpperBound g) (\(n,maybeNs) -> maybeNs /= Nothing ∨   (∃) (sinks) (\sink -> n ∊ sink)),
    -- testProperty   "isinkdomOf^*          == sinkdomOfJoinUpperBound^*"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in (trc $ NTICD.isinkdomOf                 g :: Gr () ()) ==
    --                    (trc $ fromSuccMap $
    --                           NTICD.sinkdomOfJoinUpperBound g),
    -- testProperty   "isinkdomOf^*          == isinkdomOfGfp2^*"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in (trc $ NTICD.isinkdomOf                 g :: Gr () ()) ==
    --                    (trc $ fromSuccMap $
    --                     NTICD.isinkdomOfGfp2             g),
    -- testProperty   "sinkdomOf reduces, in some sense,  to a multi-rooted tree"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     isinkdom = NTICD.isinkdomOf g :: Gr () ()
    --                 in   (∀) (nodes isinkdom) (\n -> length (suc isinkdom n) <= 1),
    -- testProperty   "sinkdomOf             == sinkdomOfisinkdomProperty"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkdomOf                  g ==
    --                    NTICD.sinkdomOfisinkdomProperty  g,
    -- testProperty   "sinkdomOf             == sinkdomNaiveLfp "
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkdomOf              g ==
    --                    NTICD.sinkdomNaiveGfp        g,
    -- testProperty   "sinkdomOf             == sinkdomOfLfp "
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkdomOf              g ==
    --                    NTICD.sinkdomOfLfp           g,
    -- testProperty   "sinkdomOf             == sinkdomOfGfp "
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkdomOf              g ==
    --                    NTICD.sinkdomOfGfp           g,
    -- testProperty   "sinkDFFromUpLocalDefViaSinkdoms == sinkDF"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                    NTICD.sinkDFFromUpLocalDefViaSinkdoms g ==
    --                    NTICD.sinkDF                          g,
    -- testProperty   "sinkDFUpGivenXViaSinkdoms == sinkDFUpGivenX"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                    NTICD.sinkDFUpGivenXViaSinkdoms  g ==
    --                    NTICD.sinkDFUpGivenX             g,
    -- testProperty   "sinkDFUpDefViaSinkdoms == sinkDFUpDef"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                    NTICD.sinkDFUpDefViaSinkdoms  g ==
    --                    NTICD.sinkDFUpDef             g,
    -- testProperty   "sinkDFUpGivenX ! (x,z) is independent of choice of x for given z"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                 let sinkDFUp = NTICD.sinkDFUpGivenX g
    --                 in (∀) (Map.assocs sinkDFUp) (\((x,z), dfUp) ->
    --                      (∀) (Map.assocs sinkDFUp) (\((x',z'), dfUp') ->
    --                        (z == z') → (dfUp == dfUp')
    --                      )
    --                    ),
    -- testProperty   "sinkDFUpGivenX ! (x,z) == sinkDFUpDef ! z"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                 let sinkDFUp    = NTICD.sinkDFUpGivenX g
    --                     sinkDFUpDef = NTICD.sinkDFUpDef    g
    --                 in (∀) (Map.assocs sinkDFUp) (\((x,z), dfUp) ->
    --                      dfUp == sinkDFUpDef ! z
    --                    )
    --                 ∧  (∀) (Map.assocs sinkDFUpDef) (\(z, dfUp) ->
    --                      (∀) [ (x, dfUp') | ((x,z'), dfUp') <- Map.assocs sinkDFUp, z == z'] (\(x, dfUp') ->
    --                        dfUp == dfUp'
    --                      )
    --                    ),
    -- testProperty   "sinkDFUp              == sinkDFUpDef"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                    NTICD.sinkDFUp                g ==
    --                    NTICD.sinkDFUpDef             g,
    -- testProperty   "sinkDFLocalViaSinkdoms == sinkDFLocalDef"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                    NTICD.sinkDFLocalViaSinkdoms  g ==
    --                    NTICD.sinkDFLocalDef          g,
    -- testProperty   "sinkDFLocal            == sinkDFLocalDef"
    --             $ \((CG _ g) :: (Connected Gr () ())) ->
    --                    NTICD.sinkDFLocal             g ==
    --                    NTICD.sinkDFLocalDef          g,
    -- testProperty   "sinkDFcd              == nticdF3"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkDFcd         g ==
    --                    NTICD.nticdF3          g,
    -- testProperty   "sinkDFFromUpLocalDefcd== nticdF3"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkDFFromUpLocalDefcd  g==
    --                    NTICD.nticdF3                 g,
    -- testProperty   "sinkDFFromUpLocalcd   == nticdF3"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkDFFromUpLocalcd     g ==
    --                    NTICD.nticdF3                 g,
    -- testProperty   "sinkDFF2cd            == nticdF3"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.sinkDFF2cd       g ==
    --                    NTICD.nticdF3          g
  ]

insensitiveDomTests = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" $
  [  testCase    ( "idomToDFFast _ isinkdom == sinkDF _ for " ++ exampleName)
            $       let isinkdom1 = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
                        isinkdom2 = fromSuccMap $ NTICD.isinkdomOfTwoFinger8      g :: Gr () ()
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       NTICD.idomToDFFast g isinkdom ==
                       NTICD.sinkDF       g) @? ""
  | (exampleName, g) <- interestingIsinkdomTwoFinger
  ] ++
  -- [  testCase    (  "sinkDFLocal == sinkDFLocalDef for " ++ exampleName)
  --           $          NTICD.sinkDFLocal    g ==
  --                      NTICD.sinkDFLocalDef g
  --                      @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    (  "sinkDFFromUpLocalDefViaSinkdoms == sinkDF for " ++ exampleName)
  --           $          NTICD.sinkDFFromUpLocalDefViaSinkdoms g ==
  --                      NTICD.sinkDF                          g
  --                      @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    (  "sinkDFUpGivenXViaMdoms == sinkDFUpGivenX for " ++ exampleName)
  --           $          NTICD.sinkDFUpGivenXViaSinkdoms     g ==
  --                      NTICD.sinkDFUpGivenX             g
  --                      @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    (  "sinkDFUpDefViaMdoms == sinkDFUpDef for " ++ exampleName)
  --           $            NTICD.sinkDFUpDefViaSinkdoms     g ==
  --                        NTICD.sinkDFUpDef             g
  --                      @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "idomToDFFast _ isinkdom == sinkDF _ for " ++ exampleName)
  --           $       let isinkdom1 = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
  --                       isinkdom2 = fromSuccMap $ NTICD.isinkdomOfTwoFinger8      g :: Gr () ()
  --                   in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
  --                      NTICD.idomToDFFast g isinkdom ==
  --                      NTICD.sinkDF       g) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "idomToDFFast _ isinkdom == idomToDF _ isinkdom for " ++ exampleName)
  --           $       let isinkdom1 = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
  --                       isinkdom2 = fromSuccMap $ NTICD.isinkdomOfTwoFinger8      g :: Gr () ()
  --                   in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
  --                       NTICD.idomToDFFast g isinkdom ==
  --                      NTICD.idomToDF     g isinkdom) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "DF of isinkdom Cycles are all the same for " ++ exampleName)
  --           $       let isinkdom = fromSuccMap $ NTICD.isinkdomOfSinkContraction g :: Gr () ()
  --                       df    = NTICD.idomToDF g isinkdom
  --                       idomSccs = scc isinkdom
  --                       cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
  --                   in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))  @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "sinkDFGraphP              ==       nticdF3GraphP for " ++ exampleName)
  --           $ NTICD.sinkDFGraphP p            == NTICD.nticdF3GraphP p @? ""
  -- | (exampleName, p) <- testsuite
  -- ] ++
  -- [  testCase    ( "sinkDFFromUpLocalGraphP   ==       nticdF3GraphP for " ++ exampleName)
  --           $ NTICD.sinkDFFromUpLocalGraphP p == NTICD.nticdF3GraphP p @? ""
  -- | (exampleName, p) <- testsuite
  -- ] ++
  -- [  testCase    ( "sinkDFFromUpLocalDefGraphP==       nticdF3GraphP for " ++ exampleName)
  --           $ NTICD.sinkDFFromUpLocalDefGraphP p
  --                                             ==
  --                                                NTICD.nticdF3GraphP p @? ""
  -- | (exampleName, p) <- testsuite
  -- ] ++
  -- [  testCase    ( "sinkDFF2GraphP            ==       nticdF3GraphP for " ++ exampleName)
  --           $ NTICD.sinkDFF2GraphP p          == NTICD.nticdF3GraphP p @? ""
  -- | (exampleName, p) <- testsuite
  -- ] ++
  []



sensitiveDomProps = testGroup "(concerning nontermination-sensitive control dependence via dom-like frontiers )" [
    testProperty   "mDFFromUpLocalDefViaSMdoms == mDF"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                       NTICD.mDFFromUpLocalDefViaMdoms g ==
                       NTICD.mDF                       g,
    testProperty   "idomToDFFast _ imdom == idomToDF _ imdom"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = fromSuccMap $ NTICD.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ NTICD.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         NTICD.idomToDFFast g imdom ==
                         NTICD.idomToDF     g imdom
                       ),
    testProperty   "idomToDFFast _ imdom  == mDF _ "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = fromSuccMap $ NTICD.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ NTICD.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         NTICD.idomToDFFast g imdom ==
                         NTICD.mDF          g
                       ),
    testProperty   "DF of imdom Cycles are all the same"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = fromSuccMap $ NTICD.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ NTICD.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         let df    = NTICD.idomToDF g imdom
                             idomSccs = scc imdom
                             cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                         in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))
                       ),
    testProperty   "imdomOfTwoFinger7^*   == imdomOfTwoFinger6^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ fromSuccMap $
                        NTICD.imdomOfTwoFinger7            g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        NTICD.imdomOfTwoFinger6            g),
    testProperty   "imdomOfLfp^*          == imdomOfTwoFinger6^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ NTICD.imdomOfLfp             g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        NTICD.imdomOfTwoFinger6            g),
    testProperty   "mdomOf             == mdomNaiveLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.mdomOf              g ==
                       NTICD.mdomNaiveLfp        g,
    testProperty   "mdomOf             == mdomOfLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.mdomOf              g ==
                       NTICD.mdomOfLfp           g,
    testProperty   "mdomOfLfp reduces, in some sense,  to a multi-rooted tree"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = NTICD.imdomOfLfp g :: Gr () ()
                    in   (∀) (nodes imdom) (\n -> length (suc imdom n) <= 1),
    testProperty   "mdomOfLfp           == mdomOfimdomProperty"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.mdomOfLfp            g ==
                       NTICD.mdomOfimdomProperty  g,
    testProperty   "mDFFromUpLocalDefViaSMdoms == mDF"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                       NTICD.mDFFromUpLocalDefViaMdoms g ==
                       NTICD.mDF                       g,
    testProperty   "mDFUpGivenXViaMdoms == mDFUpGivenX"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                       NTICD.mDFUpGivenXViaMdoms     g ==
                       NTICD.mDFUpGivenX             g,
    testProperty   "mDFUpDefViaMdoms == mDFUpDef"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                       NTICD.mDFUpDefViaMdoms     g ==
                       NTICD.mDFUpDef             g,
    testProperty   "mDFUpGivenX ! (x,z) is independent of choice of x for given z"
                $ \(ARBITRARY(g)) ->
                    let mDFUp = NTICD.mDFUpGivenX g
                    in (∀) (Map.assocs mDFUp) (\((x,z), dfUp) ->
                         (∀) (Map.assocs mDFUp) (\((x',z'), dfUp') ->
                           (z == z') → (dfUp == dfUp')
                         )
                       ),
    testProperty   "mDFUpGivenX ! (x,z) == mDFUpDef ! z"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                    let mDFUp    = NTICD.mDFUpGivenX g
                        mDFUpDef = NTICD.mDFUpDef    g
                    in (∀) (Map.assocs mDFUp) (\((x,z), dfUp) ->
                         dfUp == mDFUpDef ! z
                       )
                    ∧  (∀) (Map.assocs mDFUpDef) (\(z, dfUp) ->
                         (∀) [ (x, dfUp') | ((x,z'), dfUp') <- Map.assocs mDFUp, z == z'] (\(x, dfUp') ->
                           dfUp == dfUp'
                         )
                       ),
    testProperty   "mDFUp              == mDFUpDef"
                $ \(ARBITRARY(g)) ->
                       NTICD.mDFUp                g ==
                       NTICD.mDFUpDef             g,
    testProperty   "mDFLocalViaMdoms   == mDFLocalDef"
                $ \((CG _ g) :: (Connected Gr () ())) ->
                       NTICD.mDFLocalViaMdoms     g ==
                       NTICD.mDFLocalDef          g,
    testProperty   "mDFLocal           == mDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       NTICD.mDFLocal             g ==
                       NTICD.mDFLocalDef          g,
    testProperty   "mDFcd              == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.mDFcd            g ==
                       NTICD.ntscdF3          g,
    testProperty   "mDFFromUpLocalDefcd== ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.mDFFromUpLocalDefcd  g ==
                       NTICD.ntscdF3              g,
    testProperty   "mDFFromUpLocalcd   == ntisdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.mDFFromUpLocalcd     g ==
                       NTICD.ntscdF3              g,
    testProperty   "imdomTwoFingercd     == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.imdomTwoFingercd   g ==
                       NTICD.ntscdF3          g,
    testProperty   "mDFF2cd            == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.mDFF2cd              g ==
                       NTICD.ntscdF3              g
  ]
sensitiveDomTests = testGroup "(concerning nontermination-sensitive control dependence via dom-like frontiers )"  $
  [  testCase    (  "mDFLocal == mDFLocalDef for " ++ exampleName)
            $          NTICD.mDFLocal    g ==
                       NTICD.mDFLocalDef g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFFromUpLocalDefViaMdoms == mDF for " ++ exampleName)
            $          NTICD.mDFFromUpLocalDefViaMdoms g ==
                       NTICD.mDF                       g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFUpGivenXViaMdoms == mDFUpGivenX for " ++ exampleName)
            $          NTICD.mDFUpGivenXViaMdoms     g ==
                       NTICD.mDFUpGivenX             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFUpDefViaMdoms == mDFUpDef for " ++ exampleName)
            $            NTICD.mDFUpDefViaMdoms     g ==
                         NTICD.mDFUpDef             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ imdom == idomToDF _ imdom for " ++ exampleName)
            $       let imdom6 = fromSuccMap $ NTICD.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ NTICD.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         NTICD.idomToDFFast g imdom ==
                         NTICD.idomToDF     g imdom
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ imdom == mDF _ for " ++ exampleName)
            $       let imdom6 = fromSuccMap $ NTICD.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ NTICD.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         NTICD.idomToDFFast g imdom ==
                         NTICD.mDF          g
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "DF of imdom Cycles are all the same for " ++ exampleName)
            $       let imdom6 = fromSuccMap $ NTICD.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ NTICD.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         let df    = NTICD.idomToDF g imdom
                             idomSccs = scc imdom
                             cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                         in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))
                       )  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "imdomOfTwoFinger7^*   == imdomOfTwoFinger6^* for " ++ exampleName)
                  $ (trc $ fromSuccMap $
                           NTICD.imdomOfTwoFinger7            g :: Gr () ()) ==
                    (trc $ fromSuccMap $
                           NTICD.imdomOfTwoFinger6            g)  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "imdomOfLfp^*          == imdomOfTwoFinger6^* for " ++ exampleName)
                  $ (trc $ NTICD.imdomOfLfp             g :: Gr () ()) ==
                    (trc $ fromSuccMap $
                           NTICD.imdomOfTwoFinger6            g)  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []


newcdProps = testGroup "(concerning new control dependence definitions)" [
    testProperty  "ntacdDef               == nticdF3                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in NTICD.ntacdDef         g ==
                       NTICD.nticdF3          g
  ]
newcdTests = testGroup "(concerning new control dependence definitions)" $
  [  testCase    ( "ntnacdDefGraphP       ==  nticdF3GraphP for " ++ exampleName)
                  $ NTICD.ntacdDefGraphP      p ==
                    NTICD.nticdF3GraphP       p        @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []

wodProps = testGroup "(concerning weak order dependence)" [
    testPropertySized 40 "lfp fMay                 == lfp fMay'"
    $ \(ARBITRARY(g)) ->
                    let lfp      = NTICD.smmnLfp g NTICD.fMay
                        lfp'     = NTICD.smmnLfp g NTICD.fMay'
                    in  lfp                  == lfp',
    testPropertySized 40 "wodDef                    == wodFast"
    $ \(ARBITRARY(g)) ->
                    let wodDef   = NTICD.wodDef  g
                        wodFast  = NTICD.wodFast g
                    in  wodDef == wodFast,
    testProperty  "myWod ⊑ wodTEIL'"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        myWod = NTICD.myWod g
                        wodTEIL' = NTICD.wodTEIL' g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          ns ⊑ (wodTEIL' ! (m1,m2))
                        ),
  testProperty  "wodTEILSlice is contained in nticdMyWodSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticdWodSlice   = NTICD.nticdMyWodSlice g
                        wodTEILSlice    = NTICD.wodTEILSlice g
                    in  -- traceShow (length $ nodes g) $
                        (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice m1 m2 ⊑   nticdWodSlice m1 m2
                        )),
    testProperty  "myWod is contained in isinkdom sccs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom  = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        myWod = NTICD.myWod g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc isinkdomTrc m2 ∧ m1 ∊ suc isinkdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc isinkdomTrc n2) → (
                                   (n1 == n2) ∨ let [n1'] = Set.toList $ isinkdom ! n1 in n1 ∊ suc isinkdomTrc n1'
                              )
                          ))
                        ),
    testProperty  "snmF3Gfp reachable          == isinkdom reachable "
                $ \(ARBITRARY(generatedGraph)) ->
                    let graph     = generatedGraph
                        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
                        s3        = NTICD.snmF3 graph
                        isinkdom     = NTICD.isinkdomOfSinkContraction graph
                        isinkdomTrc  = trc $ (fromSuccMap isinkdom :: Gr () ())
                    in (∀) (nodes graph) (\m ->
                         (∀) condNodes (\n ->     ((n == m) ∨ (Set.size (s3 ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)))
                                               ↔ (m ∊ (suc isinkdomTrc n))
                         )
                       ),
    testProperty  "myWodFast                 == myWod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.myWodFast       g ==
                       NTICD.myWod           g
  ]
wodTests = testGroup "(concerning weak order dependence)" $
  [  testCase    ( "myWod ⊑ wodTEIL' for " ++ exampleName)
            $       let myWod = NTICD.myWod g
                        wodTEIL' = NTICD.wodTEIL' g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          ns ⊑ (wodTEIL' ! (m1,m2))
                        )@? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "wodTEILSlice is contained in nticdMyWodSlice for " ++ exampleName)
            $       let nticdWodSlice   = NTICD.nticdMyWodSlice g
                        wodTEILSlice    = NTICD.wodTEILSlice g
                    in  (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice m1 m2 ⊑   nticdWodSlice m1 m2
                        )) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "myWod is contained in isinkdom sccs  for " ++ exampleName)
            $       let isinkdom  = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        myWod = NTICD.myWod g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc isinkdomTrc m2 ∧ m1 ∊ suc isinkdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc isinkdomTrc n2) → (
                                   (n1 == n2) ∨ let [n1'] = Set.toList $ isinkdom ! n1 in n1 ∊ suc isinkdomTrc n1'
                              )
                          ))
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "myWodFast                   == myWod for " ++ exampleName)
            $ NTICD.myWodFast g                 == NTICD.myWod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []


dodProps = testGroup "(concerning decisive order dependence)" [
    testProperty  "rev sinkdom approximates pre-dom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinks = NTICD.controlSinks g
                    in (∀) sinks (\sink ->
                         let sinkGraph = subgraph sink g
                             imdomRev       = NTICD.imdomOfTwoFinger7 (grev sinkGraph)
                             imdomRevTrc    = trc $ (fromSuccMap $ imdomRev :: Gr () ())
                         in (∀) sink (\s ->
                              let isinkdomRev     = NTICD.isinkdomOfTwoFinger8 $ grev $ efilter (\(n,m,_) -> m /= s) $ sinkGraph
                                  isinkdomRevTrc  = trc $ (fromSuccMap $ isinkdomRev :: Gr () ())
                              in    (Set.fromList $ [(n,m) | (n,m) <- edges isinkdomRevTrc, n /= s, m /= s])
                                 ⊇ (Set.fromList $ [(n,m) | (n,m) <- edges imdomRevTrc,    n /= s, m /= s])
                            )
                       )
    -- testProperty  "myDod is contained in imdom sccs"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     imdom          = NTICD.imdomOfTwoFinger7 g
    --                     imdomTrc       = trc $ (fromSuccMap $ imdom    :: Gr () ())
    --                     isinkdomRev    = NTICD.isinkdomOfTwoFinger8 (grev g)
    --                     isinkdomRevTrc = trc $ (fromSuccMap $ isinkdomRev :: Gr () ())
    --                     imdomRev       = NTICD.imdomOfTwoFinger7 (grev g)
    --                     imdomRevTrc    = trc $ (fromSuccMap $ imdomRev :: Gr () ())
    --                     sMust = NTICD.smmnFMustDod g
    --                     myDod = NTICD.myDod g
    --                 in  (∀) (Map.assocs myDod) (\((m1,m2), ns) ->
    --                       (∀) ns (\n ->
    --                           (∃) (suc g n) (\x -> (n,x) ∈ sMust ! (m1,m2,n))
    --                         ∧ (∀) (suc g n) (\x ->
    --                               (m1 ∊ suc imdomTrc x)
    --                             ∧ (m2 ∊ suc imdomTrc x)
    --                             ∧ (((n,x) ∈ sMust ! (m1,m2,n)) → ((m1 ∊ (suc imdomRevTrc m2)) ∨ (m2 ∊ (suc imdomRevTrc m1))))
    --                           )
    --                       )
    --                     )
    -- testProperty  "myDodFast                 == myDod"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.myDodFast       g ==
    --                    NTICD.myDod           g,
    -- testProperty  "myDod is contained in imdom sccs"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     imdom  = NTICD.imdomOfTwoFinger6 g
    --                     imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
    --                     myDod = NTICD.myDod g
    --                 in  (∀) (Map.assocs myDod) (\((m1,m2), ns) ->
    --                       ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
    --                     ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
    --                           (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
    --                       ))
    --                     ∧ (∀) ns (\n ->
    --                           not $
    --                           (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
    --                       )
    --                     ),
    -- testProperty  "ntscdDodSlice == ntscdMyDodSlice property"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     myDod = NTICD.myDod g
    --                     ntscd = NTICD.ntscdF3 g
    --                     ntscdTrc = trc $ (fromSuccMap ntscd :: Gr () ())
    --                 in  (∀) (Map.assocs myDod) (\((m1,m2), ns) ->
    --                       (∀) ns (\n -> n ∈ myDod ! (m2,m1) ∨
    --                                     (∃) (ns) (\n' -> n' ∊ (suc ntscdTrc n))
    --                       )
    --                     ),
    -- testProperty  "ntscdDodSlice == ntscdMyDodSlice"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     ntscdDodSlice     = NTICD.ntscdDodSlice g
    --                     ntscdMyDodSlice   = NTICD.ntscdMyDodSlice g
    --                 in  -- traceShow (length $ nodes g) $
    --                     (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
    --                       ntscdDodSlice   m1 m2 ==
    --                       ntscdMyDodSlice m1 m2
    --                     )),
    -- testProperty  "dod implies myDod"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     dod = NTICD.dod g
    --                     myDod = NTICD.myDod g
    --                 in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
    --                       (∀) ns (\n -> n ∈ myDod ! (m1,m2) ∧
    --                                     n ∈ myDod ! (m2,m1)
    --                       )
    --                     ),
    -- testProperty  "myDod implies dod"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     dod = NTICD.dod g
    --                     myDod = NTICD.myDod g
    --                 in  (∀) (Map.keys myDod) (\(m1,m2) ->
    --                       (∀) (myDod ! (m1,m2)  ⊓  myDod ! (m2,m1)) (\n -> n ∈ dod ! (m1,m2)
    --                       )
    --                     ),
    -- testProperty  "dod is contained in imdom sccs "
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     imdom  = NTICD.imdomOfTwoFinger6 g
    --                     dod = NTICD.dod g
    --                     imdomSccs = scc (fromSuccMap imdom :: Gr () ())
    --                     imdomCycleOf m =  the (m ∊) $ imdomSccs
    --                 in  (∀) (nodes g) (\m1 ->
    --                       (∀) (List.delete m1 $ nodes g) (\m2 ->
    --                         let c1 = imdomCycleOf m1
    --                             c2 = imdomCycleOf m2
    --                         in (not (c1 == c2 ∧ length c1 > 1) ) → (Set.null $ dod ! (m1,m2))
    --                       )
    --                     ),
    -- testProperty  "dod is contained in imdom sccs, and only possible for immediate entries into sccs"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                     imdom  = NTICD.imdomOfTwoFinger6 g
    --                     imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
    --                     dod = NTICD.dod g
    --                 in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
    --                       ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
    --                     ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
    --                           (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
    --                       ))
    --                     ∧ (∀) ns (\n ->
    --                           not $
    --                           (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
    --                       )
    --                     ),
    -- testProperty  "snmF3Lfp reachable          == imdom reachable "
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let graph     = generatedGraph
    --                     condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
    --                     s3        = NTICD.snmF3Lfp graph
    --                     imdom     = NTICD.imdomOfTwoFinger6 graph
    --                     imdomTrc  = trc $ (fromSuccMap imdom :: Gr () ())
    --                 in (∀) (nodes graph) (\m ->
    --                      (∀) condNodes (\n ->     ((n == m) ∨ (Set.size (s3 ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)))
    --                                            ↔ (m ∊ (suc imdomTrc n))
    --                      )
    --                    ),
    -- testProperty  "dodColoredDagFixedFast     == dodDef"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.dodColoredDagFixedFast g ==
    --                    NTICD.dodDef                 g,
    -- testProperty  "dodColoredDagFixed         == dodDef"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.dodColoredDagFixed g ==
    --                    NTICD.dodDef             g,
    -- testProperty  "dod                       == dodDef"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.dod           g ==
    --                    NTICD.dodDef        g,
    -- testProperty  "dodFast                   == dodDef"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.dodFast       g ==
    --                    NTICD.dodDef        g,
    -- testProperty  "lfp fWOMustNoReachCheck      == lfp fWOMust"
    -- $ \(ARBITRARY(generatedGraph)) ->
    --                 let g = generatedGraph
    --                 in NTICD.smmnLfp g NTICD.fMustNoReachCheck        ==
    --                    NTICD.smmnLfp g NTICD.fMust
  ]
dodTests = testGroup "(concerning decisive order dependence)" $
  -- [  testCase    ( "myDodFast                 == myDod for " ++ exampleName)
  --           $ NTICD.myDodFast          g      == NTICD.myDod g @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "myDod is contained in imdom sccs  for " ++ exampleName)
  --           $       let imdom  = NTICD.imdomOfTwoFinger6 g
  --                       imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
  --                       myDod = NTICD.myDod g
  --                   in  (∀) (Map.assocs myDod) (\((m1,m2), ns) ->
  --                         ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
  --                       ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
  --                             (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
  --                         ))
  --                       ∧ (∀) ns (\n ->
  --                             not $
  --                             (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
  --                         )
  --                       ) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "ntscdDodSlice == ntscdMyDodSlice property for " ++ exampleName)
  --           $       let myDod = NTICD.myDod g
  --                       ntscd = NTICD.ntscdF3 g
  --                       ntscdTrc = trc $ (fromSuccMap ntscd :: Gr () ())
  --                   in  (∀) (Map.assocs myDod) (\((m1,m2), ns) ->
  --                         (∀) ns (\n -> n ∈ myDod ! (m2,m1) ∨
  --                                       (∃) (ns) (\n' -> n' ∊ (suc ntscdTrc n))
  --                         )
  --                       ) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "ntscdDodSlice == ntscdMyDodSlice for " ++ exampleName)
  --           $       let ntscdDodSlice     = NTICD.ntscdDodSlice g
  --                       ntscdMyDodSlice   = NTICD.ntscdMyDodSlice g
  --                   in  -- traceShow (length $ nodes g) $
  --                       (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
  --                         ntscdDodSlice   m1 m2 ==
  --                         ntscdMyDodSlice m1 m2
  --                       )) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "dod implies myDod for " ++ exampleName)
  --           $       let dod = NTICD.dod g
  --                       myDod = NTICD.myDod g
  --                   in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
  --                         (∀) ns (\n -> n ∈ myDod ! (m1,m2) ∧
  --                                       n ∈ myDod ! (m2,m1)
  --                         )
  --                       ) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "myDod implies dod for " ++ exampleName)
  --           $       let dod = NTICD.dod g
  --                       myDod = NTICD.myDod g
  --                   in  (∀) (Map.keys myDod) (\(m1,m2) ->
  --                         (∀) (myDod ! (m1,m2)  ⊓  myDod ! (m2,m1)) (\n -> n ∈ dod ! (m1,m2)
  --                         )
  --                       ) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "dod is contained in imdom sccs, and only possible for immediate entries into sccs for " ++ exampleName)
  --           $       let imdom  = NTICD.imdomOfTwoFinger6 g
  --                       imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
  --                       dod = NTICD.dod g
  --                   in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
  --                         ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
  --                       ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
  --                             (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
  --                         ))
  --                       ∧ (∀) ns (\n ->
  --                             not $
  --                             (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
  --                         )
  --                       ) @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "dodColoredDagFixedFast        == dodDef for " ++ exampleName)
  --           $ NTICD.dodColoredDagFixedFast g      == NTICD.dodDef g @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "dodColoredDagFixed        == dodDef for " ++ exampleName)
  --           $ NTICD.dodColoredDagFixed g      == NTICD.dodDef g @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "dod                       == dodDef for " ++ exampleName)
  --           $ NTICD.dod                g      == NTICD.dodDef g @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  -- [  testCase    ( "dodFast                   == dodDef for " ++ exampleName)
  --           $ NTICD.dodFast            g      == NTICD.dodDef g @? ""
  -- | (exampleName, g) <- interestingDodWod
  -- ] ++
  []



colorProps = testGroup "(concerning color algorithms)" [
    testProperty  "colorLfpFor                 == smmnFMustWod graph"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap isinkdom :: Gr () ())
                        sMust = NTICD.smmnFMustWod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = NTICD.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc isinkdomTrc n)) ∧ (m2 ∊ (suc isinkdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))),
    testProperty  "colorLfpFor                 == smmnFMustDod graph"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = NTICD.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = NTICD.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = NTICD.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))),
    testProperty  "colorLfpFor                 == colorFor"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = NTICD.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = NTICD.colorLfpFor g   m1 m2
                         in (∀) (nodes g) (\n ->
                           let color  = NTICD.colorFor    g n m1 m2
                           in (n /= m1 ∧ n /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                                (∀) (suc g n) (\x -> colorLfp ! x == color ! x)
                       ))),
    testProperty  "smmnFMustDod graph          == colorFor"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = NTICD.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = NTICD.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (condNodes) (\n ->   (∀) (nodes g) (\m1 ->    (∀) (nodes g) (\m2 ->
                         (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                         let color    = NTICD.colorFor    g n m1 m2
                         in   (∀) (suc g n) (\x -> (color ! x == NTICD.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n)))
                            ∧ (∀) (suc g n) (\x -> (color ! x == NTICD.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n)))
                       )))
  ]
colorTests = testGroup "(concerning color algorithms)" $
  [  testCase    ( "colorLfpFor                 == smmnFMustWod graph for" ++ exampleName)
            $       let isinkdom = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap isinkdom :: Gr () ())
                        sMust = NTICD.smmnFMustWod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = NTICD.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc isinkdomTrc n)) ∧ (m2 ∊ (suc isinkdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "colorLfpFor                 == smmnFMustDod graph for" ++ exampleName)
            $       let imdom = NTICD.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = NTICD.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = NTICD.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == NTICD.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "smmnFMustDod graph          == colorFor for " ++ exampleName)
            $       let imdom = NTICD.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = NTICD.colorLfpFor g   m1 m2
                         in (∀) (nodes g) (\n ->
                           let color  = NTICD.colorFor    g n m1 m2
                           in (n /= m1 ∧ n /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                                (∀) (suc g n) (\x -> colorLfp ! x == color ! x)
                       ))) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "colorLfpFor                 == colorFor for " ++ exampleName)
            $       let imdom = NTICD.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = NTICD.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (condNodes) (\n ->   (∀) (nodes g) (\m1 ->    (∀) (nodes g) (\m2 ->
                         (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                         let color    = NTICD.colorFor    g n m1 m2
                         in   (∀) (suc g n) (\x -> (color ! x == NTICD.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n)))
                            ∧ (∀) (suc g n) (\x -> (color ! x == NTICD.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n)))
                       )))
 @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []




nticdProps = testGroup "(concerning nticd )" [
    testProperty  "nticdFig5GraphP               == nticdF5GraphP    for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdFig5GraphP p        == NTICD.nticdF5GraphP p,
    testProperty  "nticdSinkContraction          == nticdF3GraphP   for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdSinkContractionGraphP p == NTICD.nticdF3GraphP p,
    testProperty  "controlDependenceGraphp       == nticdF3GraphP   for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  controlDependenceGraphP p      == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3'GraphP                == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3'GraphP p         == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3'dualGraphP            == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3'dualGraphP p     == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3'dualWorkListGraphP       == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3'dualWorkListGraphP p  == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3WorkListGraphP         == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3WorkListGraphP p  == NTICD.nticdF3GraphP p,
    testProperty  "nticdF3WorkListSymbolicGraphP == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.nticdF3WorkListSymbolicGraphP p == NTICD.nticdF3GraphP p,
    testProperty  "nticdFig5              == nticdF5                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                    in NTICD.nticdFig5        g ==
                       NTICD.nticdF5          g,
    testProperty  "controlDependence      == nticdF3                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in controlDependence      g exit ==
                       NTICD.nticdF3          g,
    testProperty  "nticdSinkContraction   == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdSinkContraction  g ==
                       NTICD.nticdF3               g,
    testProperty  "nticdDef               == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdDef         g ==
                       NTICD.nticdF3          g,
    testProperty  "nticdF3'               == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdF3'         g ==
                       NTICD.nticdF3          g,
    testProperty  "snmF3'dual           == snmF3 (dual)"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        snmF3      = NTICD.snmF3      g
                        snmF3'dual = NTICD.snmF3'dual g
                    in (∀) (Map.assocs snmF3) (\((m,p), mp) ->
                         let mp' = snmF3'dual ! (m,p)
                         in  mp == Set.fromList [ (p,x) | x <- suc g p] ∖ mp'
                       ),
    testProperty  "nticdF3'dual           == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdF3'dual     g ==
                       NTICD.nticdF3          g,
    testProperty  "nticdF3'dualWorkList        == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdF3'dualWorkList  g ==
                       NTICD.nticdF3          g,
    testProperty  "nticdF3WorkList        == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdF3WorkList  g ==
                       NTICD.nticdF3          g,
    testProperty  "nticdF3WorkListSymbolic== nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdF3WorkListSymbolic g ==
                       NTICD.nticdF3                 g,
    testProperty  "nticdF3'dorkListSymbolic  == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdF3'dualWorkListSymbolic g ==
                       NTICD.nticdF3                      g
  ]
nticdTests = testGroup "(concerning nticd)" $
  [  testCase    ( "nticdFig5GraphP           ==       nticdF5GraphP for " ++ exampleName)
            $ NTICD.nticdFig5GraphP p         == NTICD.nticdF5GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdSinkContractionGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ NTICD.nticdSinkContractionGraphP p == NTICD.nticdF3GraphP p @? ""
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



reducibleProps = testGroup "(concerning the generator for reducible graphs)" [
    testProperty  "every generated reducible graph is reducible"
                $ \(REDUCIBLE(g)) -> isReducible g
   ]


ntscdProps = testGroup "(concerning ntscd )" [
    testPropertySized 35 "wod ⊆ ntscd^* for reducible graphs"
                $ \(REDUCIBLE(g)) ->
                                let
                                     wod = NTICD.wodFast g
                                     ntscd = NTICD.ntscdF3 g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ),
    testPropertySized 4 "wod ⊆ ntscd^* for For-Programs, which by construction are reducible"
                $ \generated -> let  p :: Program Gr = toProgram generated
                                     g = tcfg p
                                     wod = NTICD.wodFast g
                                     ntscd = NTICD.ntscdF3 g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ),
    testProperty  "ntscdF4GraphP          == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.ntscdF4GraphP p         == NTICD.ntscdF3GraphP p,
                
    testProperty  "ntscdF4WorkListGraphP  == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.ntscdF4WorkListGraphP p == NTICD.ntscdF3GraphP p,
    testProperty  "ntscdF4WorkList == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       NTICD.ntscdF4WorkList g ==
                       NTICD.ntscdF3         g,
    testProperty  "ntscdF4         == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       NTICD.ntscdF4         g ==
                       NTICD.ntscdF3         g,
    testProperty  "ntscdDef        == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       NTICD.ntscdDef        g ==
                       NTICD.ntscdF3         g
  ]

ntscdTests = testGroup "(concerning ntscd)" $
  [  testCase    ( "wod ⊆ ntscd^* for                                   " ++ exampleName)
            $                   let  g = tcfg p
                                     wod = NTICD.wodFast g
                                     ntscd = NTICD.ntscdF3 g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ) @? ""
  | (exampleName, p) <- testsuite
  ] ++
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



timingDepProps = testGroup "(concerning timingDependence)" [
    testProperty  "the  solved timingF3EquationSystem is correct"
                $ \(ARBITRARY(g)) ->
                       let timingEqSolved    = NTICD.solveTimingEquationSystem $ NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem
                           trcG = trc g
                           pathsBetween     = NTICD.pathsBetween        g trcG
                           pathsBetweenUpTo = NTICD.pathsBetweenUpTo    g trcG
                       in  -- traceShow g $
                           (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in (m /= p) →
                                  let paths = pathsBetween p m in
                                  -- traceShow (m,p, rmq) $
                                  case rmq of
                                     NTICD.FixedStepsPlusOther s y ->
                                                                      let paths = pathsBetweenUpTo p m y in
                                                                      (∀) paths (\(hasLoop,  path ) -> y `elem` path ∧ (toInteger (length $ takeWhile (/= y) path)) == s + 1)
                                     NTICD.FixedSteps s            -> (∀) paths (\(hasLoop,  path ) -> (not hasLoop) ∧ (toInteger (length                    path)) == s + 2)
                                     NTICD.UndeterminedSteps       -> (∃) paths (\(hasLoop,  path ) -> hasLoop)
                                                                    ∨ (∃) paths (\(hasLoop1, path1) -> (not hasLoop1) ∧
                                                                          (∃) paths (\(hasLoop2, path2) -> (not hasLoop2) ∧ length (path1) /= (length path2))
                                                                      )
                                     NTICD.Unreachable             -> paths == []
                           ),
    testProperty  "prevCondsWithSuccNode  ==  prevCondsWithSuccNode'"
                $ \(ARBITRARY(g)) -> (∀) (nodes g) (\n -> 
                       (List.sort $ NTICD.prevCondsWithSuccNode  g n) ==
                       (List.sort $ NTICD.prevCondsWithSuccNode' g n)
                  ),
    testProperty  "timingSnSolvedDependence         == enumerateTimingDependence"
                $ \(ARBITRARY(g)) -> traceShow (length $ nodes g) $
                       NTICD.timingSnSolvedDependence  g ==
                       NTICD.enumerateTimingDependence  g,
    testProperty  "timingSnSolvedDependence         == timingSnSolvedDependenceWorklist"
                $ \(ARBITRARY(g)) -> traceShow (length $ nodes g) $
                       NTICD.timingSnSolvedDependence          g ==
                       NTICD.timingSnSolvedDependenceWorklist  g,
    testProperty  "timingSnSolvedDependence         == timingSnSolvedDependenceWorklist2"
                $ \(ARBITRARY(g)) -> traceShow (length $ nodes g) $
                       NTICD.timingSnSolvedDependence          g ==
                       NTICD.timingSnSolvedDependenceWorklist2 g,
    testProperty  "timingSolvedF3dependence == timingSnSolvedDependenceWorklist"
                $ \(ARBITRARY(g)) -> traceShow (length $ nodes g) $
                       NTICD.timingSolvedF3dependence g ==
                       NTICD.timingSnSolvedDependenceWorklist g,
    testProperty  "timingSolvedF3dependence == timingSnSolvedDependence"
                $ \(ARBITRARY(g)) ->  traceShow (length $ nodes g) $
                       NTICD.timingSolvedF3dependence g ==
                       NTICD.timingSnSolvedDependence g,
    testProperty  "timmaydomOfLfp            relates to solved timingF3EquationSystem"
                $ \(ARBITRARY(gg)) ->
                       let timingEqSolved    = NTICD.solveTimingEquationSystem $ NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem
                           timmaydomOfLfp    = NTICD.timmaydomOfLfp g
                           g = mkGraph [(-3,()),(0,()),(3,()),(4,())] [(0,-3,()),(0,3,()),(3,3,()),(4,-3,()),(4,0,()),(4,3,())] :: Gr () ()
                       in  (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in (m /= p) →
                                  case rmq of
                                     NTICD.FixedSteps s            -> Set.fromList [1+s] == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                                     NTICD.FixedStepsPlusOther s y -> Set.fromList [1+s] == Set.fromList [ steps | (y', steps) <- Set.toList $ timmaydomOfLfp ! p, y == y']
                                     NTICD.UndeterminedSteps       -> Set.fromList []    == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                                     NTICD.Unreachable             -> smp == Map.empty ∧
                                                                      Set.fromList []    == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                           ),
    testProperty  "timdomOfTwoFinger^*       == timdomOfLfp"
                $ \(ARBITRARY(g)) ->
                       let timdomOfTwoFinger = NTICD.timdomOfTwoFinger g
                           timdomOfLfp       = NTICD.timdomOfLfp g
                           mustReachFromIn   = reachableFromIn $ NTICD.withPossibleIntermediateNodesFromiXdom g $ timdomOfTwoFinger
                       in  -- traceShow (length $ nodes g, g) $
                           (∀) (Map.assocs timdomOfLfp) (\(n, ms) ->
                              (∀) (ms) (\(m,steps) -> Set.fromList [steps] == mustReachFromIn n m)
                           )
                         ∧ (∀) (nodes g) (\n -> (∀) (nodes g) (\m ->
                              mustReachFromIn n m == Set.fromList [ steps | (m', steps) <- Set.toList $ timdomOfLfp ! n, m == m']
                           )),
    testProperty  "timdomOfTwoFinger        relates to timingF3EquationSystem"
                $ \(ARBITRARY(g)) ->
                       let timingEqSolved    = NTICD.solveTimingEquationSystem $ NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem
                           timdomOfTwoFinger = NTICD.timdomOfTwoFinger g
                           mustReachFromIn   = reachableFromIn $ NTICD.withPossibleIntermediateNodesFromiXdom g $ timdomOfTwoFinger
                           mustReachFrom x   = suc imdomTrc x
                             where imdom    = NTICD.imdomOfTwoFinger7 g
                                   imdomTrc = trc $ fromSuccMap imdom :: Gr () ()
                       in  (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in ((m /= p) ∧ (∀) (suc g p) (\x -> m ∊ mustReachFrom x)) →
                                  case rmq of
                                     NTICD.FixedSteps s            -> Set.fromList [1+s] == mustReachFromIn p m
                                     NTICD.FixedStepsPlusOther s y -> Set.fromList [1+s] == mustReachFromIn p y
                                     NTICD.UndeterminedSteps       -> Set.fromList []    == mustReachFromIn p m
                           ),
    testProperty  "timingF3EquationSystem'  == timingF3EquationSystem"
                $ \(ARBITRARY(g)) ->
                       let timingEq        = NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem
                           timingEq'       = NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem'
                       in  timingEq         == timingEq',
    testProperty  "timingF3dependence is transitive"
                $ \(ARBITRARY(g)) ->
                       let tdep    = NTICD.timingF3dependence g
                       in (∀) (nodes g) (\n ->
                            (∀) (tdep ! n) (\n' ->
                              (∀) (tdep ! n') (\n'' ->
                                  (n'' == n)
                                ∨ (n'' ∈ tdep ! n)
                              )
                            )
                          ),
    testProperty  "timingSolvedF3dependence is transitive"
                $ \(ARBITRARY(g)) ->
                       let tdep    = NTICD.timingSolvedF3dependence g
                       in (∀) (nodes g) (\n ->
                            (∀) (tdep ! n) (\n' ->
                              (∀) (tdep ! n') (\n'' ->
                                  (n'' == n)
                                ∨ (n'' ∈ tdep ! n)
                              )
                            )
                          ),
    testProperty  "alternativeTimingSolvedF3dependence == timingSolvedF3dependence"
                $ \(ARBITRARY(g)) ->
                       let tdep            = NTICD.timingSolvedF3dependence g
                           alternativetdep = NTICD.alternativeTimingSolvedF3dependence g
                       in  alternativetdep == tdep,
    -- testProperty  "timingSolvedF3sparseDependence is intransitive for graphs with unique end Node"
    --             $ \(ARBITRARY(generatedGraph)) ->
    --                    let (_, g) = withUniqueEndNode () () generatedGraph
    --                        tdepsparse= NTICD.timingSolvedF3sparseDependence g
    --                    in  (∀) (Map.assocs tdepsparse) (\(n,n's) ->
    --                          (∀) (n's) (\n' ->
    --                            (∀) (tdepsparse ! n') (\n'' -> not $ n'' ∈ n's)
    --                          )
    --                        ),
    -- testProperty  "timingSolvedF3sparseDependence is intransitive for  For-Programs, which by construction are reducible"
    --             $ \generated ->
    --                    let p = toProgram generated  :: Program Gr
    --                        g = tcfg p
    --                        tdepsparse = NTICD.timingSolvedF3sparseDependence g
    --                    in  (∀) (Map.assocs tdepsparse) (\(n,n's) ->
    --                          (∀) (n's) (\n' ->
    --                            (∀) (tdepsparse ! n') (\n'' -> not $ n'' ∈ n's)
    --                          )
    --                        ),
    testProperty  "timingSolvedF3sparseDependence^*    == timingSolvedF3dependence ∪ {(n,n) | n ∈ nodes}"
                $ \(ARBITRARY(g)) ->
                       let tdep             = NTICD.timingSolvedF3dependence g
                           tdepsparse       = NTICD.timingSolvedF3sparseDependence g
                       in (trc $ fromSuccMap $ tdepsparse :: Gr () ()) ==
                          (      fromSuccMap $ tdep ⊔ Map.fromList [(n, Set.fromList [n]) | n <- nodes g ]),
    testProperty  "timingSolvedF3dependence ⊑ timingF3dependence"
                $ \(ARBITRARY(g)) ->
                       NTICD.timingSolvedF3dependence g ⊑
                       NTICD.timingF3dependence       g,
    testProperty  "timingF3dependence       ⊑ timingDependence"
                $ \(ARBITRARY(g)) ->
                       let gCfg = emap (\() -> NoOp) g in
                       NTICD.timingF3dependence       g ⊑
                             timingDependence         gCfg
  ]

timingDepTests = testGroup "(concerning timingDependence)" $
  [ testCase ("timdomOfTwoFinger        relates to timingF3EquationSystem for" ++ exampleName) $
                       let timingEqSolved    = NTICD.solveTimingEquationSystem $ NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem
                           timdomOfTwoFinger = NTICD.timdomOfTwoFinger g
                           mustReachFromIn   = reachableFromIn $ NTICD.withPossibleIntermediateNodesFromiXdom g $ timdomOfTwoFinger
                           mustReachFrom x   = suc imdomTrc x
                             where imdom    = NTICD.imdomOfTwoFinger7 g
                                   imdomTrc = trc $ fromSuccMap imdom :: Gr () ()
                       in  (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in ((m /= p) ∧ (∀) (suc g p) (\x -> m ∊ mustReachFrom x)) →
                                  case rmq of
                                     NTICD.FixedSteps s            -> Set.fromList [1+s] == mustReachFromIn p m
                                     NTICD.FixedStepsPlusOther s y -> Set.fromList [1+s] == mustReachFromIn p y
                                     NTICD.UndeterminedSteps       -> Set.fromList []    == mustReachFromIn p m
                           )
    @? ""
  | (exampleName, g) <- interestingTimingDep
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
    testProperty  "alternative implementation of  pre*[at(m2) ∩ pre*[at(m3)]] " $
      \(INTERCFG(cfg)) seed seed' ->
                     let  at = inNode cfg
                          k         = 100
                          language  = Set.fromList [ n | (_,n) <- labNodes cfg ]
                          ms        = sampleFrom seed 5 (nodes cfg)
                     in traceShow (length $ nodes cfg) $
                        (∀) ms (\m2 -> (∀) ms (\m3 ->
                          let pre     = preStar cfg (at m3)
                              prepreAt  = FA.simplify $ preStar cfg $ FA.simplifyModInitial False  $ FA.intersectWithCommonInitialNodes     (at m2) pre
                              prepreAt' = FA.simplify $ preStar cfg $                                inNodeAnd                          cfg     m2  pre
                              words   = FA.sampleWordsFor seed  language k prepreAt
                              words'  = FA.sampleWordsFor seed' language k prepreAt'
                          in (∀) (words ++ words') (\(m1,stack) -> -- traceShow ((m1,stack), m2, m3) $
                                 (not $ null $ FA.acceptsIn prepreAt  m1 stack)
                               ∧ (not $ null $ FA.acceptsIn prepreAt' m1 stack)
                             )
                        )),
    testProperty  "alternative implementation of  at(m2) ∩ pre*[at(m3)] " $
      \(INTERCFG(cfg)) seed seed' ->
                     let  at = inNode cfg
                          k         = 100
                          language  = Set.fromList [ n | (_,n) <- labNodes cfg ]
                          ms        = sampleFrom seed 5 (nodes cfg)
                     in traceShow (length $ nodes cfg) $
                        (∀) ms (\m2 -> (∀) ms (\m3 ->
                          let pre     = preStar cfg (at m3)
                              preAt   = FA.simplify $ FA.intersectWithCommonInitialNodes     (at m2) pre
                              preAt'  = FA.simplify $ inNodeAnd                          cfg     m2  pre
                              words   = FA.sampleWordsFor seed  language k preAt
                              words'  = FA.sampleWordsFor seed' language k preAt'
                          in (∀) (words ++ words') (\(m1,stack) -> -- traceShow ((m1,stack), m2, m3) $
                                 (not $ null $ FA.acceptsIn preAt  m1 stack)
                               ∧ (not $ null $ FA.acceptsIn preAt' m1 stack)
                             )
                        )),
    testProperty  "finite context graphs"      $
      \(INTERCFG(g)) ->
                     let  (folded, nodemap) = krinkeSCC g
                     in traceShow (length $ nodes g, length $ nodes folded) $
                        (∀) (nodes folded) (\n -> (Map.size $ contextGraphFrom folded n) >= 0),
    testProperty  "classification loops in krinkeSCC graphs"      $
      \(INTERCFG(g)) seed ->
                     let  (folded, nodemap) = krinkeSCC g
                          maxlength = 50
                          k         = 1000
                          paths     = samplePathsFor seed k maxlength folded
                     in traceShow (length $ nodes g, length $ nodes folded) $
                        (∀) paths (\path ->
                          (∀) (loopsIn path) (\loop -> (sameLevelArbitrary loop) ∨ (not $ realizableArtbitrary loop))
                        )
    -- testProperty  "sccIsSccNaive"                     $ sccIsSccNaive,
    -- testProperty  "sccIsSameLevelScc"                 $ sccIsSameLevelScc,
    -- testProperty  "simulUnbrIsUnbr"                   $ simulUnbrIsUnbr,
    -- testProperty  "simulUnblIsUnbl"                   $ simulUnblIsUnbl,
    -- testProperty  "simulUnbr'IsUnbr"                  $ simulUnbrIsUnbr,
    -- testProperty  "simulUnbl'IsUnbl"                  $ simulUnblIsUnbl,
    -- testProperty  "balancedChopIsSimulBalancedChop"   $ balancedChopIsSimulBalancedChop,
    -- testProperty  "chopsInterIDomAreChops"            $ chopsInterIDomAreChops,
    -- testProperty  "sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs" $ sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs
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


indepsProps = testGroup "(concerning dependencey graph representations using independencies)" [
    testProperty "addNonImplicitNonTrivialSummaryEdgesGfpLfp  =~   addNonImplicitNonTrivialSummaryEdges"
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
    testProperty "nonImplicitSummaryComputation is correct"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        pdg = programDependenceGraphP p
                        (cfg, parameterMaps) = withParameterNodes p
                        sdg                     = addSummaryEdges              parameterMaps pdg
                        (nonImplicitNonTrivialSummariesSdg, summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)  = addNonImplicitNonTrivialSummaryEdges p parameterMaps pdg
                        sdg'                    = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps summaryIndependencies formalInActualInInIndependencies actualOutFormalOutIndependencies nonImplicitNonTrivialSummariesSdg
                        summaries                       = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges sdg                              ]
                        summariesNonImplicitNonTrivial  = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSummariesSdg]
                    in traceShow ("SummaryGraph: ", Set.size summaries, "\t\t", "NonImplicitSummaryGraph: ", Set.size summariesNonImplicitNonTrivial) $
                       sdg == sdg'
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
    -- testProperty "summaryIndepsProperty"
    --             $ \generated ->
    --                 let p   :: Program Gr = toProgram generated
    --                 in summaryIndepsPropertyViolations p == [],
    -- testProperty "summaryComputation                      =~  summaryComputationGfpLfpWorkList"
    --             $ \generated ->
    --                 let p   :: Program Gr = toProgram generated
    --                     (cfg, parameterMaps) = withParameterNodes p
    --                     pdg = programDependenceGraphP p
    --                     sdg               = addSummaryEdges                 parameterMaps pdg
    --                     sdgGfpLfpWorkList = addSummaryEdgesGfpLfpWorkList p parameterMaps pdg
    --                 in traceShow (length $ nodes cfg, length $ [ () | (_,_,SummaryDependence) <- labEdges sdg]) $
    --                                                   sdg == sdgGfpLfpWorkList
  --   testProperty "summaryComputation                      =~  summaryComputationGfpLfp"
  --               $ \generated ->
  --                   let p   :: Program Gr = toProgram generated
  --                       (_, parameterMaps) = withParameterNodes p
  --                       pdg = programDependenceGraphP p
  --                   in addSummaryEdges parameterMaps pdg  == addSummaryEdgesGfpLfp p parameterMaps pdg,
    -- testProperty "summaryComputation                      =~  summaryComputationLfp"
    --             $ \generated ->
    --                 let p   :: Program Gr = toProgram generated
    --                     (_, parameterMaps) = withParameterNodes p
    --                     pdg = programDependenceGraphP p
    --                 in addSummaryEdges parameterMaps pdg  == addSummaryEdgesLfp parameterMaps pdg
  --   testProperty "dataDependenceGraphViaIndependenceP     == dataDependenceGraphP"
  --               $ \generated -> let  p :: Program Gr = toProgram generated in
  --                 dataDependenceGraphViaIndependenceP p   == dataDependenceGraphP p
  ]
indepsTests = testGroup "(concerning color algorithms)" $
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



miscProps = testGroup "(misc)" [
    testProperty  "trcOfTrrIsTrc"                     $ trcOfTrrIsTrc,
    testProperty  "snmF4WithReachCheckGfp == snmF3Gfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let graph     = generatedGraph
                        snmF3Gfp                = NTICD.snmF3 graph
                        snmF4WithReachCheckGfp  = NTICD.snmF4WithReachCheckGfp graph
                    in snmF4WithReachCheckGfp ⊑ snmF3Gfp
  ]


testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

