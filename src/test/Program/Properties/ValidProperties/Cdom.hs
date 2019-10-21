{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Cdom where

import Program.Properties.Util

import Prelude hiding (all)

import Data.Graph.Inductive.Dot (showDot, fglToDotGeneric)
import Control.Monad.Random (randomR, getStdRandom)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)
import Control.Exception.Base (assert)

import Algebra.Lattice
import Unicode

import Program.Properties.Util

import Util(the, reachableFromIn, sampleFrom, moreSeeds, toSet, evalBfun, isReachableFromTree, reachableFromTree, foldM1, fromSet,reachableFrom, restrict, invert''', (≡), findCyclesM, treeLevel, minimalPath,  pathsUpToLength, invert'', minimalPathForReachable, more)
import Test.Tasty
import Test.Tasty.Providers (singleTest)
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)

import Test.Tasty.Runners.AntXML
import Test.Tasty.Ingredients.Basic

import Test.QuickCheck (Testable, property)
import Test.QuickCheck.Property (Property(..))

import Data.Ord

import Debug.Trace (traceShow, trace)

import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)
import Data.Dequeue.SimpleDequeue (SimpleDequeue)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Tree as Tree

import Data.Word
import Data.Ord (Down(..))
import Data.List (sortOn)
import Data.Map ( Map, (!) )
import Data.Maybe(fromJust)

import IRLSOD(CFGEdge(..), Var(..), Name(..), isGlobalName, globalEmpty, use, def)
import CacheExecution(twoAddressCode, prependInitialization, prependFakeInitialization, initialCacheState, cacheExecution, cacheExecutionLimit, csd''''Of3, csd''''Of4, csdMergeOf, csdMergeDirectOf, cacheCostDecisionGraph, cacheCostDecisionGraphFor, cacheStateGraph, stateSets, cacheOnlyStepFor, costsFor)
import CacheSlice (cacheTimingSliceViaReach)

import Data.Graph.Inductive.Arbitrary.Reducible
import Data.Graph.Inductive.Query.DFS (scc, dfs, rdfs, rdff, reachable, condensation)
import Data.Graph.Inductive.Query.Dominators (iDom)
import Data.Graph.Inductive.Query.TimingDependence (timingDependence, timingDependenceOld)
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trcOfTrrIsTrc, withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, removeDuplicateEdges, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)
import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, lsuc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph, delEdges, insEdge, newNodes)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.ControlDependence (controlDependenceGraphP, controlDependence)
import Data.Graph.Inductive.Query.DataDependence (dataDependenceGraphP, dataDependenceGraphViaIndependenceP, withParameterNodes, dataDependence)
import Data.Graph.Inductive.Query.ProgramDependence (programDependenceGraphP, addSummaryEdges, addSummaryEdgesLfp, addSummaryEdgesGfpLfp, addSummaryEdgesGfpLfpWorkList, summaryIndepsPropertyViolations, implicitSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdges, addImplicitAndTrivialSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdgesGfpLfp)

import qualified Data.Graph.Inductive.Query.NTIODSlice as NTIODSlice
import qualified Data.Graph.Inductive.Query.LCA as LCA (lca)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (isinkdomOf, isinkdomOfGfp2, joinUpperBound, sinkdomOfJoinUpperBound, sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkdomNaiveGfp, sinkdomNaiveGfpFullTop, sinkdomOfisinkdomProperty, imdomOf, imdomOfLfp, mdomOf, mdomOfLfp, mdomNaiveLfp, mdomOfimdomProperty, onedomOf, mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, isinkdomOftwoFinger8Up,  imdomOfTwoFinger6, imdomOfTwoFinger7)
import qualified Data.Graph.Inductive.Query.NTICD.Program as PROG (
    sinkDFF2GraphP, sinkDFGraphP, sinkDFFromUpLocalDefGraphP, sinkDFFromUpLocalGraphP,
       mDFF2GraphP,    mDFGraphP,    mDFFromUpLocalDefGraphP,    mDFFromUpLocalGraphP,
    nticdSinkContractionGraphP,
    nticdDefGraphP, ntscdDefGraphP,
    nticdF3GraphP, nticdF3'GraphP, nticdF3'dualGraphP,
    nticdF3WorkListGraphP,
    nticdF3WorkListSymbolicGraphP, nticdF3'dualWorkListSymbolicGraphP, nticdFig5GraphP, nticdF5GraphP,  nticdF3'dualWorkListGraphP,
    ntscdF4GraphP, ntscdF3GraphP, ntscdF4WorkListGraphP,
    ntacdDefGraphP,
  )
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (
    isinkDFTwoFinger, mDFTwoFinger,  noJoins, stepsCL,
    sinkDFF2cd,  sinkDFcd,  sinkDFFromUpLocalDefcd, sinkDFFromUpLocalcd,  isinkdomTwoFingercd,
    sinkDFUp, sinkDFUpDef, sinkDFUpDefViaSinkdoms,
    sinkDFLocal, sinkDFLocalDef, sinkDFLocalViaSinkdoms, sinkDFUpGivenX, sinkDFUpGivenXViaSinkdoms,
    sinkDFFromUpLocalDefViaSinkdoms, sinkDF,
    idomToDF, idomToDFFast,
    mDFF2cd,        mDFcd,       mDFFromUpLocalDefcd,         mDFFromUpLocalcd,         imdomTwoFingercd,
    mDFUp, mDFUpDef, mDFUpDefViaMdoms, mDFUpGivenXViaMdoms,
    mDFLocal, mDFLocalDef, mDFLocalViaMdoms, mDFUpGivenX, 
    mDFFromUpLocalDefViaMdoms, mDF,
 )
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges as CEDGE (nticdSliceNumberedViaCEdgesFast, ntscdSliceViaCEdgesFast, dfViaCEdges, idfViaCEdgesFast, nticdSliceViaCEdgesFast, nticdSliceViaCEdgesFastFor)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers.Numbered as PDFNumbered (nticdSliceNumbered)
import qualified Data.Graph.Inductive.Query.FCACD as FCACD (wccSlice, wdSlice, nticdNTIODViaWDSlice, wodTEILSliceViaBraunF2)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (delayedInfinitely, sampleLoopPathsFor, isTracePrefixOf, sampleChoicesFor, Input(..), infinitelyDelays, runInput, observable, allChoices, isAscending, isLowEquivalentFor, isLowTimingEquivalent, isLowEquivalentTimed)
import qualified Data.Graph.Inductive.Query.PostDominance.Numbered as PDOMNumbered (iPDom, pdom, numberForest)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import qualified Data.Graph.Inductive.Query.Util.GraphTransformations as TRANS (sinkShrinkedGraphNoNewExitForSinks)
import qualified Data.Graph.Inductive.Query.NTICD.GraphTransformations as NTICD.TRANS (nticdSinkContraction)
import qualified Data.Graph.Inductive.Query.PostDominance.GraphTransformations as PDOM.TRANS (isinkdomOfSinkContraction)
import qualified Data.Graph.Inductive.Query.Slices.GraphTransformations as SLICE.TRANS (
    nticdNTIODSliceViaCutAtRepresentatives, nticdNTIODSliceViaEscapeNodes, nticdNTIODSliceViaCutAtRepresentativesNoTrivial, nticdNTIODSliceViaChoiceAtRepresentatives
 )
import qualified Data.Graph.Inductive.Query.Slices.PostDominance as SLICE.PDOM (nticdNTIODSliceViaISinkDom, ntscdNTSODSliceViaIMDom)
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (
    nticdNTIODSlice, nticdSlice,  ntscdSlice,
    ntscdNTSODSliceViaNtscd, wodTEILSliceViaNticd,
    wccSliceViaNticd,
  )
import qualified Data.Graph.Inductive.Query.Slices.OrderDependence as SLICE.ODEP (
    nticdNTIODFastSlice, wodTEILPDomSlice, 
    ntiodFastPDomSimpleHeuristicSlice, ntiodFastSlice, nticdNTIODSlice, wodTEILSlice, ntscdDodSlice, ntscdNTSODSlice, ntscdNTSODFastPDomSlice, 
    wccSliceViaNticdNTIODPDomSimpleHeuristic, nticdNTIODPDomSimpleHeuristic,
  )
import qualified Data.Graph.Inductive.Query.Slices.PostDominanceFrontiers as SLICE.PDF (nticdSliceFor)
import qualified Data.Graph.Inductive.Query.PathsBetween as PBETWEEN (
    pathsBetweenBFS, pathsBetweenUpToBFS,
    pathsBetween,    pathsBetweenUpTo,
  )
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    nticdViaSinkDom,
    ntscdViaMDom,
    ntindDef, ntsndDef,
    nticdDef, 
    ntscdDef, 
  )
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, 
    nticdF3'dualWorkList, snmF3'dual,
    ntscdF4, ntscdF3, ntscdF4WorkList
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
     mustOfLfp, mustOfGfp, mmayOf, mmayOf', rotatePDomAround, Color(..), smmnFMustDod, smmnFMustWod, colorLfpFor, colorFor,
    smmnGfp, smmnLfp, fMust, fMustBefore, fMustNoReachCheck,
    dod, dodDef, dodFast, dodColoredDagFixed, dodColoredDagFixedFast,
    ntiod, ntiodFast, ntiodFastPDom, ntiodFastPDomSimpleHeuristic,  ntsod, ntsodFast, ntsodFastPDom, wodTEIL', wodTEIL'PDom, wodDef, wodFast, fMay, fMay'
  )
import qualified Data.Graph.Inductive.Query.NTICDUnused  as NTICDUnused (ntacdDef, wodMyEntryWodMyCDSlice, myCD, myCDFromMyDom, myDom, allDomNaiveGfp, ntiodFromMay, mayNaiveGfp, possibleIntermediateNodesFromiXdom, withPossibleIntermediateNodesFromiXdom)
import qualified Data.Graph.Inductive.Query.TSCD         as TSCD (timdomsOf, timingCorrection, timingLeaksTransformation, tscdCostSlice, timDFCostFromUpLocalDefViaTimdoms, timDFCost, tscdOfLfp, timDF, timDFFromUpLocalDefViaTimdoms, timDFUpGivenXViaTimdomsDef, timDFUpGivenXViaTimdoms, timDFLocalDef, timDFLocalViaTimdoms, tscdOfNaiveCostfLfp, timdomOfLfp, tscdSlice, timdomsFromItimdomMultipleOf, validTimdomFor, validTimdomLfp,
    itimdomMultipleOfTwoFingerCost, cost1, cost1F,
    itimdomMultipleTwoFingercd, timDFFromFromItimdomMultipleOf,
    timdomOfNaiveLfp, timdomMultipleOfNaiveLfp,
    timDFFromFromItimdomMultipleOfFast, timDFFromFromItimdomMultipleOfFastCost, itimdomMultipleOfTwoFinger, timdomOfTwoFinger, tscdSliceFast, tscdSliceViaTimDF, timMultipleDFTwoFinger)
import qualified Data.Graph.Inductive.Query.PureTimingDependence as PTDEP (alternativeTimingSolvedF3dependence, timingSolvedF3dependence, timingF3dependence, timingF3EquationSystem', timingF3EquationSystem, snmTimingEquationSystem, timingSolvedF3sparseDependence, timingSnSolvedDependence, timingSnSolvedDependenceWorklist, timingSnSolvedDependenceWorklist2, enumerateTimingDependence, solveTimingEquationSystem, Reachability(..), timmaydomOfLfp, timingDependenceViaTwoFinger, nticdTimingSlice, ntscdTimingSlice, ptd, timingDependenceFromTimdom)

import qualified Data.Graph.Inductive.FA as FA


import Data.Graph.Inductive.Arbitrary


import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.DynamicAnalysis (isSecureEmpirically, isLSODEmpirically)

import Program.MHP (mhpSetFor, mhpDifferent, mhpDifferentSlow)
import Program.Properties.Analysis
import Program.Properties.CDom
import Data.Graph.Inductive.Query.BalancedSCC -- TODO: refactor that module into 2 seperate modules

import Execution (allFinishedExecutionTraces, someFinishedAnnotatedExecutionTraces)
import Program.Examples (insecure, testsuite, interproceduralTestSuit, precisionCounterExamples, interestingDodWod, interestingTimingDep, syntacticCodeExamples, code2ResumptionForProgram, code2Program, interestingIsinkdomTwoFinger, interestingImdomTwoFinger, exampleTooCoarseAbstractionIsUnsound)
import qualified ReferenceCrypto (runAES256)
import qualified Program.ExamplesCrypto (runAES256, runAES256_ct)
import Program.Defaults (defaultInput)
import Program.Analysis
import Program.Typing.FlexibleSchedulerIndependentChannels (isSecureFlexibleSchedulerIndependentChannel)
import Program.Typing.ResumptionBasedSecurity (Criterion(..), isSecureResumptionBasedSecurity, isSecureResumptionBasedSecurityFor)
import Program.CDom
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.For (compileAllToProgram)

cdom       = defaultMain                               $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
cdomX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]



cdomCdomProps = testGroup "(concerning cdoms)" $
  [ testPropertySized 20 ("idomChef                isMorePreciceThan idomMohrEtAlNoCycleTest")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     mpThan = isMorePreciceThan p
                                in idomChef `mpThan` idomMohrEtAlNoCycleTest
  ] ++
  [ testPropertySized 20 ("idomMohrEtAlNoCycleTest isMorePreciceThan idomBischof")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     mpThan = isMorePreciceThan p
                                in idomMohrEtAlNoCycleTest `mpThan` idomBischof
  ] ++
  [ testPropertySized 20 ("idomBischof             isMorePreciceThan idomMohrEtAl")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     mpThan = isMorePreciceThan p
                                in idomBischof `mpThan` idomMohrEtAl
  ] ++
  [ testPropertySized 10 ("isCdom idomMohrEtAl")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                in isCdom p idomMohrEtAl
  ] ++
  [ testPropertySized 10 ("isCdom  idomBischof")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                in isCdom p idomBischof
  ] ++
  [ testPropertySized 10 ("cdomIsCdom idomChef")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations p execs idomChef == []
  ] ++
  [ testPropertySized 10 ("cdomIsCdom idomMohrEtAl")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations p execs idomMohrEtAl == []
  ] ++
  [ testPropertySized 10 ("cdomIsCdom idomMohrEtAlNoCycleTest")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations p execs idomMohrEtAlNoCycleTest == []
  ] ++
  [ testPropertySized 10 ("cdomIsCdom idomBischof")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations p execs idomBischof == []
  ] ++
  [ testPropertySized 10 ("cdomIsCdom' idomMohrEtAl")
                $ \generated -> let  p :: Program Gr = toProgramIntra generated
                                     execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
                                in cdomIsCdomViolations' p execs idomMohrEtAl == []
  ] ++
  []


cdomCdomTests = testGroup "(concerning cdoms)" $
  [ testCase ("idomChef                isMorePreciceThan idomMohrEtAlNoCycleTest  for "  ++ exampleName)
                $ 
                                let mpThan = isMorePreciceThan p
                                in idomChef `mpThan` idomMohrEtAlNoCycleTest @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("idomMohrEtAlNoCycleTest isMorePreciceThan idomBischof              for "  ++ exampleName)
                $               let mpThan = isMorePreciceThan p
                                in idomMohrEtAlNoCycleTest `mpThan` idomBischof @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("idomBischof             isMorePreciceThan idomMohrEtAl             for "  ++ exampleName)
                $               let mpThan = isMorePreciceThan p
                                in idomBischof `mpThan` idomMohrEtAl @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("isCdom idomMohrEtAl            for " ++ exampleName) $  isCdom p idomMohrEtAl @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("isCdom idomBischof             for " ++ exampleName) $  isCdom p idomBischof @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("cdomIsCdom idomChef for " ++ exampleName) $                 (cdomIsCdomViolations  p execs idomChef) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  [ testCase ("cdomIsCdom idomMohrEtAl for " ++ exampleName) $             (cdomIsCdomViolations  p execs idomMohrEtAl) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  [ testCase ("cdomIsCdom idomMohrEtAlNoCycleTest for " ++ exampleName)  $ (cdomIsCdomViolations  p execs idomMohrEtAlNoCycleTest) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  [ testCase ("cdomIsCdom idomBischof for " ++ exampleName) $              (cdomIsCdomViolations  p execs idomBischof) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  [ testCase ("cdomIsCdom' idomMohrEtAl for " ++ exampleName) $            (cdomIsCdomViolations' p execs idomMohrEtAl) == [] @? ""
  | (exampleName, p) <- testsuite, let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  []

cdomProps = testGroup "(concerning Chops between cdoms and the nodes involved)" [
    testPropertySized 40  "domMhpProperty"                               $ (\generated ->  let p = toProgramIntra generated :: Program Gr in domMhpProperty p),
    testPropertySized 40  "idomIsTreeProgram idomChef"                   $ idomIsTreeProgram idomChef,
    testPropertySized 40  "idomIsTreeProgram idomBischof"                $ (\generated ->  let p = toProgramIntra generated :: Program Gr in idomIsTreeProgram idomBischof p),
    testPropertySized 80  "idomIsTreeProgram idomMohrEtAl"                $ idomIsTreeProgram idomMohrEtAl,
    testPropertySized 80  "idomIsTreeProgram idomMohrEtAlNoCycleTest"     $ idomIsTreeProgram idomMohrEtAlNoCycleTest,
    testPropertySized 10  "chopsCdomArePrefixes idomChef"                 $ chopsCdomArePrefixes idomChef,
    testPropertySized 10  "chopsCdomArePrefixes idomBischof"              $ chopsCdomArePrefixes idomBischof,
    testPropertySized 10  "chopsCdomArePrefixes idomMohrEtAl"             $ chopsCdomArePrefixes idomMohrEtAl,
    testPropertySized 10  "chopsCdomArePrefixes idomMohrEtAlNoCycleTest"  $ chopsCdomArePrefixes idomMohrEtAlNoCycleTest,
    testPropertySized 60  "idomChefTreeIsDomTree"              $ idomChefTreeIsDomTree,
    testPropertySized 10  "chopsCdomAreExclChops idomChef"     $ chopsCdomAreExclChops idomChef,
    testPropertySized 10  "chopsCdomAreExclChops idomBischof"  $ chopsCdomAreExclChops idomBischof,
    testPropertySized 10  "chopsCdomAreExclChops idomMohrEtAl"            $ chopsCdomAreExclChops idomMohrEtAl,
    testPropertySized 10  "chopsCdomAreExclChops idomMohrEtAlNoCycleTest" $ chopsCdomAreExclChops idomMohrEtAlNoCycleTest,
    testPropertySized 10  "inclChopIsChop"                     $ inclChopIsChop,
    testPropertySized 10  "exclChopContainedinclChop"          $ exclChopContainedinclChop,
    testPropertySized 70  "selfChopsSame"                      $ selfChopsSame,
    testProperty          "selfChopsSCC"                       $ selfChopsSCC
  ]

cdomTests = testGroup "(concerning Chops between cdoms and the nodes involved)" $
  [ testCase ("chopsCdomArePrefixes idomChef for " ++ exampleName)  $ chopsCdomArePrefixes idomChef p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomArePrefixes idomBischof for " ++ exampleName)  $ chopsCdomArePrefixes idomBischof p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomArePrefixes idomMohrEtAl for " ++ exampleName)  $ chopsCdomArePrefixes idomMohrEtAl p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomArePrefixes idomMohrEtAlNoCycleTest for " ++ exampleName)  $ chopsCdomArePrefixes idomMohrEtAlNoCycleTest p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("idomChefTreeIsDomTree for " ++ exampleName)  $ idomChefTreeIsDomTree p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomAreExclChops idomChef for " ++ exampleName)  $ chopsCdomAreExclChops idomChef p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomAreExclChops idomBischof for " ++ exampleName)  $ chopsCdomAreExclChops idomBischof p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomAreExclChops idomMohrEtAl for " ++ exampleName)  $ chopsCdomAreExclChops idomMohrEtAl p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomAreExclChops idomMohrEtAlNoCycleTest for " ++ exampleName)  $ chopsCdomAreExclChops idomMohrEtAlNoCycleTest p @? ""
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
