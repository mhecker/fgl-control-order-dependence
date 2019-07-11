{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

-- #define USEUNCONNECTED
#ifdef USEUNCONNECTED
#define ARBITRARY(g) (g) :: (Gr () ())
#else
#define ARBITRARY(g) (CG _ g) :: (Connected Gr () ())
#endif

#define UNCONNECTED(g) (g) :: (Gr () ())
#define CONNECTED(g) (CG _ g) :: (Connected Gr () ())
#define REDUCIBLE(g) (RedG g) :: (Reducible Gr () ())
#define INTER(g) (InterGraph g) :: (InterGraph () String)
#define INTERCFG(g) (InterCFG _ g) :: (InterCFG (Node) (Node, Node))
#define SIMPLECFG(g) (SimpleCFG g) :: (SimpleCFG Gr)

module Program.Properties.ValidProperties where

import Prelude hiding (all)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)
import Control.Exception.Base (assert)

import Algebra.Lattice
import Unicode

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

import Data.Ord (Down(..))
import Data.List (sortOn)
import Data.Map ( Map, (!) )
import Data.Maybe(fromJust)

import IRLSOD(CFGEdge(..), Var(..), use, def)
import CacheExecution(prependInitialization, initialCacheState, cacheExecution, cacheExecutionLimit, csdOfLfp, csd'Of, csd''''Of3, cacheCostDecisionGraph)

import Data.Graph.Inductive.Arbitrary.Reducible
import Data.Graph.Inductive.Query.DFS (scc, dfs, rdfs, rdff, reachable, condensation)
import Data.Graph.Inductive.Query.Dominators (iDom)
import Data.Graph.Inductive.Query.TimingDependence (timingDependence)
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trcOfTrrIsTrc, withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, removeDuplicateEdges, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode',)
import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph, delEdges, insEdge, newNodes)
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
    timDFFromFromItimdomMultipleOfFast, timDFFromFromItimdomMultipleOfFastCost, itimdomMultipleOfTwoFinger, timdomOfTwoFinger, tscdSliceFast, tscdSliceViaTimDF)
import qualified Data.Graph.Inductive.Query.PureTimingDependence as PTDEP (alternativeTimingSolvedF3dependence, timingSolvedF3dependence, timingF3dependence, timingF3EquationSystem', timingF3EquationSystem, snmTimingEquationSystem, timingSolvedF3sparseDependence, timingSnSolvedDependence, timingSnSolvedDependenceWorklist, timingSnSolvedDependenceWorklist2, enumerateTimingDependence, solveTimingEquationSystem, Reachability(..), timmaydomOfLfp, timingDependenceViaTwoFinger, nticdTimingSlice, ntscdTimingSlice)

import qualified Data.Graph.Inductive.FA as FA


import Data.Graph.Inductive.Arbitrary


import Program (Program, tcfg, entryOf, procedureOf, mainThread)
import Program.DynamicAnalysis (isSecureEmpirically)

import Program.Properties.Analysis
import Program.Properties.CDom
import Data.Graph.Inductive.Query.BalancedSCC -- TODO: refactor that module into 2 seperate modules

import Execution (allFinishedExecutionTraces, someFinishedAnnotatedExecutionTraces)
import Program.Examples (insecure, testsuite, interproceduralTestSuit, precisionCounterExamples, interestingDodWod, interestingTimingDep, syntacticCodeExamples, code2ResumptionForProgram, code2Program, interestingIsinkdomTwoFinger, interestingImdomTwoFinger)
import Program.Defaults (defaultInput)
import Program.Analysis
import Program.Typing.FlexibleSchedulerIndependentChannels (isSecureFlexibleSchedulerIndependentChannel)
import Program.Typing.ResumptionBasedSecurity (Criterion(..), isSecureResumptionBasedSecurity, isSecureResumptionBasedSecurityFor)
import Program.CDom
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, GeneratedProgram, SimpleCFG(..))

import Program.For (compileAllToProgram)

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
nticd      = defaultMain                               $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]
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

delay     = defaultMain                               $ testGroup "delay"    [ mkTest [delayTests], mkProp [delayProps]]
delayX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "delay"    [ mkTest [delayTests], mkProp [delayProps]]

cache     = defaultMain                               $ testGroup "cache"    [                      mkProp [cacheProps]]
cacheX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "cache"    [                      mkProp [cacheProps]]


long     = defaultMain                               $ testGroup "long"    [ mkTest [longTests], mkProp [longProps]]
longX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "long"    [ mkTest [longTests], mkProp [longProps]]

  


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
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps, cdomProps, cdomCdomProps, balancedParanthesesProps, soundnessProps                              , nticdProps, ntscdProps, insensitiveDomProps, sensitiveDomProps, timingDepProps, dodProps, wodProps, colorProps, reducibleProps, indepsProps, simonClassificationProps, newcdProps, delayProps, cacheProps]
  where missing = [longProps]
unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests, cdomTests, cdomCdomTests, balancedParanthesesTests, soundnessTests, precisionCounterExampleTests, nticdTests, ntscdTests, insensitiveDomTests, sensitiveDomTests, timingDepTests, dodTests, wodTests, colorTests                , indepsTests, simonClassificationTests, newcdTests, delayTests]
  where missing = [longTests]


longProps = testGroup "(long running)" [
    testPropertySized 25 "nticdNTIODFastSlice  is sound"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        s = SLICE.ODEP.nticdNTIODFastSlice g (Set.fromList [m1, m2])
                        infinitelyDelays = InfiniteDelay.infinitelyDelays g s
                        runInput         = InfiniteDelay.runInput         g
                        observable       = InfiniteDelay.observable         s
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentFor infinitelyDelays runInput observable input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in (if not $ different then id else traceShow (m1,m2, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (if not $ differentobservation then id else traceShow (m1, m2, differentobservation)) $
                       not differentobservation,
    testPropertySized 15   "timingClassificationAtUses is at least as precise as resumptionBasedSecurity"
                $ isSecureTimingClassificationAtUses `isAtLeastAsPreciseAsPartialGen`  (isSecureResumptionBasedSecurity ZeroOneBisimilarity),
    testPropertySized 25 "nticdNTIODSlice is termination sensitively sound for always-terminating graphs"
    $ \(ARBITRARY(generatedGraph)) ->
                let     g   = removeDuplicateEdges $ efilter (\(n,m,_) -> n /= m) $ condensation generatedGraph
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        slicer     = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                        -- slicer     = NTICD.wodTEILPDomSlice g
                        ss         = Set.fromList [ slicer (Set.fromList [m1, m2]) | m1 <- nodes g, m2 <- nodes g ]
                        runInput   = InfiniteDelay.runInput         g
                    in -- traceShow (n, Set.size ss) $
                       (∀) ss (\s ->
                         -- traceShow s $
                         let observable   = InfiniteDelay.observable s
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                     in (if not $ different then id else traceShow (s, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                         in not differentobservation
                    )
  ]

longTests =  testGroup "(long running)" $ [
  ] ++
  []


soundnessProps =  testGroup "(concerning soundness)" [
    testPropertySized 3
     ("isSound  isSecureResumptionBasedSecurity")
     (isSoundPartialGen $ isSecureResumptionBasedSecurity ZeroOneBisimilarity),
    testPropertySized 10
     ("allSoundIntraMulti [ timingClassificationAtUses, timingClassificationDomPaths, timingClassification, timingClassificationSimple,  timingClassificationIdomBischof, minimalClassification, giffhornLSOD, simonClassification ] ")
     ( allSoundIntraMulti [ isSecureTimingClassificationAtUses, isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureTimingClassificationIdomBischof, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification ] )
  ]

soundnessTests =  testGroup "(concerning soundness)" $
  [ testCase      ("allSoundP [ timingClassificationDomPaths, timingClassification, timingClassificationSimple, timingClassificationIdomBischof, minimalClassification, giffhornLSOD, simonClassification ] for " ++ exampleName)
                  ( allSoundP [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureTimingClassificationIdomBischof, isSecureMinimalClassification, giffhornLSOD, isSecureSimonClassification ] example @? "")
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
    testPropertySized 30  "timingClassificationAtUses is at least as precise as FlexibleSchedulerIndependence"
                $ \generated -> let  p :: Program Gr = toProgramIntra generated in
                isSecureTimingClassificationAtUses p ⊒ isSecureFlexibleSchedulerIndependentChannel generated,
    testPropertySized 30  "timingClassificationDomPaths == timingClassification"
                  timingDDomPathsIsTimingG,
    testPropertySized 30  "timingClassificationDomPaths is at least as precise as timingClassificationSimple"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureTimingClassificationSimple,
    testPropertySized 30  "timingClassificationAtUses is at least as precise as minimalClassification"
                $ isSecureTimingClassificationAtUses `isAtLeastAsPreciseAs` isSecureMinimalClassification,
    testPropertySized 30  "timingClassificationAtUses is at least as precise as timingClassificationDomPaths"
                $ isSecureTimingClassificationAtUses `isAtLeastAsPreciseAs` isSecureTimingClassificationDomPaths,
    testPropertySized 30  "timingClassificationDomPaths is at least as precise as giffhornLSOD"
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
    testPropertySized 20  "simonClassification is at least as precise as minimalClassification"
                $ isSecureSimonClassification `isAtLeastAsPreciseAs` isSecureMinimalClassification
  ]

simonClassificationTests = testGroup "(concerning simonClassification)" $
  [ testCase     ("simonClassification is at least as precise as minimalClassification for " ++ exampleName)
                ((isSecureSimonClassification example ⊒ isSecureMinimalClassification example) @? "")
  | (exampleName, example) <- testsuite
  ] ++
  []

giffhornProps = testGroup "(concerning Giffhorns LSOD)" [
    testPropertySized 45  "giffhornLSOD == isSecureGiffhornClassification for procedure-less programs"
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
  [  testCase    ("giffhornLSOD == isSecureGiffhornClassification for " ++ exampleName)
                $ giffhornLSOD p == isSecureGiffhornClassification p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []


insensitiveDomProps = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" [
    testProperty   "nticdViaSinkDom          == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdViaSinkDom g ==
                       SNM.nticdF3          g,
    testPropertySized 20 "sinkdom g_{M/->}^{M->*} ⊆ (sinkdom g)|{M->*}"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 -> let ms = [m1,m2,m3] in
                         let fromMs = dfs ms g
                             g' = foldr (flip delSuccessorEdges) (subgraph fromMs g) ms
                             sinkdom' = PDOM.sinkdomOfGfp g'
                         in sinkdom' ⊑ restrict sinkdom (Set.fromList fromMs)
                       ))),
    testProperty "sinkdom g^{M->*}^{M->*} ⊆ (sinkdom g)|{M->*} for random sets M of random Size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                        n  = length $ nodes g
                        ms
                         | n == 0 = []
                         | n /= 0 = [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        fromMs = dfs ms g
                        g' = foldr (flip delSuccessorEdges) (subgraph fromMs g) ms
                        sinkdom' = PDOM.sinkdomOfGfp g'
                    in sinkdom' ⊑ restrict sinkdom (Set.fromList fromMs),
    testPropertySized 20 "sinkdom g^{M->*} == (sinkdom g)|{M->*}"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                        nticd = NTICD.nticdViaSinkDom g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 -> let ms = [m1,m2,m3] in
                         let fromMs = dfs ms g
                             g' = subgraph fromMs g
                             sinkdom' = PDOM.sinkdomOfGfp g'
                             nticd' = NTICD.nticdViaSinkDom g'
                         in   sinkdom' == restrict sinkdom (Set.fromList fromMs)
                            ∧ nticd'   == restrict nticd   (Set.fromList fromMs)
                       ))),
    testProperty "sinkdom g^{M->*} == (sinkdom g)|{M->*} for random sets M of random Size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                        nticd = NTICD.nticdViaSinkDom g
                        n  = length $ nodes g
                        ms
                         | n == 0 = []
                         | n /= 0 = [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        fromMs = dfs ms g
                        g' = subgraph fromMs g
                        sinkdom' = PDOM.sinkdomOfGfp g'
                        nticd' = NTICD.nticdViaSinkDom g'
                    in   sinkdom' == restrict sinkdom (Set.fromList fromMs)
                       ∧ nticd'   == restrict nticd   (Set.fromList fromMs),
    testPropertySized 40 "stepsCL sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in PDF.stepsCL g sinkdom,
    testPropertySized 40 "noJoins sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in PDF.noJoins g sinkdom,
    testProperty   "dfs numbering properties"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        n = length $ nodes g
                        sinks = controlSinks g
                        
                        forest = rdff [ s| (s:_) <- sinks] g
                        tree = Tree.Node undefined forest
                        
                        (_, nforest) = PDOMNumbered.numberForest 1 forest
                        ntree = Tree.Node undefined nforest
                        fromNode = Map.fromList $ zip (tail $ Tree.flatten  tree) (tail $ Tree.flatten ntree)
                        toNode   = Map.fromList $ zip (tail $ Tree.flatten ntree) (tail $ Tree.flatten  tree)
                        sinkSuccs = [ (s1, s2) | sink@(_:_:_) <- sinks, let (s:sorted) = sortOn Down $ fmap (fromNode Map.!) sink, (s1,s2) <- zip (s:sorted) (sorted ++ [s]) ]
                        sinkOf        = Map.fromList [ (s, s0)  | sink@(s0:_) <- sinks, s <- sink ]
                        sinkNodes = Set.fromList [ s | sink <- sinks, s <- sink]

                        sinkdom = PDOM.sinkdomOfGfp g
                    in (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m ->
                           (       n ∈ sinkNodes   ∧  m ∈ sinkNodes  ∧  sinkOf ! n == sinkOf ! m) 
                         ∨ ((not $ n ∈ sinkNodes)  ∧  m ∈ sinkNodes  ∧  (fromNode ! (sinkOf ! m) >= fromNode ! m))
                         ∨ (fromNode ! m >= fromNode ! n)
                       )),
    testProperty   "nticdSliceNumbered  == nticdSliceNumberedViaCEdgesFast for ladder-graphs and randomly selected nodes"
    $ \(size :: Int) seed1 seed2 seed3 ->
                let n0 = (abs size) `div` 2
                    g = ladder n0  :: Gr () ()
                    idom = assert (n == 2*n0 + 3) $ 
                                       Map.fromList [(i, Just (i+2))| i <- [1,3 ..(n-3)]]
                           `Map.union` Map.fromList [(i, Nothing)   | i <- [0   ..(n-1)]]
                    roots = assert (idom == fmap fromSet (PDOM.isinkdomOfTwoFinger8 g)) $
                            fmap (\n -> [n]) $  Map.keys $ Map.filter (== Nothing) idom
                    
                    nrSlices = 1
                    n = length $ nodes g
                    mss = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    nticdslicer        = SLICE.PDF.nticdSliceFor              roots g idom
                    nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFastFor roots g idom
                in (∀) mss (\ms -> nticdslicer ms == nticdslicerCEdges ms),
    testProperty   "nticdSlice  == nticdSliceViaCEdgesFast for CFG-shaped graphs and randomly selected nodes"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 seed3 ->
  --               let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
  --                   [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
  --                   g = insEdge (exit, entry, ()) generatedGraph
                let g = generatedGraph
                    nrSlices = 10
                    n = length $ nodes g
                    mss = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    nticdslicer        = SLICE.NTICD.nticdSlice              g
                    nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                in (∀) mss (\ms -> nticdslicer ms == nticdslicerCEdges ms),
    testPropertySized 60 "idfViaCEdgesFast properties"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfLfp g
                        isinkdomsOf = PDOM.sinkdomsOf g
                        idom = fmap fromSet $ PDOM.isinkdomOfTwoFinger8 g
                        idom'  = invert''' idom
                        (cycleOfM, cycles) = findCyclesM idom
                        roots = foldr (\(n,m) roots -> if m == Nothing then Set.fromList [n] : roots else roots) cycles (Map.assocs idom)
                        levelOf = Map.fromList [ (n,l) | nl <- treeLevel idom' roots, (n,l) <- nl]
                        cEdges = Map.fromList [(z, [ y | y <- pre g z, not $ z ∈ isinkdomsOf ! y ]) | z <- nodes g]
                    in   (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  sinkdom ! x   ⊃   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                      ∧  (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  not $  x   ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                      ∧  (∀) (nodes g) (\z -> (∀) (sinkdom ! z) (\x -> (∀) (cEdges ! z) (\y -> (       x   ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])
                                                                                   ↔ (not $ sinkdom ! x    ⊃   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])
                         )))
                      ∧  (∀) (nodes g) (\z -> (∀) (sinkdom ! z) (\x -> (∀) (cEdges ! z) (\y ->
                           (   ( (sinkdom ! x  ⊃  (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])  ∧  (not $ x  ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                             ∨ ( (sinkdom ! x  ⊆  (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])  ∧  (      x  ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                           )
                         ∧ (let ok = ((x /= y)  ∧  (not $ Set.null $ sinkdom ! y ∩ sinkdom ! x)) → ((not $ x ∈ sinkdom ! y) ↔ (levelOf ! y <= levelOf ! x)) in (if ok then id else traceShow (g,x,y,z, levelOf)) ok
                           )
                         ))),
    testProperty   "nticdSlice  == nticdslicerCEdges"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticdslicer        = SLICE.NTICD.nticdSlice              g
                        nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> let ms = Set.fromList [m1,m2] in
                              nticdslicer ms == nticdslicerCEdges ms
                    )),
    testProperty   "nticdSlice  == nticdslicerCEdges for CFG like graphs for random slice-criteria of random size"
                $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        n    = length $ nodes g
                        ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        nticdslicer        = SLICE.NTICD.nticdSlice              g
                        nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                    in  nticdslicer ms == nticdslicerCEdges ms,
    testProperty   "nticdSlice  == nticdslicerCEdges for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        nticdslicer        = SLICE.NTICD.nticdSlice              g
                        nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                    in  nticdslicer ms == nticdslicerCEdges ms,
    testProperty   "idomToDFFast _ == dfViaCEdges _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                         let dfViaJ = CEDGE.dfViaCEdges g (fmap fromSet isinkdom) in
                         PDF.idomToDFFast g isinkdom == Map.fromList [ (n, dfViaJ n) | n <- nodes g]
                    ),
    testProperty   "nticd*  _ == dfViaCEdges _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticd = NTICD.nticdViaSinkDom g
                        isinkdom = PDOM.isinkdomOfTwoFinger8 g
                        dfViaJ = CEDGE.dfViaCEdges g (fmap fromSet isinkdom)
                    in (∀) (nodes g) (\n -> (∀) (nodes g) (\m -> if m == n then True else
                         (n ∈ dfViaJ m)  == (m ∈ nticd ! n)
                    )),
    testProperty   "idomToDFFast _ isinkdom == sinkDF _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g isinkdom ==
                       PDF.sinkDF       g),
    testProperty   "idomToDFFast _ isinkdom == idomToDF _ isinkdom"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g                isinkdom ==
                       PDF.idomToDF     g (fromSuccMap $ isinkdom :: Gr () ())),
    testProperty   "DF of isinkdom Cycles are all the same"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = fromSuccMap $ PDOM.TRANS.isinkdomOfSinkContraction g :: Gr () ()
                        isinkdom2 = fromSuccMap $ PDOM.isinkdomOfTwoFinger8      g :: Gr () ()
                        df1    = PDF.idomToDF g isinkdom1
                        idomSccs1 = scc isinkdom1
                        cycles1 = [ cycle | cycle <- idomSccs1, length cycle > 1 ]
                        df2    = PDF.idomToDF g isinkdom2
                        idomSccs2 = scc isinkdom2
                        cycles2 = [ cycle | cycle <- idomSccs2, length cycle > 1 ]
                    in (∀) [(isinkdom1, cycles1, df1), (isinkdom2, cycles2, df2)] (\(isinkdom, cycles, df) ->
                       (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))),
    testProperty   "iPDom^*  == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ fromSuccMap $ fmap toSet $ Map.fromList $
                              PDOMNumbered.iPDom  g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "pdom  == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (      fromSuccMap $ fmap Set.fromList $ Map.fromList $ 
                              PDOMNumbered.pdom  g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "isinkdomOfSinkContraction is intransitive"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = fromSuccMap $ PDOM.TRANS.isinkdomOfSinkContraction g :: Gr () ()
                        isinkdom2 = fromSuccMap $ PDOM.isinkdomOfTwoFinger8      g :: Gr () ()
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                         (∀) (nodes isinkdom) (\n -> length (suc isinkdom n) <= 1)),
    testProperty   "isinkdomOfSinkContraction^*  == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ fromSuccMap $
                              PDOM.TRANS.isinkdomOfSinkContraction  g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "isinkdomOf^*          == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "isinkdomOf^*          == isinkdomOfSinkContraction^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.TRANS.isinkdomOfSinkContraction g),
    testProperty   "joinUpperBound always computes an upper bound"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinks = controlSinks g
                    in (∀) (Map.assocs $ PDOM.joinUpperBound g) (\(n,maybeNs) -> maybeNs /= Nothing ∨   (∃) (sinks) (\sink -> n ∊ sink)),
    testProperty   "isinkdomOf^*          == sinkdomOfJoinUpperBound^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.sinkdomOfJoinUpperBound g),
    testProperty   "isinkdomOf^*          == isinkdomOfGfp2^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        PDOM.isinkdomOfGfp2             g),
    testProperty   "sinkdomOf reduces, in some sense,  to a multi-rooted tree"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom = PDOM.isinkdomOf g :: Gr () ()
                    in   (∀) (nodes isinkdom) (\n -> length (suc isinkdom n) <= 1),
    testProperty   "sinkdomOf             == sinkdomOfisinkdomProperty"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf                  g ==
                       PDOM.sinkdomOfisinkdomProperty  g,
    testProperty   "sinkdomOf             == sinkdomNaiveLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomNaiveGfp        g,
    testProperty   "sinkdomOf             == sinkdomOfLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomOfLfp           g,
    testProperty   "sinkdomOf             == sinkdomOfGfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomOfGfp           g,
    testProperty   "sinkdomOf             == sinkdomNaiveGfpFullTop for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomNaiveGfpFullTop g,
    testProperty   "sinkDFFromUpLocalDefViaSinkdoms == sinkDF"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFFromUpLocalDefViaSinkdoms g ==
                       PDF.sinkDF                          g,
    testProperty   "sinkDFUpGivenXViaSinkdoms == sinkDFUpGivenX"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFUpGivenXViaSinkdoms  g ==
                       PDF.sinkDFUpGivenX             g,
    testProperty   "sinkDFUpDefViaSinkdoms == sinkDFUpDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFUpDefViaSinkdoms  g ==
                       PDF.sinkDFUpDef             g,
    testProperty   "sinkDFUpGivenX ! (x,z) is independent of choice of x for given z"
                $ \(ARBITRARY(g)) ->
                    let sinkDFUp = PDF.sinkDFUpGivenX g
                    in (∀) (Map.assocs sinkDFUp) (\((x,z), dfUp) ->
                         (∀) (Map.assocs sinkDFUp) (\((x',z'), dfUp') ->
                           (z == z') → (dfUp == dfUp')
                         )
                       ),
    testProperty   "sinkDFUpGivenX ! (x,z) == sinkDFUpDef ! z"
                $ \(ARBITRARY(g)) ->
                    let sinkDFUp    = PDF.sinkDFUpGivenX g
                        sinkDFUpDef = PDF.sinkDFUpDef    g
                    in (∀) (Map.assocs sinkDFUp) (\((x,z), dfUp) ->
                         dfUp == sinkDFUpDef ! z
                       )
                    ∧  (∀) (Map.assocs sinkDFUpDef) (\(z, dfUp) ->
                         (∀) [ (x, dfUp') | ((x,z'), dfUp') <- Map.assocs sinkDFUp, z == z'] (\(x, dfUp') ->
                           dfUp == dfUp'
                         )
                       ),
    testProperty   "sinkDFUp              == sinkDFUpDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFUp                g ==
                       PDF.sinkDFUpDef             g,
    testProperty   "sinkDFLocalViaSinkdoms == sinkDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFLocalViaSinkdoms  g ==
                       PDF.sinkDFLocalDef          g,
    testProperty   "sinkDFLocal            == sinkDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFLocal             g ==
                       PDF.sinkDFLocalDef          g,
    testProperty   "sinkDFcd              == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFcd         g ==
                       SNM.nticdF3          g,
    testProperty   "isinkdomTwoFingercd   == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.isinkdomTwoFingercd g ==
                       SNM.nticdF3             g,
    testProperty   "sinkDFFromUpLocalDefcd== nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFFromUpLocalDefcd  g==
                       SNM.nticdF3                 g,
    testProperty   "sinkDFFromUpLocalcd   == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFFromUpLocalcd     g ==
                       SNM.nticdF3                 g,
    testProperty   "sinkDFF2cd            == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFF2cd       g ==
                       SNM.nticdF3          g
  ]




insensitiveDomTests = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" $
  [  testCase    ( "idomToDFFast _ isinkdom == sinkDF _ for " ++ exampleName)
            $       let isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g isinkdom ==
                       PDF.sinkDF       g) @? ""
  | (exampleName, g) <- interestingIsinkdomTwoFinger
  ] ++
  [  testCase    (  "sinkDFLocal == sinkDFLocalDef for " ++ exampleName)
            $          PDF.sinkDFLocal    g ==
                       PDF.sinkDFLocalDef g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "sinkDFFromUpLocalDefViaSinkdoms == sinkDF for " ++ exampleName)
            $          PDF.sinkDFFromUpLocalDefViaSinkdoms g ==
                       PDF.sinkDF                          g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "sinkDFUpGivenXViaMdoms == sinkDFUpGivenX for " ++ exampleName)
            $          PDF.sinkDFUpGivenXViaSinkdoms     g ==
                       PDF.sinkDFUpGivenX             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "sinkDFUpDefViaMdoms == sinkDFUpDef for " ++ exampleName)
            $            PDF.sinkDFUpDefViaSinkdoms     g ==
                         PDF.sinkDFUpDef             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ isinkdom == sinkDF _ for " ++ exampleName)
            $       let isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g isinkdom ==
                       PDF.sinkDF       g) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ isinkdom == idomToDF _ isinkdom for " ++ exampleName)
            $       let isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                        PDF.idomToDFFast g isinkdom ==
                        PDF.idomToDF     g (fromSuccMap isinkdom :: Gr () ())) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "DF of isinkdom Cycles are all the same for " ++ exampleName)
            $       let isinkdom = fromSuccMap $ PDOM.TRANS.isinkdomOfSinkContraction g :: Gr () ()
                        df    = PDF.idomToDF g isinkdom
                        idomSccs = scc isinkdom
                        cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                    in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "sinkDFGraphP              ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFGraphP p            == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFFromUpLocalGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFFromUpLocalGraphP p == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFFromUpLocalDefGraphP==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFFromUpLocalDefGraphP p
                                              ==
                                                 PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFF2GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFF2GraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []



sensitiveDomProps = testGroup "(concerning nontermination-sensitive control dependence via dom-like frontiers )" [
    testProperty   "ntscdViaMDom          == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.ntscdViaMDom g ==
                       SNM.ntscdF3        g,
    testPropertySized 40 "stepsCL sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                    in PDF.stepsCL g mdom,
    testPropertySized 40 "noJoins sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                    in PDF.noJoins g mdom,
    testProperty   "idomToDFFast _ imdom6  == idomToDFFast _ imdom7  for CFG-shaped graphs with exit->entry edge"
                $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    imdom6 = PDOM.imdomOfTwoFinger6 g
                    imdom7 = PDOM.imdomOfTwoFinger7 g
                in PDF.idomToDFFast g imdom6 == PDF.idomToDFFast g imdom7,
    testProperty   "idomToDFFast _ imdom6  == idomToDFFast _ imdom7"
                $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    imdom6 = PDOM.imdomOfTwoFinger6 g
                    imdom7 = PDOM.imdomOfTwoFinger7 g
                in PDF.idomToDFFast g imdom6 == PDF.idomToDFFast g imdom7,
    testPropertySized 60 "idfViaCEdgesFast properties"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                        imdomsOf = PDOM.mdomsOf g
                        idom = fmap fromSet $ PDOM.imdomOfTwoFinger7 g
                        idom'  = invert''' idom
                        (cycleOfM, cycles) = findCyclesM idom
                        roots = foldr (\(n,m) roots -> if m == Nothing then Set.fromList [n] : roots else roots) cycles (Map.assocs idom)
                        levelOf = Map.fromList [ (n,l) | nl <- treeLevel idom' roots, (n,l) <- nl]
                        cEdges = Map.fromList [(z, [ y | y <- pre g z, not $ z ∈ imdomsOf ! y ]) | z <- nodes g]
                    in   (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  mdom ! x   ⊃   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                      ∧  (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  not $  x   ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                      ∧  (∀) (nodes g) (\z -> (∀) (mdom ! z) (\x -> (∀) (cEdges ! z) (\y -> (       x   ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])
                                                                                   ↔ (not $ mdom ! x    ⊃   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])
                         )))
                      ∧  (∀) (nodes g) (\z -> (∀) (mdom ! z) (\x -> (∀) (cEdges ! z) (\y ->
                           (   ( (mdom ! x  ⊃  (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])  ∧  (not $ x  ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                             ∨ ( (mdom ! x  ⊆  (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])  ∧  (      x  ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                           )
                         ∧ (let lvlY' = case idom ! y of { Nothing -> -1 ; Just y' -> levelOf ! y' } in
                            let ok = ((x /= y)  ∧  (not $ Set.null $ mdom ! y ∩ mdom ! x)) → ((not $ x ∈ mdom ! y) ↔ (lvlY' < levelOf ! x)) in (if ok then id else traceShow (g,x,y,z, levelOf)) ok
                           )
                         ))),
    testProperty   "ntscdSlice  == idfViaCEdgesFast"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom    = PDOM.imdomOfTwoFinger7  g
                        idfViaJ  = CEDGE.idfViaCEdgesFast g (fmap fromSet imdom)
                        ntscdslicer = SLICE.NTICD.ntscdSlice g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> let ms = Set.fromList [m1,m2] in
                              ntscdslicer ms == idfViaJ ms
                    )),
    testProperty   "ntscdSlice  == ntscdslicerCEdges for CFG like graphs for random slice-criteria of random size"
                $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        n    = length $ nodes g
                        ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        ntscdslicer        = SLICE.NTICD.ntscdSlice              g
                        ntscdslicerCEdges  = CEDGE.ntscdSliceViaCEdgesFast g
                    in  ntscdslicer ms == ntscdslicerCEdges ms,
    testProperty   "ntscdSlice  == ntscdslicerCEdges for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        ntscdslicer        = SLICE.NTICD.ntscdSlice              g
                        ntscdslicerCEdges  = CEDGE.ntscdSliceViaCEdgesFast g
                    in  ntscdslicer ms == ntscdslicerCEdges ms,
    testProperty   "idomToDFFast _ == dfViaCEdges _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom7] (\imdom ->
                         let dfViaJ = CEDGE.dfViaCEdges g (fmap fromSet imdom) in
                         PDF.idomToDFFast g imdom == Map.fromList [ (n, dfViaJ n) | n <- nodes g]
                    ),
    testPropertySized 80   "mDFFromUpLocalDefViaSMdoms == mDF"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFFromUpLocalDefViaMdoms g ==
                       PDF.mDF                       g,
    testProperty   "idomToDFFast _ imdom == idomToDF _ imdom"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g              imdom ==
                         PDF.idomToDF     g (fromSuccMap imdom :: Gr () ())
                       ),
    testProperty   "idomToDFFast _ imdom  == mDF _ "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g imdom ==
                         PDF.mDF          g
                       ),
    testProperty   "DF of imdom Cycles are all the same"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = fromSuccMap $ PDOM.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ PDOM.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         let df    = PDF.idomToDF g imdom
                             idomSccs = scc imdom
                             cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                         in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))
                       ),
    testProperty   "imdomOfTwoFinger7^*   == imdomOfTwoFinger6^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ fromSuccMap $
                        PDOM.imdomOfTwoFinger7            g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        PDOM.imdomOfTwoFinger6            g),
    testProperty   "imdomOfLfp^*          == imdomOfTwoFinger6^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.imdomOfLfp             g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        PDOM.imdomOfTwoFinger6            g),
    testPropertySized 50   "mdomOf             == mdomNaiveLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.mdomOf              g ==
                       PDOM.mdomNaiveLfp        g,
    testPropertySized 50   "mdomOf             == mdomOfLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.mdomOf              g ==
                       PDOM.mdomOfLfp           g,
    testProperty   "mdomOfLfp reduces, in some sense,  to a multi-rooted tree"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = PDOM.imdomOfLfp g :: Gr () ()
                    in   (∀) (nodes imdom) (\n -> length (suc imdom n) <= 1),
    testProperty   "mdomOfLfp           == mdomOfimdomProperty"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.mdomOfLfp            g ==
                       PDOM.mdomOfimdomProperty  g,
    testPropertySized 50   "mDFUpGivenXViaMdoms == mDFUpGivenX"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFUpGivenXViaMdoms     g ==
                       PDF.mDFUpGivenX             g,
    testPropertySized 50   "mDFUpDefViaMdoms == mDFUpDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFUpDefViaMdoms     g ==
                       PDF.mDFUpDef             g,
    testProperty   "mDFUpGivenX ! (x,z) is independent of choice of x for given z"
                $ \(ARBITRARY(g)) ->
                    let mDFUp = PDF.mDFUpGivenX g
                    in (∀) (Map.assocs mDFUp) (\((x,z), dfUp) ->
                         (∀) (Map.assocs mDFUp) (\((x',z'), dfUp') ->
                           (z == z') → (dfUp == dfUp')
                         )
                       ),
    testProperty   "mDFUpGivenX ! (x,z) == mDFUpDef ! z"
                $ \(ARBITRARY(g)) ->
                    let mDFUp    = PDF.mDFUpGivenX g
                        mDFUpDef = PDF.mDFUpDef    g
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
                       PDF.mDFUp                g ==
                       PDF.mDFUpDef             g,
    testPropertySized 50   "mDFLocalViaMdoms   == mDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFLocalViaMdoms     g ==
                       PDF.mDFLocalDef          g,
    testProperty   "mDFLocal           == mDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFLocal             g ==
                       PDF.mDFLocalDef          g,
    testProperty   "mDFcd              == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFcd            g ==
                       SNM.ntscdF3          g,
    testProperty   "mDFFromUpLocalDefcd== ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFFromUpLocalDefcd  g ==
                       SNM.ntscdF3              g,
    testProperty   "mDFFromUpLocalcd   == ntisdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFFromUpLocalcd     g ==
                       SNM.ntscdF3              g,
    testProperty   "imdomTwoFingercd     == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.imdomTwoFingercd   g ==
                       SNM.ntscdF3          g,
    testProperty   "mDFF2cd            == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFF2cd              g ==
                       SNM.ntscdF3              g
  ]
sensitiveDomTests = testGroup "(concerning nontermination-sensitive control dependence via dom-like frontiers )"  $
  [  testCase    ( "idomToDFFast _ mdom == mDF _ for " ++ exampleName)
            $       let imdom6 = PDOM.imdomOfTwoFinger6  g
                        imdom7 = PDOM.imdomOfTwoFinger7  g
                    in (∀) [imdom6, imdom7] (\imdom ->
                       PDF.idomToDFFast g imdom ==
                       PDF.mDF       g) @? ""
  | (exampleName, g) <- interestingImdomTwoFinger
  ] ++
  [  testCase    (  "mDFLocal == mDFLocalDef for " ++ exampleName)
            $          PDF.mDFLocal    g ==
                       PDF.mDFLocalDef g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFFromUpLocalDefViaMdoms == mDF for " ++ exampleName)
            $          PDF.mDFFromUpLocalDefViaMdoms g ==
                       PDF.mDF                       g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFUpGivenXViaMdoms == mDFUpGivenX for " ++ exampleName)
            $          PDF.mDFUpGivenXViaMdoms     g ==
                       PDF.mDFUpGivenX             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFUpDefViaMdoms == mDFUpDef for " ++ exampleName)
            $            PDF.mDFUpDefViaMdoms     g ==
                         PDF.mDFUpDef             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ imdom == idomToDF _ imdom for " ++ exampleName)
            $       let imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g              imdom ==
                         PDF.idomToDF     g (fromSuccMap imdom :: Gr () ())
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ imdom == mDF _ for " ++ exampleName)
            $       let imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g imdom ==
                         PDF.mDF          g
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "DF of imdom Cycles are all the same for " ++ exampleName)
            $       let imdom6 = fromSuccMap $ PDOM.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ PDOM.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         let df    = PDF.idomToDF g imdom
                             idomSccs = scc imdom
                             cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                         in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))
                       )  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "imdomOfTwoFinger7^*   == imdomOfTwoFinger6^* for " ++ exampleName)
                  $ (trc $ fromSuccMap $
                           PDOM.imdomOfTwoFinger7            g :: Gr () ()) ==
                    (trc $ fromSuccMap $
                           PDOM.imdomOfTwoFinger6            g)  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "imdomOfLfp^*          == imdomOfTwoFinger6^* for " ++ exampleName)
                  $ (trc $ PDOM.imdomOfLfp             g :: Gr () ()) ==
                    (trc $ fromSuccMap $
                           PDOM.imdomOfTwoFinger6            g)  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []


newcdProps = testGroup "(concerning new control dependence definitions)" [
    testProperty  "ntacdDef               == nticdF3                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in NTICDUnused.ntacdDef         g ==
                       SNM.nticdF3          g
  ]
newcdTests = testGroup "(concerning new control dependence definitions)" $
  [  testCase    ( "ntnacdDefGraphP       ==  nticdF3GraphP for " ++ exampleName)
                  $ PROG.ntacdDefGraphP      p ==
                    PROG.nticdF3GraphP       p        @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []



wodProps = testGroup "(concerning weak order dependence)" [
    testProperty "nticdNTIODSlice ⊆ nticdNTIODSliceViaCutAtRepresentatives = nticdNTIODSliceViaCutAtRepresentativesNoTrivial ⊆ nticdNTIODSliceViaEscapeNodes ⊆ nticdNTIODSliceViaChoiceAtRepresentatives for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer0  = SLICE.NTICD.nticdNTIODSlice                        g
                    slicer1  = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentatives g
                    slicer1' = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentativesNoTrivial g
                    slicer2  = SLICE.TRANS.nticdNTIODSliceViaEscapeNodes          g
                    slicerNX = SLICE.TRANS.nticdNTIODSliceViaChoiceAtRepresentatives g
                    s0 = slicer0  ms
                    s1 = slicer1  ms
                    s1'= slicer1' ms
                    s2 = slicer2  ms
                    sNX= slicerNX ms
                    ok = s0 ⊆ s1
                       ∧ s1 == s1'
                       ∧ s1 ⊆ s2
                       ∧ s2 ⊆ sNX
                in -- (if Set.size s0 /= Set.size s1 ∨ Set.size s1 /= Set.size s2 then traceShow (Set.size ms, Set.size s0, Set.size s1, Set.size s2, ms, g) else id) $
                   -- (if Set.size s0 < Set.size sNX then trace ((show $ length $ nodes $ g) ++ ",\t" ++ (show $ Set.size ms) ++ ",\t" ++ (show $ Set.size s0) ++ ",\tGO,\t" ++ (show $ Set.size s1) ++ ",\t" ++ (show $ Set.size s1') ++ ",\t" ++ (show $ Set.size s2) ++ ",\t" ++ (show $ Set.size sNX)) else id) $
                  (if ok then id else traceShow (g, ms)) ok,
    testPropertySized 60 "nticdNTIODSlice ⊆ nticdNTIODSliceViaCutAtRepresentatives = nticdNTIODSliceViaCutAtRepresentativesNoTrivial ⊆ nticdNTIODSliceViaEscapeNodes ⊆ nticdNTIODSliceViaChoiceAtRepresentatives for random slice-criteria of random size and CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer0  = SLICE.NTICD.nticdNTIODSlice                        g
                    slicer1  = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentatives g
                    slicer1' = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentativesNoTrivial g
                    slicer2  = SLICE.TRANS.nticdNTIODSliceViaEscapeNodes          g
                    slicerNX = SLICE.TRANS.nticdNTIODSliceViaChoiceAtRepresentatives g
                    s0 = slicer0  ms
                    s1 = slicer1  ms
                    s1'= slicer1' ms
                    s2 = slicer2  ms
                    sNX= slicerNX ms
                    ok = s0 ⊆ s1
                       ∧ s1 == s1'
                       ∧ s1 ⊆ s2
                       ∧ s2 ⊆ sNX
                in -- (if Set.size s0 /= Set.size s1 ∨ Set.size s1 /= Set.size s2 then traceShow (Set.size ms, Set.size s0, Set.size s1, Set.size s2, ms, g) else id) $
                   -- (if Set.size s0 < Set.size sNX then trace ((show $ length $ nodes $ g) ++ ",\t" ++ (show $ Set.size ms) ++ ",\t" ++ (show $ Set.size s0) ++ ",\tGO,\t" ++ (show $ Set.size s1) ++ ",\t" ++ (show $ Set.size s1') ++ ",\t" ++ (show $ Set.size s2) ++ ",\t" ++ (show $ Set.size sNX)) else id) $ 
                   (if ok then id else traceShow (g, ms)) ok,
    testProperty "wccSlice == wccSliceViaNticd for random slice-criteria of random size and CFG-shaped graphs"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
    -- testProperty "wccSlice == wccSliceViaNticd for random slice-criteria of random size and CFG-shaped graphs with exit->entry edge"
    -- $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
    --             let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
    --                 [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
    --                 g = insEdge (exit, entry, ()) generatedGraph
                    n  = length $ nodes g
                    ms = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    wccslicer   = FCACD.wccSlice g
                    wccslicer'  = SLICE.NTICD.wccSliceViaNticd g
                in wccslicer ms == wccslicer'  ms,
    testProperty "wccSlice == * for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
                    n  = length $ nodes g
                    ms
                      | n == 0 = []
                      | n /= 0 = List.nub [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    msS = Set.fromList ms

                    wccslicer   = FCACD.wccSlice g
                    wccslicer'  = SLICE.NTICD.wccSliceViaNticd g

                    fromMs =  dfs ms g
                    g'    = subgraph fromMs g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g'

                    toMs   = rdfs ms g
                    g''    = foldr (flip delSuccessorEdges) (subgraph fromMs $ subgraph toMs g) ms
                    nticdslicer = SLICE.NTICD.nticdSlice g''

                in   wccslicer msS == wodslicer   msS
                   ∧ wccslicer msS == nticdslicer msS
                   ∧ wccslicer msS == wccslicer'  msS,
    testProperty "nticdNTIODSlice == nticdNTIODSliceViaISinkDom  for random slice-criteria of random size, and CFG-shaped graphs"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.NTICD.nticdNTIODSlice               g
                    slicer2  = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g
                in   slicer1  ms == slicer2  ms,
    testProperty "nticdNTIODSlice == nticdNTIODSliceViaISinkDom  for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.NTICD.nticdNTIODSlice              g
                    slicer2  = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g
                    slicer1' = SLICE.NTICD.nticdNTIODSlice              g'
                    slicer2' = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g'
                in   slicer1  ms == slicer2  ms
                   ∧ slicer1' ms == slicer2' ms,
    testPropertySized 20 "nticdNTIODSlice == nticdNTIODSliceViaISinkDom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    slicer1  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    slicer2  = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g
                    slicer1' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    slicer2' = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let ms = Set.fromList [m1, m2] in -- -} (∀) (nodes g) (\m3 -> let ms = Set.fromList [m1, m2, m3] in 
                       slicer1  ms == slicer2  ms
                     ∧ slicer1' ms == slicer2' ms
                   ))),
      testProperty  "sinkdoms' (slicer' m) = ∅"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        m0S
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    -- in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->   (∀) (nodes g) (\m3 -> let m0S = Set.fromList [m1, m2, m3] in
                    in 
                           let m0s = Set.toList m0S
                               g' = foldr (flip delSuccessorEdges) g m0s
                               slicer' = SLICE.NTICD.nticdSlice g'
                               sinkdoms' = PDOM.sinkdomsOf g'
                               sinkdom'  = PDOM.sinkdomOfGfp g'
                           in  (∀) (slicer' m0S) (\n -> Set.null $ sinkdoms' ! n)
                             ∧ (∀) (slicer' m0S) (\n ->            sinkdom'  ! n == Set.fromList [n])
                        -- )))
                    ,
    testProperty "nticdNTIODSlice == nticdNTIODSliceViaNticd for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    slicer2  = SLICE.NTICD.nticdNTIODSlice              g
                    slicer1' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    slicer2' = SLICE.NTICD.nticdNTIODSlice              g'
                in   slicer1  ms == slicer2  ms
                   ∧ slicer1' ms == slicer2' ms,
    testPropertySized 40 "sinkdoms g' => sinkdoms g"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    sinkdoms = PDOM.sinkdomsOf g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  let m0S = Set.fromList [m1, m2] in -- (∀) (nodes g) (\m3 -> let m0S = Set.fromList [m1, m2, m3] in
                     let  m0s = Set.toList m0S
                          toM0s = rdfs m0s g
                          g' = foldr (flip delSuccessorEdges) g m0s
                          sinkdoms' = PDOM.sinkdomsOf g'
                     in   (sinkdoms' ⊑ sinkdoms)
                   )),
      testProperty  "isinkdoms path order"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        isinkdoms = PDOM.sinkdomsOf g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) (isinkdoms ! n) (\m1 ->  (∀) (ms) (\m2 ->
                         let ok  =   ((m1,m2) ∈ must ! n)
                                   ∨ (m1 ∈ sinkdom ! m2 ∧  m2 ∈ sinkdom ! m1  ∧  m2 ∈ isinkdoms ! n)
                                   ∨ (n == m2)
                         in (if ok  then id else traceShow (g, n, m1, m2)) ok
                       ))),
      testProperty  "sinkdom path order"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        -- isinkdoms = NTICD.sinkdomsOf g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) ms (\m1 ->  (∀) (ms) (\m2 ->
                         let ok  =   ((m1,m2) ∈ must ! n)
                                   ∨ ((m2,m1) ∈ must ! n)
                                   ∨ (m1 ∈ sinkdom ! m2 ∧  m2 ∈ sinkdom ! m1)
                         in (if ok  then id else traceShow (g, n, m1, m2)) ok
                       ))),
      testProperty  "sinkdom path order for CFG with unique exit node"
                $ \(SIMPLECFG(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        -- isinkdoms = NTICD.sinkdomsOf g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) ms (\m1 ->  (∀) (ms) (\m2 ->
                         let ok  =   ((m1,m2) ∈ must ! n)
                                   ∨ ((m2,m1) ∈ must ! n)
                                   ∨ (m1 == m2)
                         in (if ok  then id else traceShow (g, n, m1, m2)) ok
                       ))),
      testPropertySized 25  "nticd nticdNTIOD Proof"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        isinkdoms = PDOM.sinkdomsOf g
                        ntind = NTICD.ntindDef g
                    in (∀) (nodes g) (\m0 -> (∀) (nodes g) (\n0 -> (∀) (nodes g) (\n' -> (∀) (nodes g) (\n -> (∀) (suc g n) (\x -> (∀) (suc g n) (\x' ->
                         let okn0m0 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must    ! x)
                                   ∧  (       n0      ∈ sinkdom ! x)
                                   ) →  (n0 ∈ sinkdom ! m0)
                             ok00 = (  True
                                   ∧  (Set.size (isinkdoms ! n) > 1)
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n /= m0)
                                   ) →  ((m0 ∈ ntind ! n)  ∧  (not $ m0 ∈ isinkdoms ! n))
                             ok0 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   -- ∧  (      n0 ∈ sinkdom ! m0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n /= m0)
                                   ) →  (m0 ∈ ntind ! n)
                             ok1 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n' ∈ isinkdoms ! n)
                                   ) →  (n' /= x)
                             ok2 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n' ∈ isinkdoms ! n)
                                   ) →  (n' /= n)
                             ok3 = (  True 
                                   ∧  (n /= n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n' ∈ isinkdoms ! n)
                                   ) →  (n0 ∈ sinkdom ! n')
                             ok4 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n')
                                   ∧  (n' ∈ sinkdom ! n)
                                   ∧  (n' /= n)
                                   ) →  (n' /= x)
                             ok5 = (  True
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n' ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   -- ∧  (n' /= x)
                                   ∧  (n' /= n)
                                   ) → ((not $ (n', m0) ∈ must ! x) ∧  (n' /= x))
                             ok6 = (  True
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   -- ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (      (n', m0) ∈ must ! x)
                                   ∧  (      n' ∈ sinkdom ! x')
                                   ∧  (      n0 ∈ sinkdom ! x )
                                   ) → ( m0 ∈ sinkdom ! x' ∧  m0 ∈ sinkdom ! n' ∧ m0 ∈ sinkdom ! x)
                                     -- ) → ((not $ (n', m0) ∈ must ! x))
                             ok7 = (  True
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (         m0 ∈ sinkdom ! x')
                                   ) → ( m0 ∈ sinkdom ! n0)
                         in (if okn0m0 ∧ ok00 ∧ ok0 ∧ ok1 ∧ ok2 ∧ ok3 ∧ ok4 ∧ ok5 ∧ ok6 ∧ ok7  then id else traceShow (g, m0, n0, n', n, x, x')) (okn0m0 ∧ ok00 ∧ ok0 ∧ ok1 ∧ ok2 ∧ ok3 ∧ ok4 ∧ ok5 ∧ ok6 ∧ ok7 )
                       )))))),
    testProperty   "ntiod size for looping ladders"
    $ \(size :: Int) ->
                let msum = Map.fold (\ns s -> Set.size ns + s) 0

                    n0 = (abs size) `div` 2
                    g = fullLadder n0  :: Gr () ()
                    n = length $ nodes g
                    ntiod = assert (n == 2*n0 + 3) $
                            ODEP.ntiodFastPDomSimpleHeuristic g
                    even = [ n | n <- nodes g, n `mod` 2 == 0]
                    odd  = [ n | n <- nodes g, n `mod` 2 /= 0]
                in -- traceShow (n, msum ntiod, sum [ (n `div` 2) * ((m1+1) `div` 2) | m1 <- odd], ((((n-1) `div` 2 + 1  ) * (n - 1)) `div` 4  ) * (n `div` 2))   $
                     (∀) odd (\m1 ->
                       let left  = Set.fromList [ (m1,m2,n) | m2 <- even, n <- Set.toList $ ntiod ! (m1,m2)  ]
                           right = Set.fromList [ (m1,m2,n) | m2 <- even, n <- even, n < m1, n /= m2 ]
                           size = (n `div` 2) * ((m1+1) `div` 2)
                       in   (left == right)
                          ∧ (Set.size right == size)
                     )
                   ∧ (msum ntiod >= ((((n-1) `div` 2 + 1  ) * (n - 1)) `div` 4  ) * (n `div` 2)),
    testProperty "nticdSlice == ntindDef"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    nticdslicer = SLICE.NTICD.nticdSlice g
                    ntind = NTICD.ntindDef g
                in (∀) (nodes g) (\m ->
                     let ms = Set.fromList [m]
                         s  = (nticdslicer ms) ∖ ms
                         s' = Set.fromList [ n | n <- nodes g, m ∈ ntind ! n ]
                     in s == s'
                   ),
      testPropertySized 40  "sinkdomOfLfp ms                 == (∀) mustOfLfp  property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  let m0S = Set.fromList [m1, m2] in
                           let m0s = Set.toList m0S
                               toM0s = rdfs m0s g
                               g' = foldr (flip delSuccessorEdges) g m0s
                               sinkdom' = PDOM.sinkdomOfGfp g'
                           in (∀) (nodes g) (\n -> (∀) m0s (\m0 -> (∀) (nodes g) (\m ->
                                let ok = (m == m0)  ∨  ((m ∈ sinkdom' ! n) → ((m,m0) ∈ must ! n))
                                in (if ok then id else traceShow (g, m0S, n, m, m0)) ok
                           )))
                       )),
    testProperty "nticdNTIOD == nticdMyViaNticd properties"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g    = generatedGraph
                    trcG = trc g
                    nticd = NTICD.nticdViaSinkDom g
                    sinkdom = PDOM.sinkdomOfGfp g
                    ntiod =  ODEP.ntiodFastPDomSimpleHeuristic g
                    must = ODEP.mustOfGfp g
                    slicer  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    nticdslicer = SLICE.NTICD.nticdSlice g
                    sinkdoms = PDOM.sinkdomsOf g
                    onPathBetween ss ts = fwd
                      where gTs = foldr (flip delSuccessorEdges) g ts
                            fwd = Set.fromList $  dfs ss gTs
                    m0S
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                     where n    = length $ nodes g
                in
                -- in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let m0S = Set.fromList [m1, m2] in  -- -} (∀) (nodes g) (\m3 -> (∀) (nodes g) (\m4 -> let m0S = Set.fromList [m1, m2, m3, m4] in
                     let  m0s = Set.toList m0S
                          toM0s = rdfs m0s g
                          g' = foldr (flip delSuccessorEdges) g m0s
                          trcG' = trc g'
                          nticd' = NTICD.nticdViaSinkDom g'
                          nticd'slicer = SLICE.NTICD.nticdSlice g'
                          sinkdom' = PDOM.sinkdomOfGfp g'
                          sinkdoms' = PDOM.sinkdomsOf g'
                          onPathBetween' ss ts = fwd
                            where g'Ts = foldr (flip delSuccessorEdges) g' ts
                                  fwd = Set.fromList $  dfs ss g'Ts
                          s = slicer m0S
                     in   (sinkdom' ⊑ sinkdom)
                        ∧ (∀) s (\n -> (n ∈ m0S)   ∨   (∃) (nticd' ! n) (\n0 -> n0 ∈ s ∧  n0 /= n) ∧ (∀) (nticd' ! n  ∩ s) (\n0 -> if n0 == n then True else
                             n0 ∈ s   ∧  ((n0 ∈ nticd ! n)  ∨  (   True 
                                                                  ∧ (∀) (suc g n) (\x -> n0 ∈ sinkdom ! x)
                                                                  ∧ (n0 ∈ sinkdom ! n)
                                                                  -- ∧ (∀) m0S (\m0 ->  m0 ∈ sinkdom ! n0)
                                                                  ∧ (∃) (suc g n) (\x -> (∃) m0S (\m0 ->
                                                                        m0 /= n0   ∧  n0 ∈ sinkdom ! m0
                                                                      ∧ x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG n0)
                                                                      ∧ (not $ (n0, m0) ∈ must ! x )
                                                                    ))
                                                                  ∧ (∀) (suc g n) (\x -> (∀) m0S (\m0 ->
                                                           let ok = (
                                                                        m0 /= n0   ∧  n0 ∈ sinkdom ! m0
                                                                      ∧ x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG n0)
                                                                      ∧ (not $ (n0, m0) ∈ must ! x )
                                                                    ) → (
                                                                        ((      m0 ∈ sinkdom ! n0)  ∧  (n ∈ ntiod ! (n0,m0)                )                                           )
                                                                      ∨ ((not $ m0 ∈ sinkdom ! n0)  ∧  (n ∈ nticdslicer (Set.fromList [m0]))
                                                                                                    ∧  ((n == m0) ∨ 
                                                                                                        (   (      m0 ∈ onPathBetween [x]       (Set.toList   $ sinkdoms ! n)) 
                                                                                                          ∧ (not $ m0 ∈                         (Set.insert n $ sinkdoms ! n)) ))      )
                                                                    )
                                                           in (if ok then id else traceShow (g,  n,  n0,  x,  m0)) ok
                                                                    ))
                                                               )
                                         )
                          ))
                        ∧ (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m ->
                            let ok = (m ∈ sinkdom' ! n) ∨ ((∃) m0S (\m0 ->  m0 /= m  ∧  m ∈ sinkdom ! m0  ∧  n `elem` (pre trcG' m0)  ∧  m0 `elem` (pre trcG m)  ∧  (not $ (m, m0) ∈ must ! n )))
                            in (if ok then id else traceShow (g, m0S, n, m)) ok
                          ))
                        ∧ (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m -> let { g'' = delSuccessorEdges g' m ; reachN = reachable n g'' } in 
                            let ok = (m ∈ sinkdom' ! n) ∨ ((∃) m0S (\m0 ->  m0 /= m  ∧  m0 `elem` reachN))
                            in (if ok then id else traceShow (g, m0S, n, m)) ok
                          ))
                        ∧ (∀) (Map.assocs nticd') (\(n, ms) -> (∀) ms (\m ->
                          let ok =   ((m ∈ nticd ! n)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (not $ m ∈ sinkdom' ! x)))
                                   ∧ ((m ∈ nticd ! n)  ∨  (m ∈ sinkdom ! n))
                                   ∧ ((m ∈ nticd ! n)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (∃) m0S (\m0 ->  m0 /= m  ∧  m ∈ sinkdom ! m0  ∧  x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG m) ∧  (not $ (m, m0) ∈ must ! n ) ) ))
                          in (if ok then id else traceShow (g, m0S, n, m)) ok
                        ))
                        ∧ (∀) (Map.assocs nticd) (\(n, ms) -> (∀) ms (\m ->
                          let ok =   ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (not $ m ∈ sinkdom' ! x)))
                                   ∧ ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (∀) (suc g n) (\x -> not $ m ∈ sinkdom' ! x))
                                   ∧ ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (sinkdom' ! n == Set.fromList [n]))
                                   ∧ ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (∃) m0S (\m0 ->  m0 /= m  ∧  m ∈ sinkdom ! m0  ∧  x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG m) ∧  (not $ (m, m0) ∈ must ! n ) ) ))
                          in (if ok then id else traceShow (g, m0S, n, m)) ok
                        ))
                        ∧ (∀) s (\n -> (n ∈ m0S)
                                     ∨ (∃) s (\m1 -> (∃) s (\m2 -> m1 /= m2  ∧  n /= m2  ∧  n ∈ ntiod ! (m1,m2))) ∧  (∀) s (\m1 -> (∀) s (\m2 -> if m1 == m2  ∨  n == m2  ∨  (not $ n ∈ ntiod ! (m1,m2)) then True else
                                         m1 ∈ s   ∧  m2 ∈ s   ∧
                                           (∃) m0S (\m0 ->          n `elem` (pre trcG' m0))
                                         ∧
                                           (∀) m0S (\m0 -> if not $ n `elem` (pre trcG' m0) then True else
                                            let ok = n ∈ nticd'slicer (Set.fromList [m0]) in (if ok then id else traceShow (g, m0s, n,  m1,  m2, m0)) ok
                                           )
                                         ∧ ( (m1 ∈ nticd' ! n) ∨ (∀) (suc g n) (\x -> not $ m1 ∈ sinkdom' ! x) ∧ (∃) (suc g n) (\x -> (m1,m2) ∈ must ! x) ∧ (∀) (suc g n) (\x -> if not $ (m1,m2) ∈ must ! x then True else
                                             let ok = x /= m1 ∧ (∃) (reachable x (delSuccessorEdges g' m1)) (\m0 -> m0 ∈ m0S ∧ m0 /= m1)in (if ok then id else traceShow (g, m0s, n,  m1,  m2, x)) ok
                                           ))
                                         ∧ let ok =  not $ m1 ∈ sinkdom' ! m2  in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                         -- ∧ let ok =  (n ∈ nticd'slicer (Set.fromList [m2]))  ∨  (∃) m0S (\m0 -> (m0 /= m1 ∧ n ∈ ntiod ! (m1,m0)))  in (if ok then id else traceShow ("lol", g, m0s, n,  m1,  m2)) ok
                                         ∧ let ok = Set.null $ sinkdoms' ! n in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                         ∧ let ok = sinkdom' ! n == Set.fromList [n] in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                         ∧ let ok = False
                                                  ∨ ( (      m2 ∈ m0S) ∧ True)
                                                  ∨ ( (not $ m2 ∈ m0S) ∧ True)
                                           in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                       ))
                                     ∨ (∃) (nticd ! n) (\n0 -> n0 ∈ s ∧  n0 /= n) ∧ (∀) (nticd ! n  ∩ s) (\n0 -> if n0 == n then True else
                                         (Set.null $ sinkdoms' ! n) ∧ (sinkdom' ! n == Set.fromList [n]) ∧
                                         n0 ∈ s   ∧  ((n0 ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨
                                                                (   True 
                                                                  ∧ (∀) (suc g n) (\x -> not $ n0 ∈ sinkdom' ! x)
                                                                  ∧ (sinkdom' ! n == Set.fromList [n])
                                                                  ∧ (Set.null $ sinkdoms' ! n)
                                                                  ∧ (∃) (suc g n) (\x -> (n0 ∈ sinkdom ! x)  ∧  (∃) m0S (\m0 ->
                                                                        m0 /= n0   ∧  m0 `elem`  reachable x (delSuccessorEdges g' n0)
                                                                    ))
                                                                  ∧ (∀) (suc g n) (\x -> if (not $ n0 ∈ sinkdom ! x) then True else (∀) m0S (\m0 ->
                                                           let ok = (
                                                                        m0 /= n0   ∧  m0 `elem`  reachable x (delSuccessorEdges g' n0)
                                                                    ) → ( True
                                                                      ∧ (n ∈ nticd'slicer (Set.fromList [m0]))
                                                                      ∧ ((n == m0) ∨ 
                                                                          (   (      m0 ∈ onPathBetween' [x]      (Set.toList   $ sinkdoms' ! n)) 
                                                                            ∧ (not $ m0 ∈                         (Set.insert n $ sinkdoms' ! n)) ))
                                                                    )
                                                           in (if ok then id else traceShow (g, m0s, n,  n0,  x,  m0)) ok
                                                                    ))
                                                               )
                                                     )
                                     )
                           )
                   -- )))),
                   ,
    testPropertySized 25 "nticdNTIODSlice == nticdNTIODSliceViaNticd"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    slicer1  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    slicer2  = SLICE.NTICD.nticdNTIODSlice              g
                    slicer1' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    slicer2' = SLICE.NTICD.nticdNTIODSlice              g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let ms = Set.fromList [m1, m2] in -- -} (∀) (nodes g) (\m3 -> let ms = Set.fromList [m1, m2, m3] in 
                       slicer1  ms == slicer2  ms
                     ∧ slicer1' ms == slicer2' ms
                   ))),
      testPropertySized 30  "nticdNTIODSlice == nticdNTIODSliceViaNticd even when using data dependencies"
                $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) ->
                   let g = generatedGraph
                       ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                         where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)
                       ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                       nticd = PDF.isinkDFTwoFinger g
                       ntiod =  ODEP.ntiodFastPDomSimpleHeuristic g
                       slicer = combinedBackwardSlice g (ddep ⊔ nticd) ntiod 
                   in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 ->
                        let ms  = [m1, m2, m3]
                            msS = Set.fromList ms
                            g' = foldr (flip delSuccessorEdges) g ms
                            nticd' = PDF.isinkDFTwoFinger g'
                            empty = Map.empty
                            slicer' = combinedBackwardSlice g (ddep ⊔ nticd') empty
                        in slicer msS == slicer' msS
                      ))),
      testProperty "nticdNTIODSlice == nticdNTIODSliceViaNticd even when using data dependencies, for random slice-criteria of random size "
                $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) seed1 seed2->
                   let g = generatedGraph
                       n  = length $ nodes g
                       ms
                         | n == 0 = []
                         | n /= 0 = [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                       ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                         where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)
                       ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                       nticd = PDF.isinkDFTwoFinger g
                       ntiod =  ODEP.ntiodFastPDomSimpleHeuristic g
                       slicer = combinedBackwardSlice g (ddep ⊔ nticd) ntiod
                       
                       msS = Set.fromList ms
                       g' = foldr (flip delSuccessorEdges) g ms
                       nticd' = PDF.isinkDFTwoFinger g'
                       empty = Map.empty
                       slicer' = combinedBackwardSlice g (ddep ⊔ nticd') empty
                   in slicer msS == slicer' msS,
    testProperty "wodTEIL ⊑ ntiod ∪ nticd*"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    wodTEIL'    = ODEP.wodTEIL'PDom g
                    ntiod       = ODEP.ntiodFastPDomSimpleHeuristic g
                    nticdslicer = SLICE.NTICD.nticdSlice g
                in (∀) (Map.assocs wodTEIL') (\((m1,m2), ns) ->  (∀) ns (\n ->
                       n ∈ ntiod ! (m1,m2)                 ∨  n ∈ ntiod ! (m2,m1)
                    ∨  n ∈ nticdslicer (Set.fromList [m1]) ∨  n ∈ nticdslicer (Set.fromList [m2])
                   )),
      testProperty  "sinkdomOfLfp m2                 == mustOfLfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               sinkdom2 = PDOM.sinkdomOfGfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ sinkdom2 ! n)
                           ))
                       ),
    testProperty "unique node property for nticdNTIODPDomSimpleHeuristic"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    ntiodslicer   = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    wodteilslicer = SLICE.ODEP.wodTEILPDomSlice g
                    property1 s s' g' unique = (∀) s' (\n -> (length (unique ! n) <= 1))
                    property2 s s' g' unique = (∀) s' (\n -> (∀) (suc g n) (\n' ->
                                                 (n' ∈ s) ∨ (unique ! n == unique ! n')
                                               ))
                    uniqueOf s s' g' = Map.fromList [ (n, [ m | m <- reachable n g', m ∈ s]) | n <- Set.toList s' ]

                in   (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       let ms = Set.fromList [m1,m2]
                           s  = ntiodslicer ms
                           s' = Set.fromList (nodes g) ∖ s
                           g' = efilter ((\(n,m,_) -> n ∈ s')) g
                           unique = uniqueOf s s' g'
                       in   property1 s s' g' unique
                          ∧ property2 s s' g' unique
                          ∧ (∀) s (\n -> n ∈ ms  ∨
                              let sn  = Set.delete n s
                                  sn' = Set.insert n s'
                                  gn' = efilter ((\(n,m,_) -> n ∈ sn')) g
                                  uniquen = uniqueOf sn sn' gn'
                              in  (not $ property1 sn sn' gn' uniquen)
                                ∨ (not $ property2 sn sn' gn' uniquen)
                           )
                     ))
                   ∧ (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       let ms = Set.fromList [m1,m2]
                           s  = wodteilslicer ms
                           s' = Set.fromList (nodes g) ∖ s
                           g' = efilter ((\(n,m,_) -> n ∈ s')) g
                           unique = uniqueOf s s' g'
                       in   property1 s s' g' unique
                          ∧ (∀) s (\n -> n ∈ ms  ∨
                              let sn  = Set.delete n s
                                  sn' = Set.insert n s'
                                  gn' = efilter ((\(n,m,_) -> n ∈ sn')) g
                                  uniquen = uniqueOf sn sn' gn'
                              in  (not $ property1 sn sn' gn' uniquen)
                           )
                     )),
    testPropertySized 40 "noJoins mmay'"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (∀) (nodes g) (\m ->
                         PDF.noJoins g $ ODEP.mmayOf' g m
                       ),
    testProperty "nticdNTIODPDomSimpleHeuristic == nticdNTIODViaWDSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    ntiodteilslicer  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    wdslicer         = FCACD.nticdNTIODViaWDSlice          g
                    ntiodteilslicer' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    wdslicer'        = FCACD.nticdNTIODViaWDSlice          g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       ntiodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ ntiodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testPropertySized 30 "wodTEILSlice  == wodTEILSliceViaBraunF2"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice           g
                    wdslicer         = FCACD.wodTEILSliceViaBraunF2 g
                    wodteilslicer'   = SLICE.ODEP.wodTEILSlice           g'
                    wdslicer'        = FCACD.wodTEILSliceViaBraunF2 g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> if m1 == m2 then True else
                       wodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ wodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testPropertySized 40 "wodTEILSlice  == wdSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice g
                    wdslicer         = FCACD.wdSlice      g
                    wodteilslicer'   = SLICE.ODEP.wodTEILSlice g'
                    wdslicer'        = FCACD.wdSlice      g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       wodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ wodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testProperty "wodTEILSlice = wodTEILSliceViaNticd for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice g
                    wodteilslicer'   = SLICE.NTICD.wodTEILSliceViaNticd g
                in wodteilslicer ms  == wodteilslicer' ms,
    testProperty "wodTEILSliceViaNticd  == wdSlice for CFG-shaped graphs and randomly selected nodes"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 seed3 ->
  --               let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
  --                   [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
  --                   g = insEdge (exit, entry, ()) generatedGraph
                let g = generatedGraph
                    nrSlices = 10
                    n = length $ nodes g
                    mss = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    wdslicer  = FCACD.wdSlice g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g
                in (∀) mss (\ms ->
                     wdslicer ms == wodslicer ms
                   ),
    testProperty "wodTEILSliceViaNticd  ∩ fromM == wccSlice for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
                    n  = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    fromMs = Set.fromList $ dfs (Set.toList ms) g
                    wccslicer  = FCACD.wccSlice g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g
                in wccslicer ms == wodslicer ms ∩ fromMs,
    testProperty "wodTEILSliceViaNticd  == wdSlice for randomly selected nodes"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    nrSlices = 10
                    n = length $ nodes g
                    mss
                      | n == 0 = []
                      | n /= 0 = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    wdslicer  = FCACD.wdSlice g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g
                in (∀) mss (\ms ->
                     wdslicer ms == wodslicer ms
                   ),
    testProperty "wodTEILSliceViaNticd  == wdSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    wodteilslicer    = SLICE.NTICD.wodTEILSliceViaNticd g
                    wdslicer         = FCACD.wdSlice      g
                    wodteilslicer'   = SLICE.NTICD.wodTEILSliceViaNticd g'
                    wdslicer'        = FCACD.wdSlice      g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       wodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ wodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testProperty "wccSliceViaNticdNTIODPDomSimpleHeuristic  == wccSlice for randomly selected nodes"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                    wccSlicer  = FCACD.wccSlice g
                    wccSlicer' = SLICE.ODEP.wccSliceViaNticdNTIODPDomSimpleHeuristic g
                in wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2]),
    testPropertySized 40 "wccSliceViaNticdNTIODSliceSimple  == wccSlice for randomly selected nodes"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                    wccSlicer  = FCACD.wccSlice g
                    wccSlicer' = NTIODSlice.wccSliceViaNticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g
                in -- traceShow (length $ nodes g) $
                   wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2]),
    testPropertySized 70 "wccSliceViaNticdNTIODSliceSimple  == wccSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                    wccSlicer  = FCACD.wccSlice g
                    wccSlicer' = NTIODSlice.wccSliceViaNticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g
                in wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2]),
    testPropertySized 70 "wccSliceViaNticdNTIODSliceSimple  == wccSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g   =      generatedGraph
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                     let wccSlicer  = FCACD.wccSlice g
                         wccSlicer' = NTIODSlice.wccSliceViaNticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g
                     in wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2])
                   )),
    testPropertySized 40 "wodTEILSlice g ms = nticdNTIODFastSlice g{ n | n ->* ms} ms"
    $ \(ARBITRARY(generatedGraph)) ->
                let g   =      generatedGraph
                    rev = grev generatedGraph
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                     let g' = subgraph (List.nub $ (reachable m1 rev) ++ (reachable m2 rev)) g
                         nticdntiodslicer  = SLICE.ODEP.nticdNTIODFastSlice g'
                     in wodteilslicer (Set.fromList [m1, m2]) == nticdntiodslicer (Set.fromList [m1, m2])
                   )),
    testProperty "wodTEILPDomSlice = wodTEILSliceViaNticd"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    nrSlices = 10
                    n = length $ nodes g
                    mss
                      | n == 0 = []
                      | n /= 0 = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    wodteilslicer    = SLICE.ODEP.wodTEILPDomSlice g
                    wodteilslicer'   = SLICE.NTICD.wodTEILSliceViaNticd g
                in (∀) mss (\ms ->
                     wodteilslicer ms  == wodteilslicer' ms
                   ),
    testPropertySized 60 "wodTEILPDomSlice g ms = nticdNTIODSliceSimple g{ n | n ->* ms} ms"
    $ \(ARBITRARY(generatedGraph)) ->
                let g   =      generatedGraph
                    rev = grev generatedGraph
                    wodteilslicer    = SLICE.ODEP.wodTEILPDomSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                     let g' = subgraph (List.nub $ (reachable m1 rev) ++ (reachable m2 rev)) g
                         nticdntiodslicer  = NTIODSlice.nticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g'
                     in wodteilslicer (Set.fromList [m1, m2]) == nticdntiodslicer (Set.fromList [m1, m2])
                   )),
    testProperty "wodTEIL  in sinks via pdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = controlSinks g0
                in (∀) sinks (\sink ->
                     let g = subgraph sink g0
                         wodTEIL'  = ODEP.wodTEIL' g
                         condNodes = [ n | n <- sink, (length $ suc g n) > 1 ]
                     in wodTEIL' == (∐) [ Map.fromList [ ((m1,m2), ns), ((m2,m1), ns) ] 
                                                | m2 <- nodes g,
                                                  let pdom = PDOM.sinkdomOfGfp $ delSuccessorEdges g m2,
                                                  m1 <- nodes g,
                                                  m1 /= m2,
                                                  let ns = Set.fromList [ n | n <- condNodes, n /= m1, n /= m2, not $ (∀) (suc g n) (\x -> m1 ∈ pdom ! x), (∃) (suc g n) (\x ->  m1 ∈ pdom ! x) ]
                                        ]
                   ),
    testProperty "wodTEIL == ntiod in sink subgraphs"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = controlSinks g0
                in (∀) sinks (\sink ->
                     let g = subgraph sink g0
                         wodTEIL'  = ODEP.wodTEIL' g
                         ntiod     = ODEP.ntiodFast g
                         ntiodSym  = (∐) [ Map.fromList [ ((m1,m2), ns), ((m2,m1), ns) ] | ((m1,m2),ns) <- Map.assocs ntiod ]
                     in wodTEIL' == ntiodSym
                   ),
    testPropertySized 40 "lfp fMay                 == lfp fMay'"
    $ \(ARBITRARY(g)) ->
                    let lfp      = ODEP.smmnLfp g ODEP.fMay
                        lfp'     = ODEP.smmnLfp g ODEP.fMay'
                    in  lfp                  == lfp',
    testPropertySized 40 "wodDef                    == wodFast"
    $ \(ARBITRARY(g)) ->
                    let wodDef   = ODEP.wodDef  g
                        wodFast  = ODEP.wodFast g
                    in  wodDef == wodFast,
    testPropertySized 60 "ntiod ⊑ wodTEIL'"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiod = ODEP.ntiod g
                        wodTEIL' = ODEP.wodTEIL' g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ns ⊑ (wodTEIL' ! (m1,m2))
                        ),
     testProperty  "ntiodFromSliceStep == ntiodFast"
     $ \(ARBITRARY(generatedGraph)) ->
                 let g0 = generatedGraph
                     sinks = controlSinks g0
                 in
                    (∀) sinks (\sink ->
                      let g = subgraph sink g0
                          ntiod = ODEP.ntiodFast g
                      in (∀) sink (\m1 -> (∀) sink (\m2 -> (m1 == m2) ∨
                           (NTIODSlice.ntiodFromSliceStep g m1 m2) == ntiod ! (m1,m2) ∪ ntiod ! (m2,m1)
                         ))
                    ),
    testPropertySized 60 "ntiodSlice == ntiodFastSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = controlSinks g0
                in
                   (∀) sinks (\sink ->
                     let g = subgraph sink g0
                         ntiodslicer     = NTIODSlice.ntiodSlice g
                         ntiodfastslicer = SLICE.ODEP.ntiodFastSlice g
                     in (∀) sink (\m1 -> (∀) sink (\m2 -> (m1 == m2) ∨
                          ntiodslicer m1 m2 == ntiodfastslicer (Set.fromList [m1, m2])
                        ))
                   ),
    testPropertySized 20 "ntiodSlice == ntiodFastPDomSimpleHeuristicSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodslicer     = NTIODSlice.ntiodSlice g
                    ntiodpdomslicer = SLICE.ODEP.ntiodFastPDomSimpleHeuristicSlice g
                in  (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                       ntiodslicer m1 m2 == ntiodpdomslicer (Set.fromList [m1, m2])
                    )),
     testProperty  "ntiodFromSimpleSliceStep cutNPasteIfPossible == ntiodFast"
     $ \(ARBITRARY(generatedGraph)) ->
                 let g = generatedGraph
                     ntiod = ODEP.ntiodFast g
                     ntiodslicestep = NTIODSlice.ntiodFromSimpleSliceStep NTIODSlice.cutNPasteIfPossible g
                 in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                           ntiodslicestep m1 m2 == ntiod ! (m1,m2) ∪ ntiod ! (m2,m1)
                    )),
    testProperty  "ntiodSliceSimple cutNPasteIfPossible == ntiodFastSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.cutNPasteIfPossible g
                    ntiodfastslicer   = SLICE.ODEP.ntiodFastSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                          ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodfastslicer (Set.fromList [m1, m2])
                   )),
    testPropertySized 15  "ntiodSliceSimple cutNPasteIfPossible == ntiodFastPDomSimpleHeuristicSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.cutNPasteIfPossible g
                    ntiodpdomslicer = SLICE.ODEP.ntiodFastPDomSimpleHeuristicSlice g
                in  (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                       ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodpdomslicer (Set.fromList [m1, m2])
                    )),
    testProperty  "ntiodFromSimpleSliceStep recompute == ntiodFast"
     $ \(ARBITRARY(generatedGraph)) ->
                 let g = generatedGraph
                     ntiod = ODEP.ntiodFast g
                     ntiodslicestep = NTIODSlice.ntiodFromSimpleSliceStep NTIODSlice.recompute g
                  in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                           ntiodslicestep m1 m2 == ntiod ! (m1,m2) ∪ ntiod ! (m2,m1)
                  )),
    testProperty  "ntiodSliceSimple recompute == ntiodFastSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.recompute g
                    ntiodfastslicer   = SLICE.ODEP.ntiodFastSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                          ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodfastslicer (Set.fromList [m1, m2])
                   )),
    testPropertySized 30  "ntiodSliceSimple recompute           == ntiodFastPDomSimpleHeuristicSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.recompute g
                    ntiodpdomslicer = SLICE.ODEP.ntiodFastPDomSimpleHeuristicSlice g
                in  (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                       ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodpdomslicer (Set.fromList [m1, m2])
                    )),
    testPropertySized 40  "ntiodSliceSimple recompute           == ntiodSliceSimple recomputecutNPasteIfPossible for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodsimpleslicer  = NTIODSlice.ntiodSliceSimple NTIODSlice.recompute           g
                    ntiodsimpleslicer' = NTIODSlice.ntiodSliceSimple NTIODSlice.cutNPasteIfPossible g
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                in  ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodsimpleslicer' (Set.fromList [m1, m2]),
    testPropertySized 60 "wodTEIL' == wodTeil'PDom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.wodTEIL'       g ==
                       ODEP.wodTEIL'PDom   g,
    testPropertySized 20 "dominator trees of (gN|{m |  m ->* n}) from dominator trees of gN in CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(g)) ->
                let nodeS = Set.fromList $ nodes g
                    [entry] = [ n | n <- nodes g, pre g n == [] ]
                    [exit]  = [ n | n <- nodes g, suc g n == [] ]
                    g' = insEdge (exit, entry, ()) g
                in (∀) (nodes g) (\n ->  n == entry   ∨   n == exit   ∨
                     let gN   = delSuccessorEdges g  n
                         g'N  = delSuccessorEdges g' n

                         gToN = subgraph keep' gN
                         
                         isinkdom  = PDOM.isinkdomOfTwoFinger8 gToN
                         isinkdom' = PDOM.isinkdomOfTwoFinger8 g'N
                         keep' = reachable n (grev gN)
                     in  isinkdom == restrict isinkdom' (Set.fromList keep')
                   ),
    testProperty  "cut and re-validate property in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = [ (g, gn, sink, ipdom, condNodes) | sink <-  controlSinks g0,
                                                let towardsSink = [ n | n <- nodes g0, (∃) sink (\s -> s `elem` reachable n g0) ],
                                                let g = subgraph towardsSink g0,
                                                let gn   = Map.fromList [ (n, delSuccessorEdges       g  n)    | n <- towardsSink ],
                                                let condNodes = Map.fromList [ (n, succs) | n <- towardsSink, let succs = suc g n, length succs > 1],
                                                let ipdom = Map.fromList [ (n, PDOM.isinkdomOfTwoFinger8 $ gn  ! n)    | n <- towardsSink ]
                            ]
                in (∀) sinks (\(g,gn,sink, ipdom, condNodes) ->
                            (∀) sink (\m -> 
                              (∀) sink (\n ->
                                   if (m == n) then True else
                                   let -- ipdomM'   = Map.union (Map.fromList [(n', Set.fromList [m]) | n' <- pre g m ]) (ipdom ! n)
                                       ipdomM''  = Map.insert m Set.empty (ipdom ! n)
                                       succs    = [ x | x <- suc g n, isReachableFromTree ipdomM'' m x]
                                       mz = foldM1 (LCA.lca (fmap fromSet ipdomM'')) succs
                                       ipdomM''' = Map.insert n (toSet mz) ipdomM''
                                  in if List.null succs then
                                       let nIsCond = Map.member n condNodes
                                           nonSinkCondNodes = Map.fromList [ (c, succs) | (c, succs) <- Map.assocs condNodes, c /= m]
                                           processed0 = Set.fromList [ x            | x <- nodes (gn ! m), m ∈ reachableFromTree ipdomM'' x]
                                           imdom0     = (if nIsCond then id else Map.insert n (fromSet $ Set.fromList $ suc (gn ! m) n)) $
                                                        Map.fromList [ (x, Nothing)   | x <- nodes (gn ! m), not $ x ∈ processed0, Map.member x nonSinkCondNodes] `Map.union` (fmap fromSet ipdomM'')
                                           worklist0  = Dequeue.fromList [ (x, succs) | x <- nodes (gn ! m), not $ x ∈ processed0, Just succs <- [Map.lookup x nonSinkCondNodes]]
                                           ipdomM'''' = -- traceShow (Map.size nonSinkCondNodes, Seq.length worklist0) $
                                                        fmap toSet $ PDOM.isinkdomOftwoFinger8Up (gn ! m) nonSinkCondNodes worklist0 processed0 (invert''' imdom0) imdom0
                                       in (∀) sink (\y ->
                                               reachableFromTree  ipdomM''''  y
                                            ⊇  reachableFromTree (ipdom ! m) y
                                          )
                                     else
                                       assert (mz /= Nothing) $
                                       (∀) sink (\y ->
                                             reachableFromTree  ipdomM'''  y
                                          ⊇  reachableFromTree (ipdom ! m) y
                                       )
                              ))
                   ),
    testProperty  "pmay properties in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = [ (g, sink, pdom, pmay, dom, condNodes) | sink <-  controlSinks g0,
                                                   let g = subgraph sink g0,
                                                   let gn   = Map.fromList [ (n, delSuccessorEdges       g  n)    | n <- sink ],
                                                   let gn'  = Map.fromList [ (n, delSuccessorEdges (grev g) n)    | n <- sink ],
                                                   let pdom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn  ! n)    | n <- sink ],
                                                   let  dom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn' ! n)    | n <- sink ],
                                                   let pmay = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn  ! n)    | n <- sink ],
                                                   let condNodes = Set.fromList [ n | n <- sink, length (suc g n) > 1]
                            ]
                in (∀) sinks (\(g,sink, pdom, pmay, dom, condNodes) ->
                            (∀) sink (\n -> (∀) condNodes (\c -> (∀) sink (\m2 -> if (c == m2) then True else
                               ((∀) (suc g c) (\x -> not $ m2 ∈ (pmay ! n) ! x))   ↔   ((n /= m2) ∧ (n /= c) ∧ (not $ m2 ∈ (pmay ! n) ! c))
                            )))
                   ),
    testProperty  "pdom swap properties in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = [ (sink, pdom, pmay, dom) | sink <-  controlSinks g0,
                                                   let g = subgraph sink g0,
                                                   let gn   = Map.fromList [ (n, delSuccessorEdges       g  n)    | n <- sink ],
                                                   let gn'  = Map.fromList [ (n, delSuccessorEdges (grev g) n)    | n <- sink ],
                                                   let pdom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn  ! n)    | n <- sink ],
                                                   let  dom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn' ! n)    | n <- sink ],
                                                   let pmay = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn  ! n)    | n <- sink ]
                            ]
                in (∀) sinks (\(sink, pdom, pmay, dom) ->
                            (∀) sink (\x -> (∀) sink (\m1 -> (∀) sink (\m2 -> (∀) sink (\n -> if (m1 == m2 ∨ m1 == x ∨ m2 == x) ∨ (m2 == n) then True else
                               ((not $ m2 ∈ (pmay ! n) ! m1) →
                                                  (( let b0 = m2 ∈ (pmay ! n) ! x
                                                         b1 = m1 ∈ (pdom ! n) ! x
                                                     in (not b0) ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((       x ∈ ( dom ! n) ! m2) →
                                                  (( let b0 = x  ∈ ( dom ! n) ! m1
                                                         b1 = m1 ∈ ( dom ! n) ! m2
                                                     in b0 ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((not $ m2 ∈ (pmay ! n) ! x) →                       -- useless??
                                                   ((let b0 = m1 ∈ (pdom ! n) ! x
                                                         b1 = m1 ∈ ( dom ! n) ! m2
                                                     in b0 ∨ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((not $ m1 ∈ (pmay ! n) ! x) →
                                                   ((let b0 = m2 ∈ (pmay ! n) ! x
                                                         b1 = m1 ∈ ( dom ! n) ! m2
                                                     in (not b0) ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((      m2 ∈ (pdom ! n) ! x) →
                                                  (( let b0 = m1 ∈ (pdom ! n) ! x
                                                         b1 = m2 ∈ (pdom ! n) ! m1
                                                     in b0 ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                    ))))),
    testProperty  "dom/may swap properties in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g0 = generatedGraph
                        sinks = controlSinks g0
                    in (∀) sinks (\sink ->
                         let g = subgraph sink g0
                             gn   = Map.fromList [ (n,        delSuccessorEdges    g n) | n <- sink ]
                             gn'  = Map.fromList [ (n, grev $ delPredecessorEdges  g n) | n <- sink ]
                             pdom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn  ! n)    | n <- sink ]
                             pmay = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn  ! n)    | n <- sink ]
                             dom  = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn' ! n)    | n <- sink ]
                             may  = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn' ! n)    | n <- sink ]
                         in (∀) sink (\n -> (∀) sink (\m1 -> (∀) sink (\m2 -> if (n == m1 ∨ n == m2 ∨ m1 == m2) then True else
                               (  (m1 ∈ (pdom ! n) ! m2)     ↔     (      m1 ∈ ( dom ! m2) ! n )  )
                             ∧ (  (m1 ∈ (pdom ! n) ! m2)     ↔     (not $ n  ∈ (pmay ! m1) ! m2)  )
                             ∧ (  (m1 ∈ ( dom ! n) ! m2)     ↔     (not $ n  ∈ ( may ! m1) ! m2)  )
                             ∧ (  (m1 ∈ (pmay ! n) ! m2)     ↔     (      m2 ∈ ( may ! n ) ! m1)  )
                            )))
                       ),
  testProperty  "allDom ! n == pdom ! n"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        allDom = NTICDUnused.allDomNaiveGfp g
                    in  (∀) (nodes g) (\n ->
                         let pdom = PDOM.sinkdomOfGfp (delSuccessorEdges g n)
                         in (∀) (nodes g) (\m -> (m ∈ pdom ! n)   ==   (Map.member m (allDom ! n)   ∧   n ∈ allDom ! n ! m))
                        ),
  testProperty  "isTransitive myDom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in  isTransitive $ (fromSuccMap $ NTICDUnused.myDom g :: Gr () ()),
  testPropertySized 40  "isTransitive myDom  for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                    in  isTransitive $ (fromSuccMap $ NTICDUnused.myDom g :: Gr () ()),
  testProperty  "myCDFromMyDom == myCD"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                    in  (Set.fromList $ edges myCDFromMyDomTrc) == (Set.fromList $ edges myCDTrc),
  testPropertySized 40  "myCDFromMyDom == myCD  for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                    in  (Set.fromList $ edges myCDFromMyDomTrc) == (Set.fromList $ edges myCDTrc),
  testPropertySized 50  "wodTEILSlice is contained in wodMyEntryWodMyCDSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticdWodSlice   = NTICDUnused.wodMyEntryWodMyCDSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice           g
                    in  (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice (Set.fromList [m1, m2]) ⊆ nticdWodSlice (Set.fromList [m1, m2])
                        )),
  testPropertySized 30  "wodTEILSlice is contained in wodMyEntryWodMyCDSlice for CFG-shaped graphs with exit->entry edge " 
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        nticdWodSlice   = NTICDUnused.wodMyEntryWodMyCDSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice           g
                    in  (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          let s  = wodTEILSlice (Set.fromList [m1, m2])
                              s' = nticdWodSlice (Set.fromList [m1, m2])
                          in s ⊆ s'
                        )),
  testPropertySized 30  "wodTEILSlice is contained in nticdNTIODSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticdWodSlice   = SLICE.ODEP.nticdNTIODSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice g
                    in (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice (Set.fromList [m1, m2]) ⊑   nticdWodSlice (Set.fromList [m1, m2])
                        )),
    testProperty  "ntiod is contained in isinkdom sccs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom  = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        ntiod = ODEP.ntiod g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc isinkdomTrc m2 ∧ m1 ∊ suc isinkdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc isinkdomTrc n2) → (
                                   (n1 == n2) ∨ let [n1'] = Set.toList $ isinkdom ! n1 in n1 ∊ suc isinkdomTrc n1'
                              )
                          ))
                        ∧ (∀) ns (\n -> (∀) (isinkdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc isinkdomTrc m1 ∧ m1 ∊ suc isinkdomTrc m   ∧   m ∊ suc isinkdomTrc m2 ∧ m2 ∊ suc isinkdomTrc m)
                          ))
                        ),
    testProperty  "snmF3Gfp reachable          == isinkdom reachable "
                $ \(ARBITRARY(generatedGraph)) ->
                    let graph     = generatedGraph
                        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
                        s3        = SNM.snmF3 graph
                        isinkdom     = PDOM.TRANS.isinkdomOfSinkContraction graph
                        isinkdomTrc  = trc $ (fromSuccMap isinkdom :: Gr () ())
                    in (∀) (nodes graph) (\m ->
                         (∀) condNodes (\n ->     ((n == m) ∨ (Set.size (s3 ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)))
                                               ↔ (m ∊ (suc isinkdomTrc n))
                         )
                       ),
    testProperty  "rotatePDomAround g (pdom_n) (n->m)  == pdom_m in arbitrary control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                    let sinks = controlSinks generatedGraph
                    in (∀) sinks (\sink -> let g = subgraph sink generatedGraph in
                         (∀) (nodes g) (\n ->
                           let gn   = efilter (\(x,y,_) -> x /= n) g
                               pdom = fmap fromSet $ PDOM.isinkdomOfTwoFinger8 gn
                               condNodes = Map.fromList [ (x, succs) | x <- nodes g, let succs = suc g x, length succs  > 1 ]
                           in    (∀) (suc g n) (\m -> if m == n then True else
                                  let pdom' = fmap fromSet $ PDOM.isinkdomOfTwoFinger8 gm
                                        where gm = delSuccessorEdges g m
                                      rpdom' = ODEP.rotatePDomAround g condNodes pdom (n,m)
                                  in pdom' == rpdom'
                                 )
                         )
                       ),
    testPropertySized 20  "ntiodFromMay            == ntiodFast for CFG-shaped graphs with exit->entry edge"  -- but: see InvalidProperties.hs
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        ntiodFromMay = NTICDUnused.ntiodFromMay g
                        ntiodFast    = ODEP.ntiodFast    g
                    in ntiodFromMay == ntiodFast,
    testProperty  "ntiodFastPDom*            == ntiodFast"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiodFastPDomSimpleHeuristic = ODEP.ntiodFastPDomSimpleHeuristic  g
                        ntiodFastPDom                = ODEP.ntiodFastPDom                 g
                        ntiodFast                    = ODEP.ntiodFast                     g
                    in   True
                       ∧ ntiodFastPDomSimpleHeuristic == ntiodFast
                       ∧ ntiodFastPDom                == ntiodFast,
    testPropertySized 20  "ntiodFastPDom*            == ntiodFast for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        ntiodFastPDomSimpleHeuristic  = ODEP.ntiodFastPDomSimpleHeuristic   g
                        ntiodFastPDom                 = ODEP.ntiodFastPDom                  g
                        ntiodFast                     = ODEP.ntiodFast                      g
                    in   True
                       ∧ ntiodFastPDomSimpleHeuristic  == ntiodFast
                       ∧ ntiodFastPDom                 == ntiodFast,
     testProperty  "ntiodFastPDom*            == ntiodFastPDom* for arbitrary graphs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiodFastPDomSimpleHeuristic = ODEP.ntiodFastPDomSimpleHeuristic  g
                        ntiodFastPDom                = ODEP.ntiodFastPDom                 g
                    in   True
                       ∧ ntiodFastPDomSimpleHeuristic == ntiodFastPDom,
    testPropertySized 30  "ntiodFastPDom*             == ntiodFastPDom* for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        ntiodFastPDomSimpleHeuristic  = ODEP.ntiodFastPDomSimpleHeuristic   g
                        ntiodFastPDom                 = ODEP.ntiodFastPDom                  g
                        n = length $ nodes g
                    in -- traceShow (n, sum $ fmap (\s -> if Set.null s then 0 else 1) $ Map.elems ntiodFastPDomSimpleHeuristic, n*n, sum $ fmap Set.size $ Map.elems ntiodFastPDomSimpleHeuristic) $
                         True
                       ∧ ntiodFastPDomSimpleHeuristic  == ntiodFastPDom,
    testProperty  "ntiodFastPDom             == ntiod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntiodFastPDom   g ==
                       ODEP.ntiod           g,
    testProperty  "ntiodFast                 == ntiod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntiodFast       g ==
                       ODEP.ntiod           g
  ]
wodTests = testGroup "(concerning weak order dependence)" $
  [  testCase    ( "ntiod ⊑ wodTEIL' for " ++ exampleName)
            $       let ntiod = ODEP.ntiod g
                        wodTEIL' = ODEP.wodTEIL' g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ns ⊑ (wodTEIL' ! (m1,m2))
                        )@? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "wodTEILSlice is contained in nticdNTIODSlice for " ++ exampleName)
            $       let nticdWodSlice   = SLICE.ODEP.nticdNTIODSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice g
                    in  (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice (Set.fromList [m1, m2])  ⊑  nticdWodSlice (Set.fromList [m1, m2])
                        )) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiod is contained in isinkdom sccs  for " ++ exampleName)
            $       let isinkdom  = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        ntiod = ODEP.ntiod g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc isinkdomTrc m2 ∧ m1 ∊ suc isinkdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc isinkdomTrc n2) → (
                                   (n1 == n2) ∨ let [n1'] = Set.toList $ isinkdom ! n1 in n1 ∊ suc isinkdomTrc n1'
                              )
                          ))
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "myCDFromMyDom == myCD for " ++ exampleName) $
                   let  myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                   in  (Set.fromList $ edges myCDFromMyDomTrc)  == (Set.fromList $ edges myCDTrc) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "isTransitive myDom for " ++ exampleName) $
                   isTransitive (fromSuccMap $ NTICDUnused.myDom g :: Gr () ()) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiodFastPDom               == ntiodFast for " ++ exampleName)
            $ ODEP.ntiodFastPDom g             == ODEP.ntiodFast g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiodFastPDom               == ntiod for " ++ exampleName)
            $ ODEP.ntiodFast g                 == ODEP.ntiod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiodFastPDom               == ntiod for " ++ exampleName)
            $ ODEP.ntiodFastPDom g             == ODEP.ntiod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []


dodProps = testGroup "(concerning decisive order dependence)" [
    testProperty "ntscdNTIOD == ntscdNTSODViaNtscd properties"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g    = generatedGraph
                    trcG = trc g
                    m0S
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                     where n    = length $ nodes g
                in
                -- in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let m0S = Set.fromList [m1, m2] in  -- -} (∀) (nodes g) (\m3 -> (∀) (nodes g) (\m4 -> let m0S = Set.fromList [m1, m2, m3, m4] in
                     let  m0s = Set.toList m0S
                          toM0s = rdfs m0s g
                          g' = foldr (flip delSuccessorEdges) g m0s
                          ntscd' = NTICD.ntscdViaMDom g'
                          nticd'slicer = SLICE.NTICD.ntscdSlice g'
                          mdom' = PDOM.mdomOfLfp g'
                     in (∀) m0S (\m -> (∀) (nticd'slicer (Set.fromList [m])) (\n -> 
                          let ok = (mdom' ! n == Set.fromList [n])
                          in (if ok then id else traceShow (g, m0S, n, m)) ok
                        ))
                   -- )))),
                   ,
  testProperty "ntscdNTSODSlice == ntscdNTSODSliceViaIMDom  for random slice-criteria of random size, and CFG-shaped graphs"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.NTICD.ntscdNTSODSliceViaNtscd   g
                    slicer2  = SLICE.PDOM.ntscdNTSODSliceViaIMDom    g
                in   slicer1  ms == slicer2  ms,
    testPropertySized 40 "ntscdSlice == ntsndDef"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    nticdslicer = SLICE.NTICD.ntscdSlice g
                    ntind = NTICD.ntsndDef g
                in (∀) (nodes g) (\m ->
                     let ms = Set.fromList [m]
                         s  = (nticdslicer ms) ∖ ms
                         s' = Set.fromList [ n | n <- nodes g, m ∈ ntind ! n ]
                     in s == s'
                   ),
    testPropertySized 30 "ntscdNTSODSlice == ntscdNTSODSliceViaNticd for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.ODEP.ntscdNTSODSlice               g
                    slicer2  = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g
                    slicer1' = SLICE.ODEP.ntscdNTSODSlice               g'
                    slicer2' = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g'
                in   slicer1  ms == slicer2  ms
                   ∧ slicer1' ms == slicer2' ms,
    testPropertySized 40 "ntscdNTSODSlice == ntscdNTSODSliceViaNtscd"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    slicer1  = SLICE.ODEP.ntscdNTSODFastPDomSlice       g
                    slicer2  = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g
                    slicer1' = SLICE.ODEP.ntscdNTSODFastPDomSlice       g'
                    slicer2' = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  let ms = Set.fromList [m1, m2] in -- (∀) (nodes g) (\m3 -> let ms = Set.fromList [m1, m2, m3] in 
                       slicer1  ms == slicer2  ms
                     ∧ slicer1' ms == slicer2' ms
                   )), -- ),
      testPropertySized 25  "ntscdNTSODSlice == ntscdNTSODSliceViaNtscd even when using data dependencies"
                $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) ->
                   let g = generatedGraph
                       ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                         where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)
                       ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                       ntscd = PDF.mDFTwoFinger g
                       ntsod =  ODEP.ntsodFastPDom g
                       slicer = combinedBackwardSlice g (ddep ⊔ ntscd) ntsod 
                   in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 ->
                        let ms  = [m1, m2, m3]
                            msS = Set.fromList ms
                            g' = foldr (flip delSuccessorEdges) g ms
                            ntscd' = PDF.mDFTwoFinger g'
                            empty = Map.empty
                            slicer' = combinedBackwardSlice g (ddep ⊔ ntscd') empty
                        in slicer msS == slicer' msS
                      ))),
      testProperty  "mdomOfLfp m2                 == mustOfLfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfLfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               mdom2 = PDOM.mdomOfLfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ mdom2 ! n)
                           ))
                       ),
    testProperty  "|ntsodFastPDom|             >= |dodColoredDagFixedFast|"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               mdom2 = PDOM.mdomOfLfp g2
                           in (∀) condNodes (\n -> (∀) (nodes g) (\m1 -> if m1 == m2 ∨ m1 == n ∨ m2 == n then True else
                                let s12n = must ! (m1,m2,n) in
                                (Set.size s12n == (Set.size $ Set.fromList $ suc g n)) ↔ (m1 ∈ mdom2 ! n)
                           ))
                       ),
    testProperty  "|ntsodFastPDom|             >= |dodColoredDagFixedFast|"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sum = Map.fold (\ns s -> Set.size ns + s) 0
                    in (sum $ ODEP.ntsodFastPDom          g) >=
                       (sum $ ODEP.dodColoredDagFixedFast g),
    testProperty  "ntsodFastPDom               ≡ ntsodFast"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntsodFastPDom   g ≡
                       ODEP.ntsodFast       g,
    testProperty  "ntsodFastPDom               ≡ ntsod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntsodFastPDom   g ≡
                       ODEP.ntsod           g,
    testProperty  "ntsodFast                 == ntsod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntsodFast       g ==
                       ODEP.ntsod           g,
    testProperty  "ntsod is contained in imdom sccs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ),
    testProperty  "ntscdDodSlice == ntscdNTSODSlice property"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntsod = ODEP.ntsod g
                        ntscd = NTICD.ntscdViaMDom g
                        ntscdTrc = trc $ (fromSuccMap ntscd :: Gr () ())
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          (∀) ns (\n -> n ∈ ntsod ! (m2,m1) ∨
                                        (∃) (ns ∩ (ntsod ! (m2, m1))) (\n' -> n' ∊ (suc ntscdTrc n))
                          )
                        ),
    testProperty  "ntscdDodSlice == ntscdNTSODSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntscdDodSlice     = SLICE.ODEP.ntscdDodSlice g
                        ntscdNTSODSlice   = SLICE.ODEP.ntscdNTSODSlice g
                    in  -- traceShow (length $ nodes g) $
                        (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          ntscdDodSlice   (Set.fromList [m1, m2]) ==
                          ntscdNTSODSlice (Set.fromList [m1, m2])
                        )),
    testProperty  "dod implies ntsod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        dod = ODEP.dod g
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          (∀) ns (\n -> n ∈ ntsod ! (m1,m2) ∧
                                        n ∈ ntsod ! (m2,m1)
                          )
                        ),
    testProperty  "ntsod implies dod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        dod = ODEP.dod g
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.keys ntsod) (\(m1,m2) ->
                          (∀) (ntsod ! (m1,m2)  ⊓  ntsod ! (m2,m1)) (\n -> n ∈ dod ! (m1,m2)
                          )
                        ),
    testProperty  "dod is contained in imdom sccs "
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom  = PDOM.imdomOfTwoFinger6 g
                        dod = ODEP.dod g
                        imdomSccs = scc (fromSuccMap imdom :: Gr () ())
                        imdomCycleOf m =  the (m ∊) $ imdomSccs
                    in  (∀) (nodes g) (\m1 ->
                          (∀) (List.delete m1 $ nodes g) (\m2 ->
                            let c1 = imdomCycleOf m1
                                c2 = imdomCycleOf m2
                            in (not (c1 == c2 ∧ length c1 > 1) ) → (Set.null $ dod ! (m1,m2))
                          )
                        ),
    testProperty  "dod is contained in imdom sccs, and only possible for immediate entries into sccs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        dod = ODEP.dod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ),
    testProperty  "snmF3Lfp reachable          == imdom reachable "
                $ \(ARBITRARY(generatedGraph)) ->
                    let graph     = generatedGraph
                        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
                        s3        = SNM.snmF3Lfp graph
                        imdom     = PDOM.imdomOfTwoFinger6 graph
                        imdomTrc  = trc $ (fromSuccMap imdom :: Gr () ())
                    in (∀) (nodes graph) (\m ->
                         (∀) condNodes (\n ->     ((n == m) ∨ (Set.size (s3 ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)))
                                               ↔ (m ∊ (suc imdomTrc n))
                         )
                       ),
    testProperty  "dodColoredDagFixedFast     == dodFast"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodColoredDagFixedFast g ==
                       ODEP.dodFast                 g,
    testProperty  "dodColoredDagFixedFast     == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodColoredDagFixedFast g ==
                       ODEP.dodDef                 g,
    testProperty  "dodColoredDagFixed         == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodColoredDagFixed g ==
                       ODEP.dodDef             g,
    testProperty  "dod                       == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dod           g ==
                       ODEP.dodDef        g,
    testProperty  "dodFast                   == dodDef"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodFast       g ==
                       ODEP.dodDef        g,
    testProperty  "lfp fMustNoReachCheck      == lfp fMust"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.smmnLfp g ODEP.fMustNoReachCheck        ==
                       ODEP.smmnLfp g ODEP.fMust
  ]
dodTests = testGroup "(concerning decisive order dependence)" $
  [  testCase    ( "mdomOfLfp m2              == mustOfLfp for " ++ exampleName)
            $       let  must = ODEP.mustOfLfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               mdom2 = PDOM.mdomOfLfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ mdom2 ! n)
                           ))
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsodFastPDom             ≡ ntsodFast for " ++ exampleName)
            $ ODEP.ntsodFastPDom      g      ≡ ODEP.ntsodFast g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsodFastPDom             ≡ ntsod for " ++ exampleName)
            $ ODEP.ntsodFastPDom      g      ≡ ODEP.ntsod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsodFast                 == ntsod for " ++ exampleName)
            $ ODEP.ntsodFast          g      == ODEP.ntsod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsod is contained in imdom sccs  for " ++ exampleName)
            $       let imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntscdDodSlice == ntscdNTSODSlice property for " ++ exampleName)
            $       let ntsod = ODEP.ntsod g
                        ntscd = NTICD.ntscdViaMDom g
                        ntscdTrc = trc $ (fromSuccMap ntscd :: Gr () ())
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          (∀) ns (\n -> n ∈ ntsod ! (m2,m1) ∨
                                        (∃) (ns ∩ (ntsod ! (m2, m1))) (\n' -> n' ∊ (suc ntscdTrc n))
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntscdDodSlice == ntscdNTSODSlice for " ++ exampleName)
            $       let ntscdDodSlice     = SLICE.ODEP.ntscdDodSlice g
                        ntscdNTSODSlice   = SLICE.ODEP.ntscdNTSODSlice g
                    in  -- traceShow (length $ nodes g) $
                        (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          ntscdDodSlice   (Set.fromList [m1, m2]) ==
                          ntscdNTSODSlice (Set.fromList [m1, m2])
                        )) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dod implies ntsod for " ++ exampleName)
            $       let dod = ODEP.dod g
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          (∀) ns (\n -> n ∈ ntsod ! (m1,m2) ∧
                                        n ∈ ntsod ! (m2,m1)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsod implies dod for " ++ exampleName)
            $       let dod = ODEP.dod g
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.keys ntsod) (\(m1,m2) ->
                          (∀) (ntsod ! (m1,m2)  ⊓  ntsod ! (m2,m1)) (\n -> n ∈ dod ! (m1,m2)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dod is contained in imdom sccs, and only possible for immediate entries into sccs for " ++ exampleName)
            $       let imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        dod = ODEP.dod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dodColoredDagFixedFast        == dodDef for " ++ exampleName)
            $ ODEP.dodColoredDagFixedFast g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dodColoredDagFixed        == dodDef for " ++ exampleName)
            $ ODEP.dodColoredDagFixed g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dod                       == dodDef for " ++ exampleName)
            $ ODEP.dod                g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dodFast                   == dodDef for " ++ exampleName)
            $ ODEP.dodFast            g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []



colorProps = testGroup "(concerning color algorithms)" [
    testProperty  "colorLfpFor                 == smmnFMustWod graph"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap isinkdom :: Gr () ())
                        sMust = ODEP.smmnFMustWod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = ODEP.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc isinkdomTrc n)) ∧ (m2 ∊ (suc isinkdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))),
    testProperty  "colorLfpFor                 == smmnFMustDod graph"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = ODEP.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = ODEP.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))),
    testProperty  "colorLfpFor                 == colorFor"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = ODEP.colorLfpFor g   m1 m2
                         in (∀) (nodes g) (\n ->
                           let color  = ODEP.colorFor    g n m1 m2
                           in (n /= m1 ∧ n /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                                (∀) (suc g n) (\x -> colorLfp ! x == color ! x)
                       ))),
    testProperty  "smmnFMustDod graph          == colorFor"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = ODEP.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (condNodes) (\n ->   (∀) (nodes g) (\m1 ->    (∀) (nodes g) (\m2 ->
                         (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                         let color    = ODEP.colorFor    g n m1 m2
                         in   (∀) (suc g n) (\x -> (color ! x == ODEP.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n)))
                            ∧ (∀) (suc g n) (\x -> (color ! x == ODEP.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n)))
                       )))
  ]
colorTests = testGroup "(concerning color algorithms)" $
  [  testCase    ( "colorLfpFor                 == smmnFMustWod graph for" ++ exampleName)
            $       let isinkdom = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap isinkdom :: Gr () ())
                        sMust = ODEP.smmnFMustWod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = ODEP.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc isinkdomTrc n)) ∧ (m2 ∊ (suc isinkdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "colorLfpFor                 == smmnFMustDod graph for" ++ exampleName)
            $       let imdom = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = ODEP.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = ODEP.colorLfpFor g   m1 m2
                         in (∀) (condNodes) (\n ->
                              (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → (
                                (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n))))
                              ∧ (∀) (suc g n) (\x -> (n /= x) → ((colorLfp ! x == ODEP.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n))))
                              )
                       ))) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "smmnFMustDod graph          == colorFor for " ++ exampleName)
            $       let imdom = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                    in (∀) (nodes g) (\m1 ->   (∀) (nodes g) (\m2 ->
                         let colorLfp = ODEP.colorLfpFor g   m1 m2
                         in (∀) (nodes g) (\n ->
                           let color  = ODEP.colorFor    g n m1 m2
                           in (n /= m1 ∧ n /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                                (∀) (suc g n) (\x -> colorLfp ! x == color ! x)
                       ))) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "colorLfpFor                 == colorFor for " ++ exampleName)
            $       let imdom = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap imdom :: Gr () ())
                        sMust = ODEP.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in (∀) (condNodes) (\n ->   (∀) (nodes g) (\m1 ->    (∀) (nodes g) (\m2 ->
                         (n /= m1 ∧ n /= m2 ∧ m1 /= m2 ∧ (m1 ∊ (suc imdomTrc n)) ∧ (m2 ∊ (suc imdomTrc n))) → 
                         let color    = ODEP.colorFor    g n m1 m2
                         in   (∀) (suc g n) (\x -> (color ! x == ODEP.White)  ↔ ((n,x) ∈ sMust ! (m1,m2, n)))
                            ∧ (∀) (suc g n) (\x -> (color ! x == ODEP.Black)  ↔ ((n,x) ∈ sMust ! (m2,m1, n)))
                       )))
 @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []




nticdProps = testGroup "(concerning nticd )" [
    testPropertySized 40  "nticdFig5GraphP               == nticdF5GraphP    for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdFig5GraphP p        == PROG.nticdF5GraphP p,
    testPropertySized 40  "nticdSinkContraction          == nticdF3GraphP   for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdSinkContractionGraphP p == PROG.nticdF3GraphP p,
    testPropertySized 40  "controlDependenceGraphp       == nticdF3GraphP   for For-Programs, which by construction have the unique end node property"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  controlDependenceGraphP p      == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3'GraphP                == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3'GraphP p         == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3'dualGraphP            == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3'dualGraphP p     == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3'dualWorkListGraphP       == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3'dualWorkListGraphP p  == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3WorkListGraphP         == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3WorkListGraphP p  == PROG.nticdF3GraphP p,
    testPropertySized 40  "nticdF3WorkListSymbolicGraphP == nticdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.nticdF3WorkListSymbolicGraphP p == PROG.nticdF3GraphP p,
    testProperty  "nticdFig5              == nticdF5                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                    in SNM.nticdFig5        g ==
                       SNM.nticdF5          g,
    testProperty  "controlDependence      == nticdF3                for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in controlDependence      g exit ==
                       SNM.nticdF3          g,
    testProperty  "nticdSinkContraction   == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.TRANS.nticdSinkContraction  g ==
                       SNM.nticdF3               g,
    testProperty  "nticdDef               == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdDef         g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3'               == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'         g ==
                       SNM.nticdF3          g,
    testProperty  "snmF3'dual           == snmF3 (dual)"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        snmF3      = SNM.snmF3      g
                        snmF3'dual = SNM.snmF3'dual g
                    in (∀) (Map.assocs snmF3) (\((m,p), mp) ->
                         let mp' = snmF3'dual ! (m,p)
                         in  mp == Set.fromList [ (p,x) | x <- suc g p] ∖ mp'
                       ),
    testProperty  "nticdF3'dual           == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'dual     g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3'dualWorkList        == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'dualWorkList  g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3WorkList        == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3WorkList  g ==
                       SNM.nticdF3          g,
    testProperty  "nticdF3WorkListSymbolic== nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3WorkListSymbolic g ==
                       SNM.nticdF3                 g,
    testProperty  "nticdF3'dorkListSymbolic  == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in SNM.nticdF3'dualWorkListSymbolic g ==
                       SNM.nticdF3                      g
  ]
nticdTests = testGroup "(concerning nticd)" $
  [  testCase    ( "nticdFig5GraphP           ==       nticdF5GraphP for " ++ exampleName)
            $ PROG.nticdFig5GraphP p         == PROG.nticdF5GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdSinkContractionGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdSinkContractionGraphP p == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "controlDependenceGraphP   ==       nticdF3GraphP for " ++ exampleName)
                  $ controlDependenceGraphP p == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFF2GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFF2GraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdDefGraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdDefGraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3'GraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'dualGraphP        ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3'dualGraphP p      == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3WorkListGraphP     ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3WorkListGraphP p   == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3WorkListSymbolicGraphP     ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3WorkListSymbolicGraphP p   == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "nticdF3'dualWorkListSymbolicGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.nticdF3'dualWorkListSymbolicGraphP p   == PROG.nticdF3GraphP p @? ""
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
                                     wod = ODEP.wodFast g
                                     ntscd = NTICD.ntscdViaMDom g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ),
    testPropertySized 4 "wod ⊆ ntscd^* for For-Programs, which by construction are reducible"
                $ \generated -> let  p :: Program Gr = toProgram generated
                                     g = tcfg p
                                     wod = ODEP.wodFast g
                                     ntscd = NTICD.ntscdViaMDom g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ),
    testProperty  "ntscdF4GraphP          == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.ntscdF4GraphP p         == PROG.ntscdF3GraphP p,
                
    testProperty  "ntscdF4WorkListGraphP  == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  PROG.ntscdF4WorkListGraphP p == PROG.ntscdF3GraphP p,
    testProperty  "ntscdF4WorkList == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       SNM.ntscdF4WorkList g ==
                       SNM.ntscdF3         g,
    testProperty  "ntscdF4         == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       SNM.ntscdF4         g ==
                       SNM.ntscdF3         g,
    testPropertySized 60  "ntscdDef        == ntscdF3"
                $ \(ARBITRARY(g)) ->
                       NTICD.ntscdDef        g ==
                       SNM.ntscdF3         g
  ]

ntscdTests = testGroup "(concerning ntscd)" $
  [  testCase    ( "wod ⊆ ntscd^* for                                   " ++ exampleName)
            $                   let  g = tcfg p
                                     wod = ODEP.wodFast g
                                     ntscd = NTICD.ntscdViaMDom g
                                     ntscdTrc = trc $ fromSuccMap ntscd :: Gr () ()
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∊ suc ntscdTrc n)
                                                      ∨ (m2 ∊ suc ntscdTrc n)
                                      )
                                   ) @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdF4GraphP            ==       ntscdF3GraphP for " ++ exampleName)
            $ PROG.ntscdF4GraphP p          == PROG.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdF4WorkListGraphP    ==       ntscdF3GraphP for " ++ exampleName)
            $ PROG.ntscdF4WorkListGraphP p  == PROG.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "ntscdDefGraphP           ==       ntscdF3GraphP for " ++ exampleName)
            $ PROG.ntscdDefGraphP p         == PROG.ntscdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []


timingDepProps = testGroup "(concerning timingDependence)" [
    testProperty "some prop"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom = TSCD.timdomOfLfp g
                    timdomnok = fmap (Set.map fst) $ timdom
                in (∀) (Map.assocs timdom) (\(n, m's) -> (∀) m's (\(m', steps) -> (∀) (timdom ! m') (\(m, steps') ->
                       if (m ∈ timdomnok ! n)   ∨  (n == m  ∨  m == m'  ∨  m' == n)  then True else (
                          True
                        ∧ (let dombefore' = PDOM.mdomOfLfp (delSuccessorEdges g m') in  not $ m  ∈ dombefore' ! n)
                        ∧ (let dombefore  = PDOM.mdomOfLfp (delSuccessorEdges g m ) in  not $ m' ∈ dombefore  ! n)
                        ∧ (∀) (suc g n) (\nr -> if       m ∈ timdomnok ! nr then True else traceShow ("nr", nr) (
                              (let dombefore' = PDOM.mdomOfLfp (delSuccessorEdges g m') in  not $ m  ∈ dombefore' ! nr)
                            ∧ (let dombefore  = PDOM.mdomOfLfp (delSuccessorEdges g m ) in  not $ m' ∈ dombefore  ! nr)
                          ))
                        ∧ (∀) (suc g n) (\nl -> if not $ m ∈ timdomnok ! nl then True else traceShow ("nl", nl) (
                              (let dombefore' = PDOM.mdomOfLfp (delSuccessorEdges g m') in        m  ∈ dombefore' ! nl)
                            ∨ (let dombefore  = PDOM.mdomOfLfp (delSuccessorEdges g m ) in        m' ∈ dombefore  ! nl)
                          ))
                       )
                ))),
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in reducible CFG"
    $ \(REDUCIBLE(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s) ok,
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in CFG with unique exit node"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let (_, g) = withUniqueEndNode () () generatedGraph
                    
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s) ok,
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in CFG with empty ntsod"
    $ \(REDUCIBLE(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    ntsod = ODEP.ntsodFastPDom   g
                    
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in ((∀) (Map.assocs ntsod) (\(_,ns) -> Set.null ns)) ==>
                   let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s, ntsod) ok,
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in CFG with unique exit node, but fixed examples"
    $ \seed1 seed2 seed3 -> (∀) interestingTimingDep (\(exampleName, example) ->
                let (_, g) = withUniqueEndNode () () example
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s) ok
                ),
    testProperty "timingLeaksTransformation tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size, but fixed examples"
    $ \seed1 seed2 seed3 -> (∀) interestingTimingDep (\(exampleName, example) ->
                let g = example :: Gr () ()
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    
                    (cost, _) = TSCD.timingLeaksTransformation g cost0 ms
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g
                    
                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms


                in let ok = (s == s')
                   in if ok then ok else traceShow (g,ms,s',s) ok
                ),
    testProperty "timingCorrection tscdCostSlice g[ms -/> ] ms == ntscdNTSODSlice ms for random slice criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    n = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    cost0 = costFor g seed3
                    
                    (cost,   _) = TSCD.timingLeaksTransformation g   cost0 ms
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g   costF  
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    g'' = foldr (flip delSuccessorEdges) g ms
                    (cost'', _) = TSCD.timingCorrection          g'' cost0
                    costF'' n m = cost'' ! (n,m)
                    tscdcostslicer''  = TSCD.tscdCostSlice           g'' costF''
                    ntscdslicer = SLICE.NTICD.ntscdSlice                g''
    
                    s    = tscdcostslicer    ms
                    s'   = ntscdntsodslicer  ms
                    s''  = tscdcostslicer''  ms
                    s''' = ntscdslicer       ms
                in let ok = (s == s') ∧ (s == s'') ∧ (s == s''') ∧ ((Map.keysSet cost ⊇ Map.keysSet cost'') ∧ (∀) (Map.assocs cost'') (\((n,m),k) -> cost ! (n,m) <= k))
                   in if ok then ok else traceShow (g,ms,cost0, s,s', s'') $ traceShow ("cost:",cost, cost'') $ ok,
    testProperty "timingCorrection itimdomMultiple"
    $ \(ARBITRARY(generatedGraph)) seed3 ->
                let g = generatedGraph
                    (cost, itimdomMultiple') = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    itimdomMultiple'' = TSCD.itimdomMultipleOfTwoFingerCost g (\n m -> cost ! (n,m))
                    noselfloops = Map.mapWithKey (\n ms -> Set.filter (\(m, k) -> m /= n) ms)
                in noselfloops itimdomMultiple'' == noselfloops itimdomMultiple',
    testProperty "timingCorrection imdom"
    $ \(ARBITRARY(generatedGraph)) seed3 ->
                let g = generatedGraph
                    (cost, itimdomMultiple') = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    itimdomMutliple'NoK = fmap (Set.map fst) itimdomMultiple'
                    imdom = PDOM.imdomOfTwoFinger6 g
                    -- noselfloops = Map.mapWithKey (\n ms -> Set.filter (/= n) ms)
                in (trc $ fromSuccMap $ itimdomMutliple'NoK :: Gr () ()) == (trc $ fromSuccMap $ imdom :: Gr () ()),
    testProperty "timdom implies mdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    mdom   = PDOM.mdomOfLfp g
                in timdom ⊑ mdom,
    testProperty "tscd implies dom"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    tscd = TSCD.tscdOfLfp g
                in (∀) (Map.assocs $  tscd) (\(n, ms) -> (∀) ms (\m -> (m == n) ∨ (not $ m ∈ timdom ! n))),
    testProperty "tscd implies onedome"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    onedom = PDOM.onedomOf timdom
                    tscd = TSCD.tscdOfLfp g
                in (∀) (Map.assocs $  tscd) (\(n, ms) -> (∀) ms (\m -> not $ m ∈ onedom n)),
    testProperty "fmap (Set.map fst) $ timdomOfLfp is transitive in reducible CFG"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                in (∀) (Map.assocs $  timdom) (\(x, ys) -> (∀) ys (\y -> (∀) (timdom ! y) (\z -> z ∈ timdom ! x ))),
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp via validTimdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g
                    valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdom (Set.fromList $ nodes g)
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                     let fuel = valid ! x in
                           (∀) ys (\(y, steps) -> (∀) (timdomMultipleNaive ! y) (\(z, steps') ->
                             -- (if (fuel > 1) then traceShow (steps + steps', fuel, steps + steps'  <= fuel) else id) $
                             ((z, (steps + steps'          )          ) ∈ timdom ! x)    ↔  (steps + steps'  <= fuel )
                           ))
                       ∧ (∀) [0..fuel-1] (\fuel' ->
                           not $
                           (∀) ys (\(y, steps) -> (∀) (timdomMultipleNaive ! y) (\(z, steps') ->
                             ((z, (steps + steps'          )          ) ∈ timdom ! x)    ↔  (steps + steps'  <= fuel')
                           ))
                         )
                   ),
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                         (∃) [0..n] (\fuel ->
                           (∀) ys (\(y, steps) -> (∀) (timdomMultipleNaive ! y) (\(z, steps') ->
                             ((z, (steps + steps'          )          ) ∈ timdom ! x)    ↔  (steps + steps'  <= fuel)
                           ))
                         )
                   ),
    testProperty "itimdom cycles vs timdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g

                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdom ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdom
                    cycleNodes = (∐) cycles
                in (∀) cycles (\cycle ->
                     let circumference = sum [ steps | m <- Set.toList cycle, (_,steps) <- Set.toList $  itimdom ! m]
                     in (∀) cycle (\m -> (∀) cycle (\m' -> 
                            False
                          ∨ (m == m')
                          ∨ (   (m' ∈ (Set.map fst $ timdom ! m ))
                              ∧ (m  ∈ (Set.map fst $ timdom ! m'))
                              ∧ (∀) (Set.filter ((==m') . fst) $ timdom ! m ) (\(_,k)  ->
                                (∀) (Set.filter ((==m ) . fst) $ timdom ! m') (\(_,k') ->
                                  (k + k' == circumference)
                                ))
                            )
                       ))
                    ),
    testProperty "timdomMultipleOfNaiveLfp step vs fuel"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g
                    valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdom (Set.fromList $ nodes g)

                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdom ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdom
                    cycleNodes = (∐) cycles
                in (∀) (Map.assocs itimdom) (\(m, m's) -> (∀) (m's) (\(m', steps) ->
                          False
                        ∨ (m == m')
                        ∨ (   (m' ∈ (Set.map fst $ timdom ! m ))
                            ∧ (m  ∈ (Set.map fst $ timdom ! m'))
                            ∧ (∀) (Set.filter ((==m') . fst) $ timdom ! m ) (\(_,k)  ->
                              (∀) (Set.filter ((==m ) . fst) $ timdom ! m') (\(_,k') ->
                                  True
                                ∧ (k == steps)
                                ∧ (k + k' == (valid ! m') + k)
                              ))
                          )
                        ∨ (m ∈ entries)
                        ∨ (valid ! m == valid ! m' + steps)
                   )),
    testProperty "validTimdomFor entries == validTimdomFor (nodes g) | entries "
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    itimdommultiple = TSCD.itimdomMultipleOfTwoFinger g
                    valid        = TSCD.validTimdomFor g (TSCD.cost1F g) itimdommultiple (Set.fromList $ nodes g)
                    validEntries = TSCD.validTimdomFor g (TSCD.cost1F g) itimdommultiple entries

                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdommultiple ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (_, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdommultiple
                    cycleNodes = (∐) cycles
                in restrict valid entries == validEntries,
    testProperty "validTimdomFor == validTimdomLfp "
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    itimmultiple = TSCD.itimdomMultipleOfTwoFinger g
                    valid    = TSCD.validTimdomFor g (TSCD.cost1F g) itimmultiple (Set.fromList $ nodes g)
                    validlfp = TSCD.validTimdomLfp g 
                in valid == validlfp,
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp via validTimdom one step"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g
                    valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdom (Set.fromList $ nodes g)
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                     let fuel = valid ! x in
                           (∀) ys (\(y, steps) ->
                             -- (if (fuel > 1) then traceShow (steps + steps', fuel, steps + steps'  <= fuel) else id) $
                             ((y, steps) ∈ timdom ! x)    ↔  (steps <= fuel )
                           )
                       ∧ (∀) [0..fuel-1] (\fuel' ->
                           not $
                           (∀) ys (\(y, steps) -> 
                             ((y, steps) ∈ timdom ! x)    ↔  (steps <= fuel')
                           )
                         )
                   ),
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp one step"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                         (∃) [0..n] (\fuel ->
                           (∀) ys (\(y, steps) -> 
                             ((y, steps)  ∈ timdom ! x)    ↔  (steps <= fuel)
                           )
                         )
                   ),
    testProperty   "ntscdNTSODSlice ⊆ tscdSlice for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                          | n == 0 = Set.empty
                          | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd   g
                        tscdslicer        = TSCD.tscdSliceFast g
                        subseteq = ntscdntsodslicer ms ⊆ tscdslicer ms
                    in  (if subseteq then id  else traceShow (ms, g)) subseteq,
    testPropertySized 40 "tscdSlice  == tscdSliceFast for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                          | n == 0 = Set.empty
                          | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        tscdslicer        = TSCD.tscdSlice     g
                        tscdslicerfast    = TSCD.tscdSliceFast g
                        same = tscdslicer ms == tscdslicerfast ms
                    in  (if same then id  else traceShow (ms, g)) same,
    testPropertySized 40 "tscdSlice  == tscdSliceViaTimDF for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        n    = length $ nodes g
                        tscdslicer        = TSCD.tscdSlice         g
                        tscdslicertimdf   = TSCD.tscdSliceViaTimDF g
                        seeds = zip (moreSeeds seed1 30) (moreSeeds seed2 30)
                    in (∀) seeds (\(seed1, seed2) ->
                         let ms
                               | n == 0 = Set.empty
                               | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                             same = tscdslicer ms == tscdslicertimdf ms
                         in  (if same then id  else traceShow (ms, g)) same
                       ),
    testProperty   "timDFFromFromItimdomMultipleOfFast == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromFromItimdomMultipleOfFast  g ==
                       TSCD.timDF                               g,
    testProperty   "timDFFromFromItimdomMultipleOf   == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromFromItimdomMultipleOf  g ==
                       TSCD.timDF                           g,
    testProperty   "timdomsFromItimdomMultipleOf     == timdomsOf"
                $ \(ARBITRARY(g)) ->
                       TSCD.timdomsFromItimdomMultipleOf  g ==
                       TSCD.timdomsOf                     g,
    testProperty   "timDFLocalViaTimdoms    == timDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFLocalViaTimdoms  g ==
                       TSCD.timDFLocalDef         g,
    testProperty   "timDFUpGivenXViaTimdoms == timDFUpGivenXViaTimdomsDef"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFUpGivenXViaTimdoms    g ==
                       TSCD.timDFUpGivenXViaTimdomsDef g,
    testProperty   "timDFFromUpLocalDefViaTimdoms == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromUpLocalDefViaTimdoms g ==
                       TSCD.timDF                          g,
    testProperty   "timDFCostFromUpLocalDefViaTimdoms == timDFCost"
                $ \(ARBITRARY(g)) seed -> 
                       let cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in TSCD.timDFCostFromUpLocalDefViaTimdoms g costF ==
                          TSCD.timDFCost                         g costF,
    testPropertySized 40   "tscdOfLfp  == timDF"
                $ \(ARBITRARY(g)) ->
                       (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfLfp g) ==
                       (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDF    g)),
    testPropertySized 40   "tscdOfNaiveCostLfp  == timDFFromFromItimdomMultipleOfFastCost"
                $ \(ARBITRARY(g)) seed ->
                       let cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfNaiveCostfLfp g costF) ==
                          (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDFFromFromItimdomMultipleOfFastCost g costF)),
    testProperty   "tscdOfNaiveCostLfp  == timDFFromFromItimdomMultipleOfFastCost for fixed examples"
                $ \seed -> (∀) interestingTimingDep (\(exampleName, example) ->
                       let g = example :: Gr () ()
                           cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfNaiveCostfLfp g costF) ==
                          (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDFFromFromItimdomMultipleOfFastCost g costF))),
    testPropertySized 40   "tscdOfNaiveCostLfp  == timDFCost"
                $ \(ARBITRARY(g)) seed ->
                       let cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfNaiveCostfLfp g costF) ==
                          (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDFCost g costF)),
    testPropertySized 40 "stepsCL timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    in PDF.stepsCL g timdom,
    testPropertySized 40 "noJoins timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    in PDF.noJoins g timdom,
    testProperty "timdomOfLfp is unique"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom  = TSCD.timdomOfLfp      g
                in (∀) (Map.assocs timdom) (\(n, ms) -> (∀) ms (\(m, steps) -> (∀) ms (\(m', steps') ->  (m == m')  →  (steps == steps')))),
    testProperty "timdomOfLfp == timdomOfNaiveLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom  = TSCD.timdomOfLfp      g
                    timdom' = TSCD.timdomOfNaiveLfp g
                in timdom == timdom',
    testProperty "itimdomMultipleTwoFingercd == tscdOfLfp in graphs without non-trivial sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = TRANS.sinkShrinkedGraphNoNewExitForSinks generatedGraph (controlSinks generatedGraph)
                in TSCD.itimdomMultipleTwoFingercd g == Map.mapWithKey Set.delete (TSCD.tscdOfLfp g),
    testProperty "timdomOfLfp is transitive up to cycles for reducible cfg"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = TSCD.timdomOfLfp g
                in (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                                                                      (z, (steps + steps'          )          ) ∈ timdom ! x
                     ∨ (∃) (timdom ! z) (\(y',steps'') -> y' == y  ∧  (z, (steps          - steps'')          ) ∈ timdom ! x)
                ))),
    testProperty "timdomOfLfp is transitive up to cycles"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom = TSCD.timdomOfLfp g
                in (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                                                                      (z, (steps + steps'          )          ) ∈ timdom ! x
                     ∨ (∃) (timdom ! z) (\(y',steps'') -> y' == y  ∧  (z, (steps          - steps'')          ) ∈ timdom ! x)
                     ∨ (∃) (timdom ! z) (\(y',steps'') -> y' == y) ∧  (not $ ((∃) (timdom ! z) (\(x', _) -> x' == x)))
                ))),
    testProperty "timdomMultipleOfNaiveLfp == itimdomMultipleOfTwoFinger^*"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    nr = toInteger $ 2 * (length $ nodes g)
                    itimdomMultiple = TSCD.itimdomMultipleOfTwoFinger g
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdomMultipleFinger = Map.fromList [ (n, Set.fromList [ (m, steps) | m <- nodes g, path <- pathsUpToLength itimdomMultiple nr n m, let steps = sum $ fmap snd path ]) | n <- nodes g]
                in timdomMultipleNaive == timdomMultipleFinger,
    testProperty "timdomOfLfp == timdomOfTwoFinger"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom  = TSCD.timdomOfLfp g
                    timdom' = TSCD.timdomOfTwoFinger g
                in timdom == timdom',
    testProperty "timdomOfLfp is transitive in graphs without non-trivial sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = TRANS.sinkShrinkedGraphNoNewExitForSinks generatedGraph (controlSinks generatedGraph)
                    timdom = TSCD.timdomOfLfp g
                in (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                       (z, steps+steps') ∈ timdom ! x
                ))),
    testProperty "timdomOfLfp is transitive in graphs without imdom cycles"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    imdom = PDOM.imdomOfTwoFinger6 g
                    cycles = snd $ findCyclesM $ fmap fromSet $ imdom
                    timdom = TSCD.timdomOfLfp g
                in  List.null cycles ==>
                    (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                       (z, steps+steps') ∈ timdom ! x
                ))),
    testProperty "ntscdTimingSlice == ntscdTimingSlice == tscdSlice == tscdSliceFast "
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    ntscdtimingslicer  = PTDEP.ntscdTimingSlice g
                    nticdtimingslicer  = PTDEP.nticdTimingSlice g
                    tscdslicer         = TSCD.tscdSlice        g
                    tscdslicerfast     = TSCD.tscdSliceFast    g
                in (∀) (nodes g) (\m ->
                     let ms = Set.fromList [m]
                         s1 = nticdtimingslicer ms
                         s2 = ntscdtimingslicer ms
                         s3 = tscdslicer        ms
                         s4 = tscdslicerfast    ms
                     in s1 == s2  ∧  s2 == s3  ∧  s3 == s4
                   ),
    testPropertySized 35 "tscdSlice is minimal wrt. timed traces and termination"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        ms = Set.fromList $ sampleFrom seed (max 1 $ abs $ seed2 `mod` (max 1 $ n `div` 2)) (nodes g)
                        s = TSCD.tscdSlice g ms
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (∀) s (\n -> n ∈ ms ∨
                         let s' = Set.delete n s
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentTimed g s input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in different
                                  )
                               ))
                         in (if differentobservation then id else traceShow (ms, n, differentobservation)) $
                            differentobservation
                       ),
    testPropertySized 25 "tscdSlice  is sound wrt. timed traces and termination"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = withoutSelfEdges $ removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        ms = Set.fromList $ sampleFrom seed (max 1 $ abs $ seed2 `mod` (max 1 $ n `div` 2)) (nodes g)
                        s = TSCD.tscdSlice g ms
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentTimed g s input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in (if not $ different then id else traceShow (ms, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in -- traceShow (length $ nodes g, Set.size s, Set.size ms, Set.size condNodes, Set.size $ (condNodes ∩ (Set.fromList $ rdfs (Set.toList ms) g)) ∖ s) $
                       (if not $ differentobservation then id else traceShow (ms, differentobservation)) $
                       not differentobservation,
    testPropertySized 20 "timingSolvedF3dependence  is sound wrt. timed traces"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        ms = Set.fromList [m1,m2]
                        s = ms ⊔ Set.fromList [n | (n, ms') <- Map.assocs $ PTDEP.timingSolvedF3dependence g, (∃) ms (\m -> m ∈ ms')]
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowTimingEquivalent g s input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in (if not $ different then id else traceShow (m1,m2, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (if not $ differentobservation then id else traceShow (m1, m2, differentobservation)) $
                       not differentobservation,
    testPropertySized 30  "the  solved timingF3EquationSystem is correct"
                $ \(ARBITRARY(g)) ->
                       let timingEqSolved    = PTDEP.solveTimingEquationSystem $ PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem
                           trcG = trc g
                           pathsBetween     = PBETWEEN.pathsBetween        g trcG
                           pathsBetweenUpTo = PBETWEEN.pathsBetweenUpTo    g trcG
                       in  -- traceShow g $
                           (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in (m /= p) →
                                  let paths = pathsBetween p m in
                                  -- traceShow (m,p, rmq) $
                                  case rmq of
                                     PTDEP.FixedStepsPlusOther s y ->
                                                                      let paths = pathsBetweenUpTo p m y in
                                                                      (∀) paths (\(hasLoop,  path ) -> y `elem` path ∧ (toInteger (length $ takeWhile (/= y) path)) == s + 1)
                                     PTDEP.FixedSteps s            -> (∀) paths (\(hasLoop,  path ) -> (not hasLoop) ∧ (toInteger (length                    path)) == s + 2)
                                     PTDEP.UndeterminedSteps       -> (∃) paths (\(hasLoop,  path ) -> hasLoop)
                                                                    ∨ (∃) paths (\(hasLoop1, path1) -> (not hasLoop1) ∧
                                                                          (∃) paths (\(hasLoop2, path2) -> (not hasLoop2) ∧ length (path1) /= (length path2))
                                                                      )
                                     PTDEP.Unreachable             -> paths == []
                           ),
    testProperty  "prevCondsWithSuccNode  ==  prevCondsWithSuccNode'"
                $ \(ARBITRARY(g)) -> (∀) (nodes g) (\n -> 
                       (List.sort $ prevCondsWithSuccNode  g n) ==
                       (List.sort $ prevCondsWithSuccNode' g n)
                  ),
    testProperty  "timingSnSolvedDependence         == enumerateTimingDependence"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSnSolvedDependence  g ==
                       PTDEP.enumerateTimingDependence g,
    testProperty  "timingSnSolvedDependence         == timingSnSolvedDependenceWorklist"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSnSolvedDependence          g ==
                       PTDEP.timingSnSolvedDependenceWorklist  g,
    testProperty  "timingSnSolvedDependence         == timingSnSolvedDependenceWorklist2"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSnSolvedDependence          g ==
                       PTDEP.timingSnSolvedDependenceWorklist2 g,
    testProperty  "timingSolvedF3dependence == timingSnSolvedDependenceWorklist"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSolvedF3dependence g ==
                       PTDEP.timingSnSolvedDependenceWorklist g,
    testProperty  "timingSolvedF3dependence == timingSnSolvedDependence"
                $ \(ARBITRARY(g)) -> 
                       PTDEP.timingSolvedF3dependence g ==
                       PTDEP.timingSnSolvedDependence g,
    testProperty  "timmaydomOfLfp            relates to solved timingF3EquationSystem"
                $ \(ARBITRARY(g)) ->
                       let timingEqSolved    = PTDEP.solveTimingEquationSystem $ PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem
                           timmaydomOfLfp    = PTDEP.timmaydomOfLfp g
                       in  (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in (m /= p) →
                                  case rmq of
                                     PTDEP.FixedSteps s            -> Set.fromList [1+s] == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                                     PTDEP.FixedStepsPlusOther s y -> Set.fromList [1+s] == Set.fromList [ steps | (y', steps) <- Set.toList $ timmaydomOfLfp ! p, y == y']
                                     PTDEP.UndeterminedSteps       -> Set.fromList []    == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                                     PTDEP.Unreachable             -> smp == Map.empty ∧
                                                                      Set.fromList []    == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                           ),
    testProperty  "itimdomMultipleOfTwoFinger^* {no loop}  == timdomOfLfp for graphs without itimdomMultiple cycles"
                $ \(ARBITRARY(g)) ->
                       let itimdomMultiple   = TSCD.itimdomMultipleOfTwoFinger g
                           timdomOfLfp       = TSCD.timdomOfLfp g
                           mustReachFromIn   = reachableFromIn $ fmap (Set.map (\(x,steps) -> (x,(steps, Set.empty)))) $ itimdomMultiple

                           imdom = PDOM.imdomOfTwoFinger6 g
                           cycles = snd $ findCyclesM $ fmap (fromSet . Set.map fst ) $ itimdomMultiple
                       in  List.null cycles ==>
                           (∀) (Map.assocs timdomOfLfp) (\(n, ms) ->
                              (∀) (ms) (\(m,steps) -> Set.fromList [steps] == mustReachFromIn n m)
                           )
                         ∧ (∀) (nodes g) (\n -> (∀) (nodes g) (\m ->
                              mustReachFromIn n m == Set.fromList [ steps | (m', steps) <- Set.toList $ timdomOfLfp ! n, m == m']
                           ))
                         ∧ (timdomOfLfp  ==  Map.fromList [ (n, Set.fromList [ (m, steps) | m <- nodes g, path <- minimalPath itimdomMultiple n m, let steps = sum $ fmap snd path ]) | n <- nodes g]),
    testProperty  "timingF3EquationSystem'  == timingF3EquationSystem"
                $ \(ARBITRARY(g)) ->
                       let timingEq        = PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem
                           timingEq'       = PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem'
                       in  timingEq         == timingEq',
    testProperty  "timingF3dependence is transitive"
                $ \(ARBITRARY(g)) ->
                       let tdep    = PTDEP.timingF3dependence g
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
                       let tdep    = PTDEP.timingSolvedF3dependence g
                       in (∀) (nodes g) (\n ->
                            (∀) (tdep ! n) (\n' ->
                              (∀) (tdep ! n') (\n'' ->
                                  (n'' == n)
                                ∨ (n'' ∈ tdep ! n)
                              )
                            )
                          ),
    testProperty  "timingDependenceViaTwoFinger        == timingSolvedF3dependence ∪ {(n,n) | n ∈ nodes}"
                $ \(ARBITRARY(g)) ->
                       let tdep             = PTDEP.timingSolvedF3dependence g
                           tdepviatwofinger = PTDEP.timingDependenceViaTwoFinger g
                       in  tdepviatwofinger == tdep ⊔ Map.fromList [(n, Set.fromList [n]) | n <- nodes g ],
    testProperty  "alternativeTimingSolvedF3dependence == timingSolvedF3dependence"
                $ \(ARBITRARY(g)) ->
                       let tdep            = PTDEP.timingSolvedF3dependence g
                           alternativetdep = PTDEP.alternativeTimingSolvedF3dependence g
                       in  alternativetdep == tdep,
    testProperty  "timingSolvedF3sparseDependence^*    == timingSolvedF3dependence ∪ {(n,n) | n ∈ nodes}"
                $ \(ARBITRARY(g)) ->
                       let tdep             = PTDEP.timingSolvedF3dependence g
                           tdepsparse       = PTDEP.timingSolvedF3sparseDependence g
                       in (trc $ fromSuccMap $ tdepsparse :: Gr () ()) ==
                          (      fromSuccMap $ tdep ⊔ Map.fromList [(n, Set.fromList [n]) | n <- nodes g ]),
    testProperty  "timingSolvedF3dependence ⊑ timingF3dependence"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSolvedF3dependence g ⊑
                       PTDEP.timingF3dependence       g,
    testProperty  "timingF3dependence       ⊑ timingDependence"
                $ \(ARBITRARY(g)) ->
                       let gCfg = emap (\() -> NoOp) g in
                       PTDEP.timingF3dependence       g ⊑
                             timingDependence         gCfg
  ]

timingDepTests = testGroup "(concerning timingDependence)" $
  [  testCase    ("timingCorrection itimdomMultiple for " ++ exampleName)
            $   let (cost, itimdomMultiple') = TSCD.timingCorrection g (TSCD.cost1 g)
                    itimdomMultiple'' = TSCD.itimdomMultipleOfTwoFingerCost g (\n m -> cost ! (n,m))
                    noselfloops = Map.mapWithKey (\n ms -> Set.filter (\(m, k) -> m /= n) ms)
                in noselfloops itimdomMultiple'' == noselfloops itimdomMultiple' @? ""
  | (exampleName, g) <- interestingTimingDep ++ interestingIsinkdomTwoFinger
  ] ++
  [  testCase    ("timingCorrection imdom for " ++ exampleName)
            $   let (cost, itimdomMultiple') = TSCD.timingCorrection g (TSCD.cost1 g)
                    itimdomMutliple'NoK = fmap (Set.map fst) itimdomMultiple'
                    imdom = PDOM.imdomOfTwoFinger6 g
                in (trc $ fromSuccMap $ itimdomMutliple'NoK :: Gr () ()) == (trc $ fromSuccMap $ imdom :: Gr () ()) @? ""
  | (exampleName, g) <- interestingTimingDep ++ interestingIsinkdomTwoFinger
  ] ++
  []




cdomCdomProps = testGroup "(concerning cdoms)" $
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
    testPropertySized 40  "idomIsTreeProgram idomChef"                   $ idomIsTreeProgram idomChef,
    testPropertySized 20  "idomIsTreeProgram idomBischof"                $ idomIsTreeProgram idomBischof,
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


balancedParanthesesProps = testGroup "(concerning sccs, as well as general chops and balanced-parantheses-chops)" [
    testProperty  "alternative implementation of  pre*[at(m2) ∩ pre*[at(m3)]] " $
      \(INTERCFG(cfg)) seed seed' ->
                     let  at = inNode cfg
                          k         = 100
                          language  = Set.fromList [ n | (_,n) <- labNodes cfg ]
                          ms        = sampleFrom seed 5 (nodes cfg)
                     in -- traceShow (length $ nodes cfg) $
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
                     in -- traceShow (length $ nodes cfg) $
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
                     in -- traceShow (length $ nodes g, length $ nodes folded) $
                        (∀) (nodes folded) (\n -> (Map.size $ contextGraphFrom folded n) >= 0),
    testProperty  "sccIsSccNaive"                     $ sccIsSccNaive,
    testProperty  "sccIsSameLevelScc"                 $ sccIsSameLevelScc,
    testProperty  "simulUnbrIsUnbr"                   $ simulUnbrIsUnbr,
    testProperty  "simulUnblIsUnbl"                   $ simulUnblIsUnbl,
    testProperty  "simulUnbr'IsUnbr"                  $ simulUnbrIsUnbr,
    testProperty  "simulUnbl'IsUnbl"                  $ simulUnblIsUnbl,
    testProperty  "balancedChopIsSimulBalancedChop"   $ balancedChopIsSimulBalancedChop,
    testProperty  "chopsInterIDomAreChops"            $ chopsInterIDomAreChops,
    testProperty  "sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs" $ sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs,
    testProperty  "sameLevelSummaryGraphIssameLevelSummaryGraph'" $ sameLevelSummaryGraphIssameLevelSummaryGraph'
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

indepsProps = testGroup "(concerning dependencey graph representations using independencies)" [
    testPropertySized 25 "addNonImplicitNonTrivialSummaryEdgesGfpLfp  =~   addNonImplicitNonTrivialSummaryEdges"
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
    testPropertySized 50 "nonImplicitSummaryComputation is correct"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        pdg = programDependenceGraphP p
                        (cfg, parameterMaps) = withParameterNodes p
                        sdg                     = addSummaryEdges              parameterMaps pdg
                        (nonImplicitNonTrivialSummariesSdg, summaryIndependencies, formalInActualInInIndependencies, actualOutFormalOutIndependencies)  = addNonImplicitNonTrivialSummaryEdges p parameterMaps pdg
                        sdg'                    = addImplicitAndTrivialSummaryEdgesLfp p parameterMaps summaryIndependencies formalInActualInInIndependencies actualOutFormalOutIndependencies nonImplicitNonTrivialSummariesSdg
                        summaries                       = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges sdg                              ]
                        summariesNonImplicitNonTrivial  = Set.fromList $[ e | e@(_,_,SummaryDependence) <- labEdges nonImplicitNonTrivialSummariesSdg]
                    in -- traceShow ("SummaryGraph: ", Set.size summaries, "\t\t", "NonImplicitSummaryGraph: ", Set.size summariesNonImplicitNonTrivial) $
                       sdg == sdg',
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
    testPropertySized 50 "summaryIndepsProperty"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                    in summaryIndepsPropertyViolations p == [],
    testPropertySized 50 "summaryComputation                      =~  summaryComputationGfpLfpWorkList"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        (cfg, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                        sdg               = addSummaryEdges                 parameterMaps pdg
                        sdgGfpLfpWorkList = addSummaryEdgesGfpLfpWorkList p parameterMaps pdg
                    in -- traceShow (length $ nodes $ tcfg p, length $ nodes cfg, length $ [ () | (_,_,SummaryDependence) <- labEdges sdg]) $
                                                      sdg == sdgGfpLfpWorkList,
    testPropertySized 50 "summaryComputation                      =~  summaryComputationGfpLfp"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        (_, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                    in addSummaryEdges parameterMaps pdg  == addSummaryEdgesGfpLfp p parameterMaps pdg,
    testPropertySized 50 "summaryComputation                      =~  summaryComputationLfp"
                $ \generated ->
                    let p   :: Program Gr = toProgram generated
                        (_, parameterMaps) = withParameterNodes p
                        pdg = programDependenceGraphP p
                    in addSummaryEdges parameterMaps pdg  == addSummaryEdgesLfp parameterMaps pdg,
    testPropertySized 50 "dataDependenceGraphViaIndependenceP     == dataDependenceGraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  dataDependenceGraphViaIndependenceP p   == dataDependenceGraphP p
  ]
indepsTests = testGroup "(concerning dependencey graph representations using independencies)" $
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




delayProps = testGroup "(concerning inifinte delay)" [
    testPropertySized 25 "ntscdNTSODFastPDomSlice  is sound"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        slicer     = SLICE.ODEP.ntscdNTSODFastPDomSlice g
                        ss         = Set.fromList [ slicer (Set.fromList [m1, m2]) | m1 <- nodes g, m2 <- nodes g ]
                        runInput   = InfiniteDelay.runInput         g
                    in (∀) ss (\s ->
                         let observable   = InfiniteDelay.observable s
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                     in (if not $ different then id else traceShow (s, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                         in not differentobservation
                    ),
    testPropertySized 25 "ntscdNTSODFastPDomSlice  is minimal"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        s = SLICE.ODEP.ntscdNTSODFastPDomSlice g (Set.fromList [m1, m2])
                        runInput         = InfiniteDelay.runInput g
                    in -- traceShow (length $ nodes g, Set.size s, Set.size $ condNodes) $
                       (∀) s (\n -> n == m1  ∨  n == m2  ∨
                         let s' = Set.delete n s
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                    in different
                                  )
                               ))
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            (if differentobservation then id else traceShow (m1, m2, n, differentobservation)) $
                            differentobservation
                       ),
    testPropertySized 25 "infinitelyDelays trace contains trace"
                $ \(ARBITRARY(generatedGraph)) seed seed' ->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        runInput = InfiniteDelay.runInput g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [nSamples] = fmap toInteger $ sampleFrom seed  1        [0.. 4 * (length $ nodes g)]
                        s          =   Set.fromList $ sampleFrom seed' nSamples (nodes g)
                        infinitelyDelays = InfiniteDelay.infinitelyDelays g s
                    in (∀) choices  (\choice ->  (∀) (nodes g) (\startNode -> 
                         let input = InfiniteDelay.Input startNode choice
                             trace    = runInput input
                             traceObs = InfiniteDelay.observable s trace
                             continuations = infinitelyDelays input
                         in    traceObs ∈ continuations
                            ∧ (∀) continuations ( \continuation -> traceObs `InfiniteDelay.isTracePrefixOf` continuation)
                       )),
    testPropertySized 25 "nticdNTIODFastSlice  is minimal"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        s = SLICE.ODEP.nticdNTIODFastSlice g (Set.fromList [m1, m2])
                        runInput         = InfiniteDelay.runInput g
                    in -- traceShow (length $ nodes g, Set.size s, Set.size $ condNodes) $
                       (∀) s (\n -> n == m1  ∨  n == m2  ∨
                         let s' = Set.delete n s
                             infinitelyDelays = InfiniteDelay.infinitelyDelays g s'
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentFor infinitelyDelays runInput observable input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                    in different
                                  )
                               ))
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            (if differentobservation then id else traceShow (m1, m2, n, differentobservation)) $
                            differentobservation
                       ),
    testPropertySized 25 "inifiniteDelays  is unique w.r.t nticdNTIODFastSlice"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                    let g = generatedGraph
                        n = toInteger $ length $ nodes g
                        startNodes =               sampleFrom       seed1 (n `div` 10 + 1) (nodes g)
                        choices    = InfiniteDelay.sampleChoicesFor seed2 (n `div`  2 + 1)        g
                        [m1,m2]    =               sampleFrom       seed3                2 (nodes g)
                        s = SLICE.ODEP.nticdNTIODFastSlice g (Set.fromList [m1, m2])
                        infinitelyDelays = InfiniteDelay.infinitelyDelays g s
                    in -- traceShow ("Graph: ", length $ nodes g) $
                       (∀) choices (\choice -> (∀) startNodes (\startNode  -> 
                         let input = InfiniteDelay.Input startNode choice
                             continuations = infinitelyDelays input
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            let result = InfiniteDelay.isAscending continuations
                            in (if result then id else traceShow (m1, m2, input, g, result)) $ result
                       ))
  ]
delayTests = testGroup "(concerning  inifinite delay)" $
  [  testCase    ( "ntscdNTSODFastPDomSlice  is minimal for " ++ exampleName) $
               let n = toInteger $ length $ nodes g
                   condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                   choices    = InfiniteDelay.allChoices g Map.empty condNodes
                   runInput   = InfiniteDelay.runInput         g
               in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                    let s = SLICE.ODEP.ntscdNTSODFastPDomSlice g (Set.fromList [m1, m2])
                    in -- traceShow (length $ nodes g, Set.size s, Set.size $ condNodes) $
                       (∀) s (\n -> n == m1  ∨  n == m2  ∨
                         let s' = Set.delete n s
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                    in different
                                  )
                               ))
                         in -- traceShow (length startNodes, length choices, length continuations, startNode) $
                            -- (if length continuations == 1 then id else traceShow (InfiniteDelay.observable s $ InfiniteDelay.runInput g input, continuations)) $
                            (if differentobservation then id else traceShow (m1, m2, n, differentobservation)) $
                            differentobservation
                       )
                  )) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntscdNTSODFastPDomSlice  is sound for " ++ exampleName) $ 
               let n = toInteger $ length $ nodes g
                   condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                   choices    = InfiniteDelay.allChoices g Map.empty condNodes
                   runInput   = InfiniteDelay.runInput         g
               in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                    let s = SLICE.ODEP.ntscdNTSODFastPDomSlice g (Set.fromList [m1, m2])
                        observable       = InfiniteDelay.observable         s
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                     in (if not $ different then id else traceShow (m1,m2, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (if not $ differentobservation then id else traceShow (m1, m2, differentobservation)) $
                       not differentobservation
                  )) @? ""
  | (exampleName, g) <- interestingDodWod, exampleName /= "wodDodInteresting4"
  ] ++
  []



cacheProps = testGroup "(concerning cache timing)" [
    testPropertySized 25 "csd is sound"
                $ \generated seed1 seed2 seed3 ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b
                          where (a,b) = toCodeSimple generated
                        g0 = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        vars = Set.fromList [ var | n <- nodes g0, var@(Global x) <- Set.toList $ use g0 n ∪ def g0 n]
                        (newN0:new) = (newNodes ((Set.size vars) + 1) g0)
                        varToNode = Map.fromList $ zip (Set.toList vars) new
                        nodeToVar = Map.fromList $ zip new (Set.toList vars)

                        prepend = prependInitialization g0 n0 newN0 varToNode

                        initialGlobalState1 = Map.fromList $ zip (Set.toList vars) (fmap (`rem` 32) $ moreSeeds seed1 (Set.size vars))
                        initialFullState   = ((Map.empty, Map.empty, ()), initialCacheState, 0)
                        g1 = prepend initialGlobalState1


                        (ccg1, cost) = cacheCostDecisionGraph g1 newN0
                        costF n m = cost ! (n,m)
                        artificialNodes = Set.fromList (nodes ccg1) ∖ Set.fromList (nodes g1)
                        
                        -- nticd' =            isinkDFTwoFinger g1
                        tscd'  =            TSCD.timDFFromFromItimdomMultipleOfFastCost ccg1 costF
                        dd'    = invert'' $ dataDependence         g1 vars newN0
                        -- csd'   = invert'' $ csd'Of                 g1      newN0
                        csd'   = invert'' $ csd''''Of3             g1      newN0


                        slicer ms = s ∖ artificialNodes
                          where s = combinedBackwardSlice g1 (tscd' ⊔ dd' ⊔ csd') (Map.empty) ms

                        limit = 9000
                        (execution1, limited1) = assert (length es == 1) $ (head es, (length $ head es) >= limit)
                          where es = cacheExecutionLimit limit g1 initialFullState newN0

                        ms = [ nodes g0 !! (m `mod` (length $ nodes g0)) | m <- moreSeeds seed2 100]
                    in traceShow ("|g1|", length $ nodes g1, "|ccg1|", length $ nodes ccg1, "|csd'", sum $ fmap Set.size $ Map.elems csd') $
                       -- traceShow ("g1: ", g1) $
                       (∀) ms (\m ->
                         let s = slicer (Set.fromList [m])
                             notInS = (Set.fromList $ Map.elems varToNode) ∖ s
                             newValues = fmap (`rem` 32) $ moreSeeds (seed3 + m) (Set.size notInS)
                             initialGlobalState2 = (Map.fromList $ zip (fmap (\n -> nodeToVar ! n) $ Set.toList notInS) newValues) `Map.union` initialGlobalState1
                             g2 = prepend initialGlobalState2
                             
                             (execution2, limited2) = assert (length es == 1) $ (head es, (length $ head es) >= limit)
                               where es = cacheExecutionLimit limit g2 initialFullState newN0

                             exec1Obs = filter (\(n,_) -> n ∈ s) $ execution1
                             exec2Obs = filter (\(n,_) -> n ∈ s) $ execution2

                             ok = -- traceShow ("|notInS|:", Set.size notInS, "Limited: ", limited1 ∨ limited2, "   |execution1|: ", length execution1, "   |execution2|: ", length execution2) $
                                  -- traceShow ("g2: ", g2) $
                                  limited1 ∨ limited2 ∨ (exec1Obs == exec2Obs)
                          in if ok then ok else
                               traceShow ("M:: ", m, "  S::", s) $
                               traceShow ("G1 =====", g1) $
                               traceShow ("G2 =====", g2) $
                               traceShow (execution1, "=========", execution2) $
                               traceShow (exec1Obs,   "=========", exec2Obs) $
                               traceShow (List.span (\(a,b) -> a == b) (zip exec1Obs exec2Obs)) $
                               ok
                        )
                    --      let observable   = InfiniteDelay.observable s
                    --          differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                    --            let input = InfiniteDelay.Input startNode choice
                    --                trace = runInput input
                    --                obs   = observable trace
                    --            in (∃) choices' (\choice' ->
                    --                 let input' = InfiniteDelay.Input startNode choice'
                    --                     trace' = runInput input'
                    --                     obs'   = observable trace'
                    --                     different = not $ obs == obs'
                    --                  in (if not $ different then id else traceShow (s, startNode, choice, choice', g)) $
                    --                     different
                    --               )
                    --            ))
                    --      in not differentobservation
                    -- ),
  ]
  
-- cacheTests = testGroup "(concerning  inifinite delay)" $
--   [  testCase    ( "ntscdNTSODFastPDomSlice  is sound for " ++ exampleName) $ 
--                let n = toInteger $ length $ nodes g
--                    condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
--                    choices    = InfiniteDelay.allChoices g Map.empty condNodes
--                    runInput   = InfiniteDelay.runInput         g
--                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
--                     let s = SLICE.ODEP.ntscdNTSODFastPDomSlice g (Set.fromList [m1, m2])
--                         observable       = InfiniteDelay.observable         s
--                         differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
--                                let input = InfiniteDelay.Input startNode choice
--                                    trace = runInput input
--                                    obs   = observable trace
--                                in (∃) choices' (\choice' ->
--                                     let input' = InfiniteDelay.Input startNode choice'
--                                         trace' = runInput input'
--                                         obs'   = observable trace'
--                                         different = not $ obs == obs'
--                                      in (if not $ different then id else traceShow (m1,m2, startNode, choice, choice', g)) $
--                                         different
--                                   )
--                                ))
--                     in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
--                        (if not $ differentobservation then id else traceShow (m1, m2, differentobservation)) $
--                        not differentobservation
--                   )) @? ""
--   | (exampleName, g) <- interestingDodWod, exampleName /= "wodDodInteresting4"
--   ] ++
--   []




miscProps = testGroup "(misc)" [
    testProperty  "trcOfTrrIsTrc"                     $ trcOfTrrIsTrc
  ]


testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

