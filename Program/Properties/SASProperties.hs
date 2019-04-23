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

module Program.Properties.SASProperties where

import Prelude hiding (all)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)
import Control.Exception.Base (assert)

import Algebra.Lattice
import Unicode

import Util(invert'', (≡), findCyclesM, fromSet, sublists, moreSeeds)
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
import Data.Tree (Tree(..), Forest)
import qualified Data.Tree as Tree

import Data.Ord (Down(..))
import Data.List (sortOn)
import Data.Map ( Map, (!) )
import Data.Maybe(fromJust)

import IRLSOD(CFGEdge(..))

import Data.Graph.Inductive.Arbitrary.Reducible
import Data.Graph.Inductive.Query.DFS (scc, dfs, rdfs, rdff, reachable, condensation)
import Data.Graph.Inductive.Query.Dominators (iDom)
import Data.Graph.Inductive.Query.TimingDependence (timingDependence)
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trr, fromSuccMap, toSuccMap, controlSinks, delSuccessorEdges)
import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph, delEdges, insEdge)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.ControlDependence (controlDependenceGraphP, controlDependence)
import Data.Graph.Inductive.Query.DataDependence (dataDependenceGraphP, dataDependenceGraphViaIndependenceP, withParameterNodes)
import Data.Graph.Inductive.Query.ProgramDependence (programDependenceGraphP, addSummaryEdges, addSummaryEdgesLfp, addSummaryEdgesGfpLfp, addSummaryEdgesGfpLfpWorkList, summaryIndepsPropertyViolations, implicitSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdges, addImplicitAndTrivialSummaryEdgesLfp, addNonImplicitNonTrivialSummaryEdgesGfpLfp)

import qualified Data.Graph.Inductive.Query.MyWodSlice as MyWodSlice
import qualified Data.Graph.Inductive.Query.LCA as LCA (lca)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (isinkdomOf, isinkdomOfGfp2, joinUpperBound, sinkdomOfJoinUpperBound, sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkdomNaiveGfp, sinkdomNaiveGfpFullTop, sinkdomOfisinkdomProperty, imdomOf, imdomOfLfp, mdomOf, mdomOfLfp, mdomNaiveLfp, mdomOfimdomProperty, onedomOf, mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, isinkdomOftwoFinger8Up,  imdomOfTwoFinger6, imdomOfTwoFinger7)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (
    isinkDFTwoFinger, mDFTwoFinger,  noJoins, stepsCL,
    sinkDFF2cd, sinkDFF2GraphP, sinkDFcd, sinkDFGraphP, sinkDFFromUpLocalDefcd, sinkDFFromUpLocalDefGraphP, sinkDFFromUpLocalcd, sinkDFFromUpLocalGraphP, isinkdomTwoFingercd,
    sinkDFUp, sinkDFUpDef, sinkDFUpDefViaSinkdoms,
    sinkDFLocal, sinkDFLocalDef, sinkDFLocalViaSinkdoms, sinkDFUpGivenX, sinkDFUpGivenXViaSinkdoms,
    sinkDFFromUpLocalDefViaSinkdoms, sinkDF,
    idomToDF, idomToDFFast,
    mDFF2cd,    mDFF2GraphP,    mDFcd,    mDFGraphP,   mDFFromUpLocalDefcd,     mDFFromUpLocalDefGraphP,    mDFFromUpLocalcd,    mDFFromUpLocalGraphP,     imdomTwoFingercd,
    mDFUp, mDFUpDef, mDFUpDefViaMdoms, mDFUpGivenXViaMdoms,
    mDFLocal, mDFLocalDef, mDFLocalViaMdoms, mDFUpGivenX, 
    mDFFromUpLocalDefViaMdoms, mDF,
 )
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges as CEDGE (nticdSliceNumberedViaCEdgesFast, ntscdSliceViaCEdgesFast, dfViaCEdges, idfViaCEdgesFast, nticdSliceViaCEdgesFast, nticdSliceViaCEdgesFastFor)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers.Numbered as PDFNumbered (nticdSliceNumbered)
import qualified Data.Graph.Inductive.Query.FCACD as FCACD (wccSlice, wdSlice, nticdMyWodViaWDSlice, wodTEILSliceViaBraunF2)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (delayedInfinitely, sampleLoopPathsFor, isTracePrefixOf, sampleChoicesFor, Input(..), infinitelyDelays, runInput, observable, allChoices, isAscending, isLowEquivalentFor, isLowTimingEquivalent, isLowEquivalentTimed)
import qualified Data.Graph.Inductive.Query.PostDominance.Numbered as PDOMNumbered (iPDom, pdom, numberForest)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    wodTEILSliceViaISinkDom,
    wccSliceViaISinkDom,
    nticd, ntscd,
    sinkShrinkedGraphNoNewExitForSinks,
    ntindDef, ntsndDef,
    nticdMyWodSliceViaCutAtRepresentatives, nticdMyWodSliceViaEscapeNodes, nticdMyWodSliceViaCutAtRepresentativesNoTrivial, nticdMyWodSliceViaChoiceAtRepresentatives,
    nticdMyWodSliceViaNticd,
    nticdMyWodSliceViaISinkDom,
    joiniSinkDomAround,
    pathsBetweenBFS, pathsBetweenUpToBFS,
    pathsBetween,    pathsBetweenUpTo,
    possibleIntermediateNodesFromiXdom, withPossibleIntermediateNodesFromiXdom,
    nticdSlice,  ntscdSlice, nticdSliceFor, 
    mayNaiveGfp,
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    isinkdomOfSinkContraction,
    nticdSinkContraction, nticdSinkContractionGraphP,
    nticdF3GraphP, nticdF3'GraphP, nticdF3'dualGraphP, nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, nticdF3WorkListGraphP, nticdDef, nticdDefGraphP, nticdF3WorkListSymbolicGraphP, nticdF3'dualWorkListSymbolicGraphP, nticdFig5GraphP, nticdF5GraphP, nticdF3'dualWorkList, snmF3'dual, nticdF3'dualWorkListGraphP,
    ntscdF4GraphP, ntscdF3GraphP, ntscdF4WorkListGraphP,                                                                        ntscdF4, ntscdF3, ntscdF4WorkList,                      ntscdDef, ntscdDefGraphP
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
    ntscdMyDodSliceViaNtscd, mustOfLfp, mustOfGfp, mmayOf, mmayOf', rotatePDomAround, Color(..), smmnFMustDod, smmnFMustWod, colorLfpFor, colorFor,
    nticdMyWodFastSlice, wodTEILPDomSlice, wodTEILSliceViaNticd,
    myWodFastPDomSimpleHeuristicSlice, myWodFastSlice, nticdMyWodSlice, wodTEILSlice, ntscdDodSlice, ntscdMyDodSlice, ntscdMyDodFastPDomSlice, 
    wccSliceViaNticd, wccSliceViaNticdMyWodPDomSimpleHeuristic, nticdMyWodPDomSimpleHeuristic,
    smmnGfp, smmnLfp, fMust, fMustBefore, fMustNoReachCheck,
    dod, dodDef, dodFast, dodColoredDagFixed, dodColoredDagFixedFast,
    myWod, myWodFast, myWodFastPDom, myWodFastPDomSimpleHeuristic,  myDod, myDodFast, myDodFastPDom, wodTEIL', wodTEIL'PDom, wodDef, wodFast, fMay, fMay'
  )
import qualified Data.Graph.Inductive.Query.NTICDUnused  as NTICDUnused (ntacdDef, ntacdDefGraphP, wodMyEntryWodMyCDSlice, myCD, myCDFromMyDom, myDom, allDomNaiveGfp, myWodFromMay)
import qualified Data.Graph.Inductive.Query.TSCD         as TSCD (timdomsOf, timingCorrection, timingLeaksTransformation, tscdCostSlice, timDFCostFromUpLocalDefViaTimdoms, timDFCost, tscdOfLfp, timDF, timDFFromUpLocalDefViaTimdoms, timDFUpGivenXViaTimdomsDef, timDFUpGivenXViaTimdoms, timDFLocalDef, timDFLocalViaTimdoms, tscdOfNaiveCostfLfp, timdomOfLfp, tscdSlice, timdomsFromItimdomMultipleOf, validTimdomFor, validTimdomLfp,
    itimdomMultipleOfTwoFingerCost, cost1, cost1F,
    itimdomMultipleTwoFingercd, timDFFromFromItimdomMultipleOf,
    timdomOfNaiveLfp, timdomMultipleOfNaiveLfp,
    timDFFromFromItimdomMultipleOfFast, timDFFromFromItimdomMultipleOfFastCost, itimdomMultipleOfTwoFinger, timdomOfTwoFinger, tscdSliceFast, tscdSliceViaTimDF)
import qualified Data.Graph.Inductive.Query.PureTimingDependence as PTDEP (alternativeTimingSolvedF3dependence, timingSolvedF3dependence, timingF3dependence, timingF3EquationSystem', timingF3EquationSystem, snmTimingEquationSystem, timingSolvedF3sparseDependence, timingSnSolvedDependence, timingSnSolvedDependenceWorklist, timingSnSolvedDependenceWorklist2, enumerateTimingDependence, solveTimingEquationSystem, Reachability(..), timmaydomOfLfp, timingDependenceViaTwoFinger, nticdTimingSlice, ntscdTimingSlice)

import qualified Data.Graph.Inductive.FA as FA


import Data.Graph.Inductive.Arbitrary


import Program (Program, tcfg)
import Program.Tests (isSecureEmpirically)

import Program.Properties.Analysis
import Program.Properties.CDom
import Data.Graph.Inductive.Query.BalancedSCC -- TODO: refactor that module into 2 seperate modules

import Execution (allFinishedExecutionTraces, someFinishedAnnotatedExecutionTraces)
import Program.Examples (testsuite, interproceduralTestSuit, precisionCounterExamples, interestingDodWod, interestingTimingDep, syntacticCodeExamples, code2ResumptionForProgram, code2Program, interestingIsinkdomTwoFinger, interestingImdomTwoFinger)
import Program.Defaults (defaultInput)
import Program.Analysis
import Program.Typing.FlexibleSchedulerIndependentChannels (isSecureFlexibleSchedulerIndependentChannel)
import Program.Typing.ResumptionBasedSecurity (Criterion(..), isSecureResumptionBasedSecurity, isSecureResumptionBasedSecurityFor)
import Program.CDom
import Program.Generator (toProgram, toProgramIntra, GeneratedProgram, SimpleCFG(..))


testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

main      = all

all        = defaultMain                               $ tests
allX       = defaultMainWithIngredients [antXMLRunner] $ tests
pdom       = defaultMain                               $ testGroup "pdom"      [ mkTest [pdomTests], mkProp [pdomProps]]
pdomX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "pdom"      [ mkTest [pdomTests], mkProp [pdomProps]]

pdf        = defaultMain                               $ testGroup "pdf"       [ mkTest [pdfTests], mkProp [pdfProps]]
pdfX       = defaultMainWithIngredients [antXMLRunner] $ testGroup "pdf"       [ mkTest [pdfTests], mkProp [pdfProps]]


ntsod      = defaultMain                               $ testGroup "ntsod"     [ mkTest [ntsodTests], mkProp [ntsodProps]]
ntsodX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "ntsod"     [ mkTest [ntsodTests], mkProp [ntsodProps]]

ntiod      = defaultMain                               $ testGroup "ntiod"     [ mkTest [ntiodTests], mkProp [ntiodProps]]
ntiodX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "ntiod"     [ mkTest [ntiodTests], mkProp [ntiodProps]]

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"


tests :: TestTree
tests = testGroup "Tests" [unitTests, properties]


unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ pdomTests, pdfTests, ntsodTests, ntiodTests]

properties :: TestTree
properties = testGroup "Properties" [ pdomProps, pdfProps, ntsodProps, ntiodProps]


pdomProps = testGroup "(concerning generalized postdominance)" (theorem1 ++ observation1 ++ observation2)
theorem1 = [
    testProperty "mdom    is reflexive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            mdom = PDOM.mdomOfLfp g
        in (∀) (nodes g) (\n -> n ∈ mdom ! n),
    testProperty "sinkdom is reflexive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfGfp g
        in (∀) (nodes g) (\n -> n ∈ sinkdom ! n),
    testProperty "mdom    is transitive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            mdom = PDOM.mdomOfLfp g
        in (∀) (Map.assocs $ mdom)    (\(x, ys) -> (∀) ys (\y -> (∀) (mdom ! y)     (\z -> z ∈ mdom ! x  ))),
    testProperty "sinkdom    is transitive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfLfp g
        in (∀) (Map.assocs $ sinkdom) (\(x, ys) -> (∀) ys (\y -> (∀) (sinkdom ! y) (\z -> z ∈ sinkdom ! x))),
    testProperty "mdom    has transitive reduction that forms a pseudo forest"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            mdom = PDOM.mdomOfLfp g
            redu = (trr $ fromSuccMap $ mdom :: Gr () ())
            clos = toSuccMap $ trc redu
        in (mdom    == clos) ∧ (∀) (Map.assocs $ toSuccMap $ redu) (\(n, ms) -> Set.size ms <= 1),
    testProperty "sinkdom has transitive reduction that forms a pseudo forest"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfLfp g
            redu = (trr $ fromSuccMap $ sinkdom :: Gr () ())
            clos = toSuccMap $ trc redu
        in (sinkdom == clos) ∧ (∀) (Map.assocs $ toSuccMap $ redu) (\(n, ms) -> Set.size ms <= 1)
  ]
observation1 = [
    testProperty   "rdfs sinkdom approximation"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            n = length $ nodes g
            sinks = controlSinks g
            sinkNodes = Set.fromList [ s | sink <- sinks, s <- sink]


            forest = rdff [ s | (s:_) <- sinks ] g

            forestEdges :: [Tree Node] -> [(Node, Node)]
            forestEdges = concatMap f
              where f (Tree.Node n ts) = [ (n, m) | (Tree.Node m _) <- ts ] ++ concatMap f ts

            isinkdom =       Map.fromList [ (nj, Set.fromList [nj']) | sink <- sinks, (nj,nj') <- zip sink (tail sink ++ [head sink]) ]
                     ⊔ (∐) [ Map.fromList [ (m, Set.fromList [n]) ]  | (n,m) <- forestEdges forest, not $ m ∈ sinkNodes]
            sinkdom = PDOM.sinkdomOfGfp g
        in    (∀) (Map.assocs isinkdom) (\(n, ms) -> Set.size ms <= 1)  ∧  (toSuccMap $ trc $ (fromSuccMap $ isinkdom :: Gr () ())) ⊒ sinkdom
  ]
observation2 = [
    testProperty   "sink boundedness is retained  by isinkdom step"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfLfp g
            redu = toSuccMap (trr $ fromSuccMap $ sinkdom :: Gr () ())
            sinks = controlSinks g
            sinkNodes = Set.fromList [ s | sink <- sinks, s <- sink]
        in (∀) (Map.assocs redu) (\(x, ys) -> (∀) ys (\y ->
             (not $ Set.null $ (sinkdom ! x ∩ sinkNodes)) → (∃) sinks (\sink -> (∀) sink (\s -> s ∈ sinkdom ! x ∧ s ∈ sinkdom ! y))
           ))
  ]
pdomTests = testGroup "(concerning generalized postdominance)" $
  []





pdfProps = testGroup "(concerning generalized postdominance frontiers)" (lemma1 ++ lemma2 ++ lemma3 ++ algorithm2)
lemma1 = [
    testProperty   "mDFFromUpLocalDefViaSinkdoms == mDF"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFFromUpLocalDefViaMdoms g ==
                       PDF.mDF                       g,
    testProperty   "sinkDFFromUpLocalDefViaSinkdoms == sinkDF"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFFromUpLocalDefViaSinkdoms g ==
                       PDF.sinkDF                          g
  ]
lemma2 = [
    testPropertySized 40 "mDFLocalViaSinkdoms == mDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFLocalViaMdoms  g ==
                       PDF.mDFLocalDef          g,
    testProperty   "sinkDFLocalViaSinkdoms == sinkDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFLocalViaSinkdoms  g ==
                       PDF.sinkDFLocalDef          g
  ]
lemma3 = [
    testPropertySized 40 "mDFUpGivenXViaSinkdoms == mDFUpDef"
                $ \(ARBITRARY(g)) ->
                    let mdoms = PDOM.mdomsOf g
                        dfUp    = PDF.mDFUpGivenXViaMdoms g
                        dfUpDef = PDF.mDFUpDef            g
                    in (∀) (Map.assocs mdoms) (\(z, xs) -> (∀) xs (\x -> 
                          dfUp ! (x,z) == dfUpDef ! z
                       )),
    testProperty   "sinkDFUpGivenXViaSinkdoms == sinkDFUpDef"
                $ \(ARBITRARY(g)) ->
                    let sinkdoms = PDOM.sinkdomsOf g
                        dfUp    = PDF.sinkDFUpGivenXViaSinkdoms g
                        dfUpDef = PDF.sinkDFUpDef               g
                    in (∀) (Map.assocs sinkdoms) (\(z, xs) -> (∀) xs (\x -> 
                          dfUp ! (x,z) == dfUpDef ! z
                       ))
  ]
algorithm2 = [ 
    testProperty   "mDFTwoFinger == ntscd"
                $ \(ARBITRARY(g)) ->
                    let imDF = PDF.mDFTwoFinger g
                        mdom = PDOM.mdomOfLfp g
                        ntscd   = NTICD.ntscd g
                    in   (∀) (Map.assocs ntscd)   (\(n, ms) -> (∀) ms (\m -> (n /= m) → (n ∈ imDF ! m)))
                       ∧ (∀) (Map.assocs imDF) (\(m, ns) -> (∀) ns (\n -> (n /= m) → (m ∈ ntscd ! n))),
   testProperty   "isinkDFTwoFinger == nticd"
                $ \(ARBITRARY(g)) ->
                    let isinkDF = PDF.isinkDFTwoFinger g
                        sinkdom = PDOM.sinkdomOfGfp g
                        nticd   = NTICD.nticd g
                    in   (∀) (Map.assocs nticd)   (\(n, ms) -> (∀) ms (\m -> (n /= m) → (n ∈ isinkDF ! m)))
                       ∧ (∀) (Map.assocs isinkDF) (\(m, ns) -> (∀) ns (\n -> (n /= m) → (m ∈ nticd ! n)))
  ]


pdfTests = testGroup "(concerning generalized postdominance frontiers)" $
  []


ntsodProps = testGroup "(concerning nontermination   sensititve order dependence)" (lemma4 ++ observation3 ++ observation4)
lemma4 = [
      testProperty  "dod is contained in imdom cycles, and only possible for immediate entries into cycles"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom  = PDOM.mdomOfLfp g
                        dod = ODEP.dod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∈ mdom ! m2 ∧ m2 ∈ mdom ! m1))
                        ∧ (∀) ns (\n -> (not $ n ∈ mdom ! m1) ∧ (not $ n ∈ mdom ! m2))
                        ∧ (∀) ns (\n -> (∀) (mdom ! n) (\m -> (m /= n) → (
                            (m ∈ mdom ! m1) ∧ (m ∈ mdom ! m2) ∧ (m1 ∈ mdom ! m) ∧ (m2 ∈ mdom ! m)
                          )))
                        )
  ]
observation3 = [
      testProperty  "ntsod is contained in imdom cycles, and only possible for immediate entries into cycles"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom  = PDOM.mdomOfLfp g
                        ntsod = ODEP.myDod g
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∈ mdom ! m2 ∧ m2 ∈ mdom ! m1))
                        ∧ (∀) ns (\n -> (not $ n ∈ mdom ! m1) ∧ (not $ n ∈ mdom ! m2))
                        ∧ (∀) ns (\n -> (∀) (mdom ! n) (\m -> (m /= n) → (
                            (m ∈ mdom ! m1) ∧ (m ∈ mdom ! m2) ∧ (m1 ∈ mdom ! m) ∧ (m2 ∈ mdom ! m)
                          )))
                        )
  ]
observation4 = [
      testPropertySized 60  "myDod reduction to ntscd"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = PDOM.imdomOfTwoFinger6 g
                        (cycleOf,cycles) = findCyclesM (fmap fromSet imdom)
                        ntsod = ODEP.myDod g
                        gNOfNode =
                          Map.fromList [ (m, gN) |
                                             bigM <- cycles,
                                             let bigN_M = Set.fromList [ n | n <- nodes g, (∃) (imdom ! n) (\m -> m ∈ bigM) ],
                                             let fromN = Set.fromList $ dfs  (Set.toList bigN_M) g,
                                             let toM   = Set.fromList $ rdfs (Set.toList bigM) g,
                                             let gN = subgraph (Set.toList $ fromN ∩ toM) g,
                                             m <- Set.toList bigM
                          ]
                    in   (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                           let ntscd' = NTICD.ntscd (delSuccessorEdges (gNOfNode ! m2) m2) in
                           (∀) ns (\n -> (∃) cycles (\bigM -> m1 ∈ bigM ∧ m2 ∈ bigM ∧ (∃) (imdom ! n) (\m -> m ∈ bigM) ∧ m1 ∈ ntscd' ! n))
                         )
                       ∧ (∀) (cycles) (\bigM -> let gN = gNOfNode ! (Set.findMin bigM) in
                           (∀) bigM (\m2 -> let nticd' = NTICD.nticd (delSuccessorEdges gN m2) in
                             (∀) (Map.assocs nticd') (\(n,ms) -> (∀) ms (\m1 -> (m1 ∈ bigM) → (n ∈ ntsod ! (m1, m2))))
                           )
                         ),
      testProperty  "myDodFastPDom               ≡ myDod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.myDodFastPDom   g ≡
                       ODEP.myDod           g
  ]
ntsodTests = testGroup "(concerning nontermination   sensititve order dependence)" $
  []


ntiodProps = testGroup "(concerning nontermination insensititve order dependence)" (observation5 ++ observation6 ++ observation8 ++ theorem5 ++ observation10 ++  observationANON)
observation5 = [
      testPropertySized 60  "ntiod is contained in isinkdom cycles"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom  = PDOM.sinkdomOfLfp g
                        ntiod = ODEP.myWod g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∈ sinkdom ! m2 ∧ m2 ∈ sinkdom ! m1))
                        ∧ (∀) ns (\n -> (∀) (sinkdom ! n) (\m -> (m /= n) → (
                            (m ∈ sinkdom ! m1) ∧ (m ∈ sinkdom ! m2) ∧ (m1 ∈ sinkdom ! m) ∧ (m2 ∈ sinkdom ! m)
                          )))
                        )
  ]
observation6 = [
      testPropertySized 60  "myWod reduction to nticd"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom = PDOM.isinkdomOfTwoFinger8 g
                        (cycleOf,cycles) = findCyclesM (fmap fromSet isinkdom)
                        ntiod = ODEP.myWod g
                        gNOfNode =
                          Map.fromList [ (m, gN) |
                                             bigM <- cycles,
                                             let bigN_M = Set.fromList [ n | n <- nodes g, (∃) (isinkdom ! n) (\m -> m ∈ bigM) ],
                                             let fromN = Set.fromList $ dfs  (Set.toList bigN_M) g,
                                             let toM   = Set.fromList $ rdfs (Set.toList bigM) g,
                                             let gN = subgraph (Set.toList $ fromN ∩ toM) g,
                                             m <- Set.toList bigM
                          ]
                    in   (Set.fromList cycles == Set.fromList [ Set.fromList sink | sink <- controlSinks g, (length sink) > 1])
                       ∧ (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                           let nticd' = NTICD.nticd (delSuccessorEdges (gNOfNode ! m2) m2) in
                           (∀) ns (\n -> (∃) cycles (\bigM -> m1 ∈ bigM ∧ m2 ∈ bigM ∧ (∃) (isinkdom ! n) (\m -> m ∈ bigM) ∧ m1 /= n ∧ m1 ∈ nticd' ! n))
                         )
                       ∧ (∀) (cycles) (\bigM -> let gN = gNOfNode ! (Set.findMin bigM) in
                           (∀) bigM (\m2 -> let nticd' = NTICD.nticd (delSuccessorEdges gN m2) in
                             (∀) (Map.assocs nticd') (\(n,ms) -> (∀) ms (\m1 -> (m1 ∈ bigM ∧ m1 /= n) → (n ∈ ntiod ! (m1, m2))))
                           )
                         ),
      testPropertySized 60  "myWodFastPDom               ≡ myWod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.myWodFastPDom   g ≡
                       ODEP.myWod           g
  ]
observation8 = [
      testPropertySized 60  "myWodFastPDom               ≡ myWod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.myWodFastPDomSimpleHeuristic   g ≡
                       ODEP.myWod                          g
  ]
theorem5 = [
    testPropertySized 60 "nticdMyWodSlice == nticdMyWodSliceViaNticd == nticdMyWodSliceViaISinkDom ==  for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer0  = ODEP.nticdMyWodSlice                g
                    slicer1  = NTICD.nticdMyWodSliceViaNticd       g
                    slicer2  = NTICD.nticdMyWodSliceViaISinkDom    g
                in   slicer0 ms == slicer1 ms
                   ∧ slicer1 ms == slicer2 ms
  ]
observation10 = [
    testPropertySized 60  "nticdMyWodSlice == nticdMyWodSliceViaNticd even when using data dependencies"
    $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) seed1 seed2 ->
                let g = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                      where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)

                    ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                    nticd = PDF.isinkDFTwoFinger g
                    mywod =  ODEP.myWodFastPDomSimpleHeuristic g
                    slicer = combinedBackwardSlice g (ddep ⊔ nticd) mywod

                    g' = foldr (flip delSuccessorEdges) g ms
                    nticd' = PDF.isinkDFTwoFinger g'
                    empty = Map.empty
                    slicer' = combinedBackwardSlice g (ddep ⊔ nticd') empty
                in slicer ms == slicer' ms
  ]
observationANON = [
    testPropertySized 60 "wccSliceViaISInkDom == wccSlice for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer0 = FCACD.wccSlice g
                    slicer1 = NTICD.wccSliceViaISinkDom     g
                    slicer2 = ODEP.wccSliceViaNticd g
                in   slicer0 ms == slicer1 ms
                   ∧ slicer1 ms == slicer2 ms,
    testPropertySized 40 "wodTEILSliceViaISinkDom = wodTEILSliceViaNticd == wodTEILSlice for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer0  = ODEP.wodTEILSlice               g
                    slicer1  = NTICD.wodTEILSliceViaISinkDom   g
                    slicer2  = ODEP.wodTEILSliceViaNticd       g
                in   slicer0 ms == slicer1 ms
                   ∧ slicer1 ms == slicer2 ms
  ]



ntiodTests = testGroup "(concerning nontermination insensititve order dependence)" (observation9)
observation9 =  [
      testCase ("nontermination insensitive slices cannot in general be computed by binary control dependence") $
                   let g0 = mkGraph [(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,()),(8,()),(9,()),(10,()),(11,()),(12,()),(13,()),(14,())] [(1,2,()),(1,10,()),(2,3,()),(2,6,()),(3,4,()),(3,9,()),(4,12,()),(4,14,()),(5,3,()),(6,7,()),(7,8,()),(7,11,()),(8,6,()),(9,10,()),(11,8,()),(11,13,()),(12,5,()),(13,8,()),(14,5,())] :: Gr () ()
                       g = subgraph [6,7,8,11,13] g0
                       edges = [(n,m,()) | n <- nodes g, m <- nodes g ]
                       cds = [ cd | es <- sublists edges, let cdG = mkGraph (labNodes g) es :: Gr () (), let cd = toSuccMap cdG]
                       nticdntiodslicer  = ODEP.nticdMyWodSlice g
                       wodslicer         = ODEP.wodTEILSlice g
                       wccslicer         = FCACD.wccSlice g
                   in (not $ (∃) cds (\cd -> (∀) (fmap Set.fromList $ sublists $ nodes g) (\ms ->
                        let s = combinedBackwardSlice g cd Map.empty ms in s == wodslicer ms ∨ s == nticdntiodslicer ms ∨ s == wccslicer ms
                      ))) @? ""
  ]
