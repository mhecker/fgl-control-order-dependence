{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Sensitivedom where

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

sensitivedom      = defaultMain                               $ testGroup "sensitiveDom"     [ mkTest [sensitiveDomTests],  mkProp [sensitiveDomProps]]
sensitivedomX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "sensitiveDom"     [ mkTest [sensitiveDomTests],  mkProp [sensitiveDomProps]]



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

