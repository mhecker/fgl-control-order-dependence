{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Dod where

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
dod        = defaultMain                               $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]
dodX       = defaultMainWithIngredients [antXMLRunner] $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]


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
                       slicer = combinedBackwardSlice (ddep ⊔ ntscd) ntsod 
                   in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 ->
                        let ms  = [m1, m2, m3]
                            msS = Set.fromList ms
                            g' = foldr (flip delSuccessorEdges) g ms
                            ntscd' = PDF.mDFTwoFinger g'
                            empty = Map.empty
                            slicer' = combinedBackwardSlice (ddep ⊔ ntscd') empty
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
                        sum = Map.foldr (\ns s -> Set.size ns + s) 0
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
