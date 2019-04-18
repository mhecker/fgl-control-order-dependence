{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

module Program.Properties.InvalidProperties where

-- #define UNCONNECTED
#ifdef UNCONNECTED
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


import Prelude hiding (all)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)
import qualified Control.Exception.Base (assert)

import Algebra.Lattice
import Unicode

import Test.Tasty
import Test.Tasty.Providers (singleTest)
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.Options

import Test.Tasty.Runners.AntXML
import Test.Tasty.Ingredients.Basic

import Test.Tasty.ExpectedFailure

import Test.QuickCheck (Testable, property)
import Test.QuickCheck.Property (Property(..))

import Debug.Trace (traceShow)

import Data.Ord

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map ( Map, (!) )

import Util(restrict, sampleFrom, moreSeeds,minimalPath,reachableFromIn, findCyclesM, fromSet, sublists)

import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trcOfTrrIsTrc, withUniqueEndNode, fromSuccMap, removeDuplicateEdges, delSuccessorEdges, toSuccMap)
import Data.Graph.Inductive (mkGraph, edges, suc, delEdges, grev, nodes, efilter, pre, insEdge, labNodes)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.DFS (dfs, rdfs, reachable)
import Data.Graph.Inductive.Query.Dominators (iDom)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (Input(..), runInput, observable, allChoices, isLowTimingEquivalent)

import Program (Program, tcfg)
import Program.Defaults

import Program.Typing.FlexibleSchedulerIndependentChannels (isSecureFlexibleSchedulerIndependentChannelFor)
import Program.Properties.Analysis
import Program.Properties.CDom
import Data.Graph.Inductive.Query.BalancedSCC -- TODO: refactor that module into 2 seperate modules

import Execution (allFinishedExecutionTraces, someFinishedAnnotatedExecutionTraces)
import Program.Examples
import Program.Analysis hiding (timing)
import Program.CDom
import Program.Generator (toProgram, GeneratedProgram, SimpleCFG(..))
import Data.Graph.Inductive.Arbitrary

import Data.Graph.Inductive (Node, subgraph)
import Data.Graph.Inductive.Query.ControlDependence (controlDependenceGraphP, controlDependence)
import Data.Graph.Inductive.Util (controlSinks)
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    Reachability(..),
    combinedBackwardSlice,
    cost1, cost1F,
    ntscdMyDodSlice, ntscdMyDodSliceViaNtscd, imdomOfTwoFinger6,
    validTimdomFor,
    solveTimingEquationSystem, snmTimingEquationSystem, timingF3EquationSystem,
    sinkdomOfGfp, sinkdomNaiveGfpFullTop, sinkdomOf,
    noJoins, mmayOf, mmayOf', stepsCL,  stepsCLLfp,
    dfFor, anyDFFromUpLocalDefViaAnydoms,
    ntscdTimingSlice, tscdSliceForTrivialSinks,
    mDF,
    timingSolvedF3sparseDependence, timingSolvedF3dependence,
    timdomOfPrevNaiveLfp, itimdomMultipleOfTwoFinger,
    withPossibleIntermediateNodesFromiXdom,
    smmnFMustDod,
    isinkdomOfTwoFinger8,
    imdomOfTwoFinger7, joiniSinkDomAround,
    myWod, isinkdomOfSinkContraction, myDod, myWodFast, wodFast, myWodFastSlice,
    smmnLfp, smmnGfp, fMustBefore, fMust,
    dodDef, dodSuperFast, wodDef,
    dodColoredDagFixed, dodColoredDag,
    wodTEIL', wodTEILSlice,
    wodTEILPDomSlice,
    nticdF5,                         ntscdFig4,       ntscdF3, nticdF5, nticdFig5, nticdIndus, nticdF3,
    nticdF5GraphP, nticdIndusGraphP, ntscdFig4GraphP,  ntscdF3GraphP, nticdF5GraphP, nticdFig5GraphP,
    nticdMyWodSlice,
    nticdMyWodSliceViaEscapeNodes, nticdMyWodSliceViaNticd, nticdMyWodSliceViaCutAtRepresentatives, nticdMyWodSliceViaChoiceAtRepresentatives,
    snmF4WithReachCheckGfp,
    snmF3, snmF5
  ) 
import qualified Data.Graph.Inductive.Query.NTICDUnused as NTICDUnused (rofldomOfTwoFinger7, myCD, myCDFromMyDom, myWodFromMay)
import qualified Data.Graph.Inductive.Query.TSCD        as TSCD (timingCorrection, tscdCostSlice, timDF, timdomOfLfp, timdomsOf,)
import qualified Data.Graph.Inductive.Query.FCACD as FCACD (wccSlice)

main      = all

all        = defaultMain                               $ expectFail $ tests
allX       = defaultMainWithIngredients [antXMLRunner] $ expectFail $ tests
cdom       = defaultMain                               $ expectFail $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
cdomX      = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
balanced   = defaultMain                               $ expectFail $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
balancedX  = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
timing     = defaultMain                               $ expectFail $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
timingX    = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
timingDep  = defaultMain                               $ expectFail $ testGroup "timingDep" [ mkTest [timingDepTests], mkProp [timingDepProps] ]
timingDepX = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "timingDep" [ mkTest [timingDepTests], mkProp [timingDepProps] ]
giffhorn   = defaultMain                               $ expectFail $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]
giffhornX  = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "giffhorn"  [ mkTest [giffhornTests], mkProp [giffhornProps] ]
soundness  = defaultMain                               $ expectFail $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]
soundnessX = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "soundness" [ mkTest [soundnessTests], mkProp [soundnessProps] ]
preccex    = defaultMain                               $ expectFail $ testGroup "preccex"   [ mkTest [precisionCounterExampleTests] ]
preccexX   = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "preccex"   [ mkTest [precisionCounterExampleTests] ]

nticd      = defaultMain                               $ expectFail $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]
nticdX     = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "nticd"     [ mkTest [nticdTests], mkProp [nticdProps]]

ntscd      = defaultMain                               $ expectFail $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]
ntscdX     = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "ntscd"     [ mkTest [ntscdTests], mkProp [ntscdProps]]

insensitiveDom    = defaultMain                               $ expectFail $ testGroup "insensitiveDom"   [                                mkProp [insensitiveDomProps]]
insensitiveDomX   = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "insensitiveDom"   [                                mkProp [insensitiveDomProps]]

misc       = defaultMain                               $ expectFail $ testGroup "misc"      [ mkProp [miscProps] ]
miscX      = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "misc"      [ mkProp [miscProps] ]
dod        = defaultMain                               $ expectFail $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]
dodX       = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]
wod        = defaultMain                               $ expectFail $ testGroup "wod"       [ mkTest [wodTests], mkProp [wodProps]]
wodX       = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "wod"       [ mkTest [wodTests], mkProp [wodProps]]

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"


tests :: TestTree
tests = testGroup "Tests" [unitTests, properties]


properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps, cdomProps, cdomCdomProps, balancedParanthesesProps, soundnessProps, timingDepProps, insensitiveDomProps ]

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests, cdomTests, cdomCdomTests, balancedParanthesesTests, soundnessTests, precisionCounterExampleTests ]


soundnessProps =  localOption d $ testGroup "(concerning soundness)" [
    testPropertySized 10
     ("allSoundIntraMulti [ unsoundIRLSODAttempt  ] ")
     ( allSoundIntraMulti [ unsoundIRLSODAttempt  ] )
  ]
 where d = 2000000 :: QuickCheckTests

soundnessTests =  testGroup "(concerning soundness)" $
  [ testCase      ("allSoundP [ timingClassification using idomChef ] for " ++ exampleName)
                  ( allSoundP [ isSecureTimingClassificationIdomChef ] example @? "")
  | (exampleName, example) <- [ ("cdomIsBroken'", cdomIsBroken') ]
  ] ++
  [ testCase      ("allSoundP [ unsoundIRLSODAttempt ] for " ++ exampleName)
                  ( allSoundP [ unsoundIRLSODAttempt ] example @? "")
  | (exampleName, example) <- [ ("figure5right", figure5right) ]
  ] ++
  []


precisionCounterExampleTests = testGroup "(counterxamples to: timingClassification(-DomPaths) is at least as precise as minimalClassification)" $
  []


timingDepProps = testGroup "(concerning timingDependence)" [
    testProperty   "mDF   ⊑ timDF"
                $ \(ARBITRARY(g)) ->
                       NTICD.mDF    g ⊑
                       TSCD.timDF  g,
    testProperty   "anyDFFromUpLocalDefViaAnydoms == anyDF"
                $ \(ARBITRARY(g)) (UNCONNECTED(anydom0)) -> 
                   let anydomG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges anydom0, let n' = toG ! n, let m' = toG ! m, (n' == m') ∨ (∀) (n' : suc g n') (\x' -> m' `elem` reachable x' g) ] :: Gr ()()
                          where toG = Map.fromList $ zip (nodes anydom0) (cycle $ nodes g)
                       anydom = NTICD.stepsCLLfp g $
                                Map.fromList [ (n, Set.fromList [n]) | n <- nodes anydomG ]
                              ⊔ Map.fromList [ (n, Set.fromList $ suc anydomG n) | n <- nodes anydomG ]
                   in NTICD.anyDFFromUpLocalDefViaAnydoms anydom g ==
                      NTICD.dfFor                         g anydom,
    testPropertySized 25 "timingSolvedF3dependence  is minimal wrt. timed traces in graphs without self-node"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g0 = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        g = efilter (\(n,m,_) -> n /= m) g0
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        ms = Set.fromList [m1,m2]
                        s = ms ⊔ Set.fromList [n | (n, ms') <- Map.assocs $ NTICD.timingSolvedF3dependence g, (∃) ms (\m -> m ∈ ms')]
                    
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (∀) s (\n -> n == m1  ∨  n == m2  ∨
                         let s' = Set.delete n s
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowTimingEquivalent g s' input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in different
                                  )
                               ))
                         in (if differentobservation then id else traceShow (m1, m2, n, differentobservation)) $
                            differentobservation
                       ),
      testProperty  "timingSolvedF3sparseDependence is intransitive for graphs with unique end Node"
                $ \(ARBITRARY(generatedGraph)) ->
                       let (_, g) = withUniqueEndNode () () generatedGraph
                           tdepsparse= NTICD.timingSolvedF3sparseDependence g
                       in  (∀) (Map.assocs tdepsparse) (\(n,n's) ->
                             (∀) (n's) (\n' ->
                               (∀) (tdepsparse ! n') (\n'' -> not $ n'' ∈ n's)
                             )
                           ),
    testProperty  "timingSolvedF3sparseDependence is intransitive for  For-Programs, which by construction are reducible"
                $ \generated ->
                       let p = toProgram generated  :: Program Gr
                           g = tcfg p
                           tdepsparse = NTICD.timingSolvedF3sparseDependence g
                       in  (∀) (Map.assocs tdepsparse) (\(n,n's) ->
                             (∀) (n's) (\n' ->
                               (∀) (tdepsparse ! n') (\n'' -> not $ n'' ∈ n's)
                             )
                           )
  ]
  
timingDepTests = testGroup "(concerning timingDependence)" $
  [ testCase ("fmap (Set.map fst) $ timdomOfLfp is transitive for " ++ exampleName) $ 
                let timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                in (∀) (Map.assocs $  timdom) (\(x, ys) -> (∀) ys (\y -> (∀) (timdom ! y) (\z -> z ∈ timdom ! x)))
    @? ""
  | (exampleName, g :: Gr () ()) <- [("exampleTimingDepInterestingTwoFinger", exampleTimingDepInterestingTwoFinger)]
  ] ++
  [ testCase ("timdomsOf* ==  timdomOfLfp for " ++ exampleName) $ 
                    let timdom  = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                        timdoms = TSCD.timdomsOf g
                        gdom  = fromSuccMap timdom  :: Gr () ()
                        gdoms = fromSuccMap timdoms :: Gr () ()

                    in gdom == trc gdoms
    @? ""
  | (exampleName, g :: Gr () ()) <- [("exampleTimingDepInterestingTwoFinger", exampleTimingDepInterestingTwoFinger)]
  ] ++
  [ testCase ("timingCorrection tscdCostSlice == ntscdMyDodSlice for " ++ exampleName) $ 
                let (cost, _) = TSCD.timingCorrection g (NTICD.cost1 g)
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdmydodslicer  = NTICD.ntscdMyDodSliceViaNtscd g

                    (cycleOf, cycles) = findCyclesM $ fmap fromSet $ imdom
                      where imdom = NTICD.imdomOfTwoFinger6 g
                    s  = tscdcostslicer   ms
                    s' = ntscdmydodslicer ms
                in   (   (s == s'))
                   ∨ (   (s  ⊇ s')
                      ∧ (∃) cycles (\cycle -> Set.size (cycle ∩ s') == 1))
    @? ""
  | (exampleName, g :: Gr () (), ms) <- [(" exampleTimingDepCorrectionInteresting11",       exampleTimingDepCorrectionInteresting11      , Set.fromList [-30,6]),
                                         (" exampleTimingDepCorrectionInteresting11Simple", exampleTimingDepCorrectionInteresting11Simple, Set.fromList [-30,6])
                                        ]
  ] ++
  [ testCase ("timingCorrection tscdCostSlice == ntscdMyDodSlice for " ++ exampleName) $ 
                let (cost, _) = TSCD.timingCorrection g (NTICD.cost1 g)
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdmydodslicer  = NTICD.ntscdMyDodSliceViaNtscd g

                    (cycleOf, cycles) = findCyclesM $ fmap fromSet $ imdom
                      where imdom = NTICD.imdomOfTwoFinger6 g

                in Control.Exception.Base.assert ((∀) cycles (\cycle -> Set.size (cycle ∩ ms) /= 1)) $
                   tscdcostslicer ms == ntscdmydodslicer ms
    @? ""
  | (exampleName, g :: Gr () (), ms) <- [(" exampleTimingDepCorrectionInteresting10",  exampleTimingDepCorrectionInteresting10, Set.fromList [-11,-10])]
  ] ++
  [ testCase ("itimdomMultipleOfTwoFinger        relates to timingF3EquationSystem for " ++ exampleName) $ 
                       let timingEqSolved    = NTICD.solveTimingEquationSystem $ NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem
                           itimdomMultiple   = NTICD.itimdomMultipleOfTwoFinger g
                           mustReachFromIn   = reachableFromIn $ NTICD.withPossibleIntermediateNodesFromiXdom g $ itimdomMultiple
                           mustReachFrom x   = suc isinkdomTrc x
                             where isinkdom    = NTICD.isinkdomOfTwoFinger8 g
                                   isinkdomTrc = trc $ fromSuccMap isinkdom :: Gr () ()
                       in  (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in ((m /= p) ∧ m ∊ mustReachFrom p) →
                                  case rmq of
                                     NTICD.FixedSteps s            -> Set.fromList [1+s] == mustReachFromIn p m
                                     NTICD.FixedStepsPlusOther s y -> Set.fromList [1+s] == mustReachFromIn p y
                                     NTICD.UndeterminedSteps       -> Set.fromList []    == mustReachFromIn p m
                           )
    @? ""
  | (exampleName, g :: Gr () ()) <- [("exampleTimingDepInterestingTwoFinger5", exampleTimingDepInterestingTwoFinger5)]
  ] ++
  [ testCase ("itimdomMultipleOfTwoFinger^*       == timdomOfLfp for " ++ exampleName) $ 
                       let itimdomMultiple   = NTICD.itimdomMultipleOfTwoFinger g
                           timdomOfLfp       = TSCD.timdomOfLfp g
                           mustReachFromIn   = reachableFromIn $ NTICD.withPossibleIntermediateNodesFromiXdom g $ itimdomMultiple
                       in  
                           (∀) (Map.assocs timdomOfLfp) (\(n, ms) ->
                              (∀) (ms) (\(m,steps) -> Set.fromList [steps] == mustReachFromIn n m)
                           )
                         ∧ (∀) (nodes g) (\n -> (∀) (nodes g) (\m ->
                              mustReachFromIn n m == Set.fromList [ steps | (m', steps) <- Set.toList $ timdomOfLfp ! n, m == m']
                           ))
    @? ""
  | (exampleName, g :: Gr () ()) <-  [("exampleTimingDepInterestingTwoFinger5", exampleTimingDepInterestingTwoFinger5)]
  ] ++
  [ testCase ("timdomOfPrevNaiveLfp == timdomOfTwoFinger^* for " ++ exampleName) $ 
                let itimdom = NTICD.itimdomMultipleOfTwoFinger g
                    timdomPrevNaive = NTICD.timdomOfPrevNaiveLfp g
                    timdomPrevFinger = Map.fromList [ (n, Set.fromList [ (m, steps) | m <- nodes g, path <- minimalPath itimdom n m, let steps = sum $ fmap snd path ]) | n <- nodes g]
                in  timdomPrevNaive == timdomPrevFinger
    @? ""
  | (exampleName, g :: Gr () ()) <- [("exampleTimingDepInterestingTwoFinger5", exampleTimingDepInterestingTwoFinger5)]
  ] ++
  [ testCase ("validTimdomFor entries > 0 for " ++ exampleName) $ 
                let validEntries = NTICD.validTimdomFor g (NTICD.cost1F g) itimdommultiple entries

                    itimdommultiple = NTICD.itimdomMultipleOfTwoFinger g
                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdommultiple ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (_, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdommultiple
                    cycleNodes = (∐) cycles
                in (∀) (Map.assocs validEntries) (\(n, f) -> f > 0)
    @? ""
  | (exampleName, g :: Gr () ()) <- [("exampleTimingDepInterestingTwoFinger5", exampleTimingDepInterestingTwoFinger5)]
  ] ++
  [ testCase ("timdomOfTwoFinger        relates to timingF3EquationSystem for" ++ exampleName) $
                       let timingEqSolved    = NTICD.solveTimingEquationSystem $ NTICD.snmTimingEquationSystem g NTICD.timingF3EquationSystem
                           itimdomMultiple   = NTICD.itimdomMultipleOfTwoFinger g
                           mustReachFromIn   = reachableFromIn $ NTICD.withPossibleIntermediateNodesFromiXdom g $ itimdomMultiple
                           mustReachFrom x   = suc isinkdomTrc x
                             where isinkdom    = NTICD.isinkdomOfTwoFinger8 g
                                   isinkdomTrc = trc $ fromSuccMap isinkdom :: Gr () ()
                       in  (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in ((m /= p) ∧ m ∊ mustReachFrom p) →
                                  case rmq of
                                     NTICD.FixedSteps s            -> Set.fromList [1+s] == mustReachFromIn p m
                                     NTICD.FixedStepsPlusOther s y -> Set.fromList [1+s] == mustReachFromIn p y
                                     NTICD.UndeterminedSteps       -> Set.fromList []    == mustReachFromIn p m
                           )
    @? ""
  | (exampleName, g :: Gr () ()) <- [("exampleTimingDepInterestingTwoFinger5", exampleTimingDepInterestingTwoFinger5)]
  ] ++
  [ testCase "ntscdTimingSlice == tscdSliceForTrivialSinks"
    $           let g    = mkGraph [(-48,()),(-19,()),(-13,()),(-6,()),(47,())] [(-48,-13,()),(-19,-48,()),(-13,-48,()),(-6,-19,()),(-6,-13,()),(47,-48,()),(47,-19,()),(47,-13,()),(47,-6,())] :: Gr () ()
                    ntscdtimingslicer  = NTICD.ntscdTimingSlice g
                    tscdslicer         = NTICD.tscdSliceForTrivialSinks        g
                    ms = Set.fromList [-13]
                in ntscdtimingslicer  ms == tscdslicer  ms @? ""
  ] ++
  []



timingClassificationDomPathsProps = testGroup "(concerning timingClassificationDomPaths)" $
  [ testCase ("isSecureSimonClassification is at least as precise as isSecureFlexibleSchedulerIndependentChannel for " ++ exampleName)
    $   isSecureFlexibleSchedulerIndependentChannelFor forProgram ⊑ isSecureSimonClassification program   @? ""
  | (exampleName, program, forProgram) <- [("minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD", minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD, minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODFor) ]
  ] ++
  [ testCase ("isSecureMinimalClassification is at least as precise as isSecureFlexibleSchedulerIndependentChannel for " ++ exampleName)
    $   isSecureFlexibleSchedulerIndependentChannelFor forProgram ⊑ isSecureMinimalClassification program   @? ""
  | (exampleName, program, forProgram) <- [("minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD", minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD, minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODFor) ]
  ] ++
  [ testCase ("isSecureFlexibleSchedulerIndependentChannel is at least as precise as isSecureTimingClassificationAtUses for " ++ exampleName)
    $   isSecureTimingClassificationAtUses program ⊑ isSecureFlexibleSchedulerIndependentChannelFor forProgram @? ""
  | (exampleName, code) <- [("figure5left", figure5leftCode) ],
    let (program, forProgram) = (code2Program code, code2ForProgram code)
  ] ++
  [ testCase ("isSecureTimingCombinedTimingClassification is at least as precise as isSecureTimingClassification for " ++ exampleName)  $   isSecureTimingCombinedTimingClassification p ⊒ isSecureTimingClassification p @? ""
  | (exampleName, p) <- [("timingSecureButNotCombinedTimingSecure", timingSecureButNotCombinedTimingSecure) ]
  ] ++
  []

timingClassificationDomPathsTests = testGroup "(concerning timingClassificationDomPaths)" $
  []



giffhornProps = testGroup "(concerning Giffhorns LSOD)" [
  ]
giffhornTests = testGroup "(concerning Giffhorns LSOD)" $
  []



nticdProps = testGroup "(concerning nticd )" [
    testProperty ("nticdF5               /= nticdF3 implies that\n" ++ 
                  "snmF5                  ⊑  snmf3                  , for graphs with unique end node property, without self-edges")
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                        selfedges = [ e | e@(n,m) <- edges g, n == m]
                    in
                       selfedges == [] &&
                       NTICD.nticdF5      g /=
                       NTICD.nticdF3      g 
                       ==>
                       NTICD.snmF5        g ⊑
                       NTICD.snmF3        g,
    testProperty  "controlDependence      == nticdF                for graphs with unique end node property"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in controlDependence      g exit ==
                       NTICD.nticdF5          g,
    testProperty  "controlDependence      == nticdFig5             for graphs with unique end node property"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in controlDependence      g exit ==
                       NTICD.nticdFig5        g,
    testProperty  "controlDependence      == nticdIndus            for graphs with unique end node property"
                $ \((CG entry generatedGraph) :: (Connected Gr () ())) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in controlDependence      g exit ==
                       NTICD.nticdIndus       g
  ]
  
nticdTests = testGroup "(concerning nticd)" $
  [  testCase    ( "snmF5                     ⊑  snmF3 for " ++ exampleName)
                  $ let g = tcfg p
                    in
                       NTICD.snmF5        g ⊑
                       NTICD.snmF3        g
                    @? ""
  | (exampleName, p) <- failingSnmF3F5
  ] ++
  [  testCase    ( "controlDependenceGraphP   ==       nticdF5GraphP for " ++ exampleName)
                  $ controlDependenceGraphP p == NTICD.nticdF5GraphP p @? ""
  | (exampleName, p) <- failingNticd
  ] ++
  [  testCase    ( "controlDependenceGraphP   ==       nticdFig5GraphP for " ++ exampleName)
                  $ controlDependenceGraphP p == NTICD.nticdFig5GraphP p @? ""
  | (exampleName, p) <- failingNticd
  ] ++
  [  testCase    ( "controlDependenceGraphP   ==       nticdIndusGraphP for " ++ exampleName)
                  $ controlDependenceGraphP p == NTICD.nticdIndusGraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []


ntscdTests = testGroup "(concerning ntscd)" $
  [  testCase    ( "wod ⊆ ntscd for reducible graphs, as conjectured in [1], page 19 for" ++ exampleName)
            $  let g = tcfg p
                   wod = NTICD.wodDef g
                   ntscd = NTICD.ntscdF3 g
               in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                    (∀) (ns) (\n ->   (m1 ∈ ntscd ! n)
                                    ∨ (m2 ∈ ntscd ! n)
                              )
                    ) @? ""
  | (exampleName, p) <- failingWodNtscdReducible
  ] ++
  [  testCase    ( "ntscdFig4GraphP         ==       ntscdF3GraphP for " ++ exampleName)
            $ NTICD.ntscdFig4GraphP p       == NTICD.ntscdF3GraphP p @? ""
  | (exampleName, p) <- failingNtscd
  ] ++
  []

ntscdProps = testGroup "(concerning ntscd )" [
    testProperty  "wod ⊆ ntscd for reducible graphs, as conjectured in [1], page 19"
                $ \generated -> let  p :: Program Gr = toProgram generated
                                     g = tcfg p
                                     wod = NTICD.wodDef g
                                     ntscd = NTICD.ntscdF3 g
                                in (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                                      (∀) (ns) (\n ->   (m1 ∈ ntscd ! n)
                                                      ∨ (m2 ∈ ntscd ! n)
                                      )
                                  ),
  testProperty  "ntscdFig4GraphP          == ntscdF3GraphP"
                $ \generated -> let  p :: Program Gr = toProgram generated in
                  NTICD.ntscdFig4GraphP p   == NTICD.ntscdF3GraphP p,
    testProperty  "ntscdFig4                == ntscdF3"
                $ \((CG entry g) :: (Connected Gr () ())) ->
                    let exit = entry -- all this does is add a self-loop to entry
                    in NTICD.ntscdFig4       g ==
                       NTICD.ntscdF3         g
  ]


insensitiveDomProps = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" [
    testProperty   "sinkdomOf             == sinkdomNaiveGfpFullTop"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.sinkdomOf              g ==
                       NTICD.sinkdomNaiveGfpFullTop g,
    testPropertySized 20 "sinkdom g_{M/->}^{->*M} ⊆ (sinkdom g)|{->*M}"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = NTICD.sinkdomOfGfp g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 -> let ms = [m1,m2,m3] in
                         let toMs = rdfs ms g
                             g' = foldr (flip delSuccessorEdges) (subgraph toMs g) ms
                             sinkdom' = NTICD.sinkdomOfGfp g'
                         in sinkdom' ⊑ restrict sinkdom (Set.fromList toMs)
                       ))),
    testProperty "sinkdom g^{M->*}^{->*M} ⊆ (sinkdom g)|{->*M} for random sets M of random Size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        sinkdom = NTICD.sinkdomOfGfp g
                        n  = length $ nodes g
                        ms =  [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        toMs = rdfs ms g
                        g' = foldr (flip delSuccessorEdges) (subgraph toMs g) ms
                        sinkdom' = NTICD.sinkdomOfGfp g'
                    in sinkdom' ⊑ restrict sinkdom (Set.fromList toMs),
    testPropertySized 20 "sinkdom g^{->*M} == (sinkdom g)|{->*M}"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = NTICD.sinkdomOfGfp g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 -> let ms = [m1,m2,m3] in
                         let toMs = rdfs ms g
                             g' = subgraph toMs g
                             sinkdom' = NTICD.sinkdomOfGfp g'
                         in sinkdom' == restrict sinkdom (Set.fromList toMs)
                       ))),
    testProperty "sinkdom g^{->*M} == (sinkdom g)|{->*M} for random sets M of random Size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        sinkdom = NTICD.sinkdomOfGfp g
                        n  = length $ nodes g
                        ms =  [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        toMs = rdfs ms g
                        g' = subgraph toMs g
                        sinkdom' = NTICD.sinkdomOfGfp g'
                    in sinkdom' == restrict sinkdom (Set.fromList toMs)
 ]

cdomCdomProps = testGroup "(concerning cdoms)" $
  [ testCase ("cdomIsCdom' idomChef for " ++ exampleName)  $ (cdomIsCdomViolations' p execs idomChef) == [] @? ""
  | (exampleName, p) <- failingCdomIsCdom', let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  []


cdomCdomTests = testGroup "(concerning cdoms)" $
  []

cdomProps = testGroup "(concerning Chops between cdoms and the nodes involved)" [
    testPropertySized 20  "idomIsTreeProgram idomMohrBischof"  $ idomIsTreeProgram idomBischof,
    testPropertySized 10  "chopsCdomArePrefixes idomBischof"   $ chopsCdomArePrefixes idomBischof,
    testPropertySized 10  "chopsCdomAreExclChops idomBischof " $ chopsCdomAreExclChops idomBischof
  ]

balancedParanthesesProps = testGroup "(concerning sccs, as well as general chops and balanced-parantheses-chops)" [
    testProperty  "classification loops in krinkeSCC graphs"      $
      \(INTERCFG(g)) seed ->
                     let  (folded, nodemap) = krinkeSCC g
                          maxlength = 50
                          k         = 1000
                          paths     = samplePathsFor seed k maxlength folded
                     in -- traceShow (length $ nodes g, length $ nodes folded) $
                        (∀) paths (\path ->
                          (∀) (loopsIn path) (\loop -> (sameLevelArbitrary loop) ∨ (not $ realizableArtbitrary loop))
                        ),
    testProperty  "acyclic realizable scc paths for arbitrary graphs"      $
      \(INTER(g)) seed ->
                          let maxlength = 50
                              k         = 1000
                              paths     = sampleRealizablePathsFor seed k maxlength g
                              sccG  = krinkeSCC g
                          in  (∀) (paths) (\path -> not $ hasCycle (αFor g sccG path)),
    testProperty  "acyclic realizable scc paths for cfgs"      $
      \(INTERCFG(g)) seed ->
                          let maxlength = 50
                              k         = 1000
                              paths     = sampleRealizablePathsFor seed k maxlength g
                              sccG  = krinkeSCC g
                          in  (∀) (paths) (\path -> not $ hasCycle (αFor g sccG path))
  ]

balancedParanthesesTests = testGroup "(concerning sccs, as well as general chops and balanced-parantheses-chops)" $
  []

cdomTests = testGroup "(concerning Chops between cdoms and the nodes involved)" $
  [ testCase ("chopsCdomArePrefixes idomBischof for " ++ exampleName)  $ chopsCdomArePrefixes idomBischof p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [ testCase ("chopsCdomAreExclChops idomBischof for " ++ exampleName)  $ chopsCdomAreExclChops idomBischof p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []


miscProps = testGroup "(misc)" [
    testProperty  "snmF4WithReachCheckGfp ⊑ snmF3Gfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let graph     = generatedGraph
                        snmF3Gfp                = NTICD.snmF3 graph
                        snmF4WithReachCheckGfp  = NTICD.snmF4WithReachCheckGfp graph
                    in snmF4WithReachCheckGfp ⊑ snmF3Gfp
  ]

dodProps = testGroup "(concerning decisive order dependence)" [
    testProperty  "dodColoredDag     == dodColoredDagFixed"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.dodColoredDag       g ==
                       NTICD.dodColoredDagFixed  g,
    testProperty  "lfp fMustBefore      == lfp fMust"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.smmnLfp g NTICD.fMustBefore        ==
                       NTICD.smmnLfp g NTICD.fMust,
    -- TODO: select a counter examples, since counter examples arent realiably found within 100 graphs
    -- testProperty  "some myDod-outside-of-imdom-sccs-property"
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
    --                     ),
    testProperty  "rev sinkdom approximates pre-dom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinks = controlSinks g
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
                       ),
    testProperty  "rev sinkdom approximates pre-dom"
    $ \(UNCONNECTED(generatedGraph)) ->
                    let g = delEdges [ e | e@(n,m) <- edges generatedGraph, n == m] generatedGraph
                        sinks = controlSinks g
                        imdom    = NTICD.imdomOfTwoFinger7    $        g
                        imdomrev = NTICD.imdomOfTwoFinger7    $ grev $ g
                        rofldom  = NTICDUnused.rofldomOfTwoFinger7  $        g     
                    in (∀) (nodes g) (\n ->
                         let reachableForward  =  dfs [n] g
                             reachableBackward = rdfs [n] g
                             idom = fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom g n
                             allReachable =
                                Set.fromList reachableForward  == Set.fromList (nodes g)
                              ∧ Set.fromList reachableBackward == Set.fromList (nodes g)
                         in -- (if allReachable then traceShow (allReachable, length $ nodes g) else id) $ 
                            allReachable → (idom ==  NTICD.joiniSinkDomAround g n imdom rofldom)
                       )
  ]
dodTests = testGroup "(concerning decisive order dependence)" $
  [  testCase    ( "dodSlices can be computed by binary control dependence") $
                   let g = mkGraph [(1,()),(4,()),(5,())] [(1,4,()),(4,1,()),(5,1,()),(5,4,())] :: Gr () ()
                       edges = [(n,m,()) | n <- nodes g, m <- nodes g ]
                       cds = [ cd | es <- sublists edges, let cdG = mkGraph (labNodes g) es :: Gr () (), let cd = toSuccMap cdG]
                   in (∃) cds (\cd -> (∀) (fmap Set.fromList $ sublists $ nodes g) (\ms -> NTICD.ntscdMyDodSlice g ms == NTICD.combinedBackwardSlice g cd Map.empty ms)) @? ""
  ] ++
  [  testCase    ( "ntscdDodSlice == ntscdMyDodSlice property strong for " ++ exampleName)
            $       let myDod = NTICD.myDod g
                        ntscd = NTICD.ntscdF3 g
                    in  (∀) (Map.assocs myDod) (\((m1,m2), ns) ->
                          (∀) ns (\n -> n ∈ myDod ! (m2,m1) ∨
                                        (∃) (ns) (\n' -> n' ∈ ntscd ! n)
                          )
                        ) @? ""
  | (exampleName, g) <- [("dodSuperFastCounterExample", dodSuperFastCounterExample :: Gr () () )]
  ] ++
  [  testCase    ( "dodSuperFast              == dodDef for " ++ exampleName)
            $ NTICD.dodSuperFast g            == NTICD.dodDef g @? ""
  | (exampleName, g) <- [("dodSuperFastCounterExample6", dodSuperFastCounterExample6 :: Gr () ())]
  ] ++
  []


wodProps = testGroup "(concerning weak order dependence)" [
    testProperty "nticdMyWodSlice == NTICD.nticdMyWodSliceViaCutAtRepresentatives for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer0  = NTICD.nticdMyWodSlice                        g
                    slicer1  = NTICD.nticdMyWodSliceViaCutAtRepresentatives g
                    slicer2  = NTICD.nticdMyWodSliceViaEscapeNodes          g
                in slicer0  ms == slicer1  ms,
    testProperty "NTICD.nticdMyWodSliceViaCutAtRepresentatives  == nticdMyWodSliceViaEscapeNodes  for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer0  = NTICD.nticdMyWodSlice                        g
                    slicer1  = NTICD.nticdMyWodSliceViaCutAtRepresentatives g
                    slicer2  = NTICD.nticdMyWodSliceViaEscapeNodes          g
                in slicer1  ms == slicer2  ms,
    testProperty "NTICD.nticdMyWodSliceViaEscapeNodes == nticdMyWodSliceViaChoiceAtRepresentatives  for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer0  = NTICD.nticdMyWodSlice                        g
                    slicer1  = NTICD.nticdMyWodSliceViaCutAtRepresentatives g
                    slicer2  = NTICD.nticdMyWodSliceViaEscapeNodes          g
                    slicerNX = NTICD.nticdMyWodSliceViaChoiceAtRepresentatives g
                in slicer2  ms == slicerNX ms,
    testProperty "nticdMyWodSlice == nticdMyWodSliceViaEscapeNodes  for random slice-criteria of random size andCFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
    -- testProperty "nticdMyWodSlice == nticdMyWodSliceViaEscapeNodes  for random slice-criteria of random size"
    -- $ \(ARBITRARY(generatedGraph)) seed1 seed2->
    --             let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer1  = NTICD.nticdMyWodSliceViaNticd       g
                    slicer2  = NTICD.nticdMyWodSliceViaEscapeNodes  g
                    -- slicer1' = NTICD.nticdMyWodSliceViaNticd       g'
                    -- slicer2' = NTICD.nticdMyWodSliceViaEscapeNodes g'
                    ok = slicer1  ms == slicer2  ms
                       -- ∧ slicer1' ms == slicer2' ms
                in (if ok then id else traceShow (g, ms)) ok,
    testProperty "unique node property2 for wodTEIL"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    wodteilslicer = NTICD.wodTEILPDomSlice g
                    property2 s s' g' unique = (∀) s' (\n -> (∀) (suc g n) (\n' ->
                                                 (n' ∈ s) ∨ (unique ! n == unique ! n')
                                               ))
                    uniqueOf s s' g' = Map.fromList [ (n, [ m | m <- reachable n g', m ∈ s]) | n <- Set.toList s' ]

                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                     let ms = Set.fromList [m1,m2]
                         s  = wodteilslicer ms
                         s' = Set.fromList (nodes g) ∖ s
                         g' = efilter ((\(n,m,_) -> n ∈ s')) g
                         unique = uniqueOf s s' g'
                     in property2 s s' g' unique
                   )),
    testProperty  "gfp fMustBefore      == gfp fMust"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.smmnGfp g NTICD.fMustBefore        ==
                       NTICD.smmnGfp g NTICD.fMust,
    testPropertySized 40 "stepsCL mmay'"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (∀) (nodes g) (\m ->
                         NTICD.stepsCL g $ NTICD.mmayOf' g m
                       ),
    testPropertySized 40 "stepsCL mmay"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (∀) (nodes g) (\m ->
                         NTICD.stepsCL g $ NTICD.mmayOf g m
                       ),
    testPropertySized 40 "noJoins mmay"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (∀) (nodes g) (\m ->
                         NTICD.noJoins g $ NTICD.mmayOf g m
                       ),
    testProperty "myWodSlice g' == wodTEILSlice g for CFG-shaped graphs g (with exit->entry edge: g')"
    $ \(SIMPLECFG(g)) ->
                let [entry] = [ n | n <- nodes g, pre g n == [] ]
                    [exit]  = [ n | n <- nodes g, suc g n == [] ]
                    g' = insEdge (exit, entry, ()) g
                    mywodslicer   = NTICD.myWodFastSlice g'
                    wodteilslicer = NTICD.wodTEILSlice   g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> let ms = Set.fromList [m1, m2] in
                      mywodslicer ms == wodteilslicer ms
                   )),
    testProperty  "wodTEIL' ∩ sinks = myWod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mywod    = Map.filter (not . Set.null) $ NTICD.myWodFast g
                        wodTEIL' = Map.filter (not . Set.null) $ NTICD.wodTEIL' g
                        sinks    = controlSinks g
                        sinkNodes = (∐) [ Set.fromList [(m1,m2) | m1 <- sink, m2 <- sink, m1 /= m2] | sink <- sinks ]
                    in restrict wodTEIL' sinkNodes  == mywod,
    testProperty  "wodFast ⊑ myWodFast"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        wod   = NTICD.wodFast g
                        myWod = NTICD.myWodFast g
                    in  wod ⊑ myWod,
                        -- (∀) (Map.assocs wod) (\((m1,m2), ns) ->
                        --   ns ⊑ (myWod ! (m1,m2))
                        -- ),
    testProperty  "myWod is only possible for entries into sccs"
    $ \((CG _ generatedGraph) :: (Connected Gr () ())) ->
                    let g = generatedGraph
                        isinkdom  = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        myWod = NTICD.myWod g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          (∀) ns (\n ->
                              not $
                              (n  ∊ suc isinkdomTrc m1 ∨ n  ∊ suc isinkdomTrc m2)
                          )
                        ),
    testProperty  "myWodFromMay            == myWodFast in arbitrary control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
               let sinks = controlSinks generatedGraph
               in (∀) sinks (\sink ->
                    let g = subgraph sink generatedGraph
                        myWodFromMay = NTICDUnused.myWodFromMay g
                        myWodFast    = NTICD.myWodFast    g
                    in myWodFromMay == myWodFast
               ),
    testProperty  "myWod has no comparable all-max-path-reachable pairs of controlling nodes"
    $ \((CG _ generatedGraph) :: (Connected Gr () ())) ->
                    let g = generatedGraph
                        isinkdom  = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        myWod = NTICD.myWod g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc isinkdomTrc n2 ∨ n2 ∊ suc isinkdomTrc n1) → (n1 == n2)
                          ))
                        )
  ] 



wodTests = testGroup "(concerning weak order dependence)" $
  [  testCase    ( "wodSlices can be computed by binary control dependence") $
                   let g = subgraph [6,7,8,11,13] $ mkGraph [(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,()),(8,()),(9,()),(10,()),(11,()),(12,()),(13,()),(14,())] [(1,2,()),(1,10,()),(2,3,()),(2,6,()),(3,4,()),(3,9,()),(4,12,()),(4,14,()),(5,3,()),(6,7,()),(7,8,()),(7,11,()),(8,6,()),(9,10,()),(11,8,()),(11,13,()),(12,5,()),(13,8,()),(14,5,())] :: Gr () ()
                       edges = [(n,m,()) | n <- nodes g, m <- nodes g ]
                       cds = [ cd | es <- sublists edges, let cdG = mkGraph (labNodes g) es :: Gr () (), let cd = toSuccMap cdG]
                       nticddmywodslicer = NTICD.nticdMyWodSlice g
                       wodslicer         = NTICD.wodTEILSlice g
                       wccslicer         = FCACD.wccSlice g
                   in (∃) cds (\cd -> (∀) (fmap Set.fromList $ sublists $ nodes g) (\ms -> let s = NTICD.combinedBackwardSlice g cd Map.empty ms in s == wodslicer ms ∨ s == nticddmywodslicer ms ∨ s == wccslicer ms)) @? ""
  ] ++
  [  testCase    ( "myCDFromMyDom == myCD for " ++ exampleName) $
                   let  myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                   in  (Set.fromList $ edges myCDFromMyDomTrc) ==  (Set.fromList $ edges myCDTrc) @? ""
  | (exampleName, g) <- myCDvsMyDom
  ] ++
  [  testCase    ( "myCDFromMyDom ⊆ myCD for " ++ exampleName) $
                   let  myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                   in (Set.fromList $ edges myCDFromMyDomTrc) ⊆ (Set.fromList $ edges myCDTrc) @? ""
  | (exampleName, g) <- myCDvsMyDom
  ] ++
  []



testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

