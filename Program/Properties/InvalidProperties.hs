{-# LANGUAGE ScopedTypeVariables #-}
module Program.Properties.InvalidProperties where

import Prelude hiding (all)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)

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

import Data.Ord

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map ( Map, (!) )

import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trcOfTrrIsTrc, withUniqueEndNode, fromSuccMap)
import Data.Graph.Inductive (mkGraph, edges, suc)
import Data.Graph.Inductive.PatriciaTree (Gr)

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
import Program.Generator (toProgram, GeneratedProgram)

import Data.Graph.Inductive.Arbitrary

import Data.Graph.Inductive.Query.ControlDependence (controlDependenceGraphP, controlDependence)
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    myWod, isinkdomOfSinkContraction, myDod,
    dodDef, dodSuperFast, wodDef,
    nticdF5,                         ntscdFig4,       ntscdF3, nticdF5, nticdFig5, nticdIndus, nticdF3,
    nticdF5GraphP, nticdIndusGraphP, ntscdFig4GraphP,  ntscdF3GraphP, nticdF5GraphP, nticdFig5GraphP,
    snmF3, snmF5
  ) 


main      = all

all        = defaultMain                               $ expectFail $ tests
allX       = defaultMainWithIngredients [antXMLRunner] $ expectFail $ tests
cdom       = defaultMain                               $ expectFail $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
cdomX      = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "cdom"      [ mkTest [cdomTests, cdomCdomTests], mkProp [cdomProps, cdomCdomProps]]
balanced   = defaultMain                               $ expectFail $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
balancedX  = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "balanced"  [ mkTest [balancedParanthesesTests], mkProp [balancedParanthesesProps]]
timing     = defaultMain                               $ expectFail $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
timingX    = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "timing"    [ mkTest [timingClassificationDomPathsTests,precisionCounterExampleTests], mkProp [timingClassificationDomPathsProps] ]
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


misc       = defaultMain                               $ expectFail $ testGroup "misc"      [ mkProp [miscProps] ]
miscX      = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "misc"      [ mkProp [miscProps] ]
dod        = defaultMain                               $ expectFail $ testGroup "dod"       [ mkTest [dodTests]]
dodX       = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "dod"       [ mkTest [dodTests]]
wod        = defaultMain                               $ expectFail $ testGroup "wod"       [ mkProp [wodProps]]
wodX       = defaultMainWithIngredients [antXMLRunner] $ expectFail $ testGroup "wod"       [ mkProp [wodProps]]

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"


tests :: TestTree
tests = testGroup "Tests" [unitTests, properties]


properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps, cdomProps, cdomCdomProps, balancedParanthesesProps, soundnessProps ]

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests, cdomTests, cdomCdomTests, balancedParanthesesTests, soundnessTests, precisionCounterExampleTests ]


soundnessProps =  localOption d $ testGroup "(concerning soundness)" [
    testPropertySized 3
     ("allSound [ unsoundIRLSODAttempt  ] ")
     ( allSound [ unsoundIRLSODAttempt  ] )
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


cdomCdomProps = testGroup "(concerning cdoms)" $
  [ testCase ("cdomIsCdom' idomChef for " ++ exampleName)  $ (cdomIsCdomViolations' p execs idomChef) == [] @? ""
  | (exampleName, p) <- failingCdomIsCdom', let execs = fmap fst $ unsafePerformIO $ evalRandIO $ someFinishedAnnotatedExecutionTraces 100 p defaultInput
  ] ++
  []


cdomCdomTests = testGroup "(concerning cdoms)" $
  []

cdomProps = testGroup "(concerning Chops between cdoms and the nodes involved)" [
  ]

balancedParanthesesProps = testGroup "(concerning sccs, as well as general chops and balanced-parantheses-chops)" [
  ]

balancedParanthesesTests = testGroup "(concerning sccs, as well as general chops and balanced-parantheses-chops)" $
  []

cdomTests = testGroup "(concerning Chops between cdoms and the nodes involved)" $
  []


miscProps = testGroup "(misc)" [
  ]

dodTests = testGroup "(concerning decisive order dependence)" $
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
    testProperty  "myWod is only possible for entries into sccs"
    $ \((CG _ generatedGraph) :: (Connected Gr () ())) ->
                    let g = generatedGraph
                        isinkdom  = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        myWod = NTICD.myWod g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          (∀) ns (\n ->
                              not $
                              (n  ∈ suc isinkdomTrc m1 ∨ n  ∈ suc isinkdomTrc m2)
                          )
                        ),
    testProperty  "myWod has no comparable all-max-path-reachable pairs of controlling nodes"
    $ \((CG _ generatedGraph) :: (Connected Gr () ())) ->
                    let g = generatedGraph
                        isinkdom  = NTICD.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        myWod = NTICD.myWod g
                    in  (∀) (Map.assocs myWod) (\((m1,m2), ns) ->
                          (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∈ suc isinkdomTrc n2 ∨ n2 ∈ suc isinkdomTrc n1) → (n1 == n2)
                          ))
                        )
  ] 




testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

