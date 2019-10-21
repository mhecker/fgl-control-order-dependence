{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Cdom where


import Debug.Trace (traceShow, trace)
import Control.Exception.Base (assert)
import Control.Monad.Random (randomR, getStdRandom)

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map, (!))


import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Runners.AntXML

import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, lsuc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph, delEdges, insEdge, newNodes)
import Data.Graph.Inductive.PatriciaTree (Gr)

import Unicode
import Util(sampleFrom, invert'', moreSeeds)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, code2ResumptionForProgram, code2Program)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)

import Program.Properties.CDom
import Execution (allFinishedExecutionTraces, someFinishedAnnotatedExecutionTraces)
import Program.CDom

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
