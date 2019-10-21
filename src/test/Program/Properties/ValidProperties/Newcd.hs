{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Newcd where


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
import Data.Graph.Inductive.Arbitrary
import Data.Graph.Inductive.Query.TransClos (trc)

import Unicode
import Util(sampleFrom, invert'', moreSeeds, restrict)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)



import qualified Data.Graph.Inductive.Query.NTICD.Program as PROG (ntacdDefGraphP, nticdF3GraphP)
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (nticdF3)
import qualified Data.Graph.Inductive.Query.NTICDUnused  as NTICDUnused (ntacdDef)

newcd      = defaultMain                               $ testGroup "newcd"     [ mkTest [newcdTests], mkProp [newcdProps]]
newcdX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "newcd"     [ mkTest [newcdTests], mkProp [newcdProps]]


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

