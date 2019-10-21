{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Color where

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
import Util(sampleFrom, invert'', moreSeeds)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)


import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (isinkdomOf, isinkdomOfGfp2, joinUpperBound, sinkdomOfJoinUpperBound, sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkdomNaiveGfp, sinkdomNaiveGfpFullTop, sinkdomOfisinkdomProperty, imdomOf, imdomOfLfp, mdomOf, mdomOfLfp, mdomNaiveLfp, mdomOfimdomProperty, onedomOf, mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, isinkdomOftwoFinger8Up,  imdomOfTwoFinger6, imdomOfTwoFinger7)
import qualified Data.Graph.Inductive.Query.PostDominance.GraphTransformations as PDOM.TRANS (isinkdomOfSinkContraction)
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
     mustOfLfp, mustOfGfp, mmayOf, mmayOf', rotatePDomAround, Color(..), smmnFMustDod, smmnFMustWod, colorLfpFor, colorFor,
    smmnGfp, smmnLfp, fMust, fMustBefore, fMustNoReachCheck,
    dod, dodDef, dodFast, dodColoredDagFixed, dodColoredDagFixedFast,
    ntiod, ntiodFast, ntiodFastPDom, ntiodFastPDomSimpleHeuristic,  ntsod, ntsodFast, ntsodFastPDom, wodTEIL', wodTEIL'PDom, wodDef, wodFast, fMay, fMay'
  )

color      = defaultMain                               $ testGroup "color"     [ mkTest [colorTests], mkProp [colorProps]]
colorX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "color"     [ mkTest [colorTests], mkProp [colorProps]]

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
