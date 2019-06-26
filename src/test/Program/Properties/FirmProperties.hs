{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

-- #define USECONNECTED
#ifdef USECONNECTED
#define ARBITRARY(g) (CG _ g) :: (Connected Gr () ())
#else
#define ARBITRARY(g) (g) :: (Gr () ())
#endif

#define UNCONNECTED(g) (g) :: (Gr () ())

module Program.Properties.FirmProperties where

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

import Data.Graph.Inductive.Query.DFS (dfs, rdfs, rdff)
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trr, fromSuccMap, toSuccMap, controlSinks, delSuccessorEdges, delPredecessorEdges, withUniqueEndNode)
import Data.Graph.Inductive (mkGraph, nodes, edges,  suc, Node, labNodes, subgraph, reachable, insEdge, lpre)
import Data.Graph.Inductive.PatriciaTree (Gr)

-- import qualified Data.Graph.Inductive.Query.LCA as LCA (lca)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (sinkdomOfGfp, mdomOfLfp,  mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, imdomOfTwoFinger6)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (
    sinkDF,    mDFFromUpLocalDefViaMdoms,       mDFLocalDef,     mDFLocalViaMdoms,       mDFUpGivenXViaMdoms,        mDFUpDef,     mDFTwoFinger,
    mDF,    sinkDFFromUpLocalDefViaSinkdoms, sinkDFLocalDef,  sinkDFLocalViaSinkdoms, sinkDFUpGivenXViaSinkdoms,  sinkDFUpDef, isinkDFTwoFinger,
    --  noJoins, stepsCL,
 )
import qualified Data.Graph.Inductive.Query.FCACD as FCACD (wccSlice)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import qualified Data.Graph.Inductive.Query.Slices.PostDominance as SLICE.PDOM (
    wodTEILSliceViaISinkDom, wccSliceViaISinkDom, nticdNTIODSliceViaISinkDom,
  )
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (
    wodTEILSliceViaNticd,    wccSliceViaNticd,    nticdNTIODSlice
  )
import qualified Data.Graph.Inductive.Query.Slices.OrderDependence as SLICE.ODEP (
    nticdNTIODSlice, wodTEILSlice,
  )
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    nticdViaSinkDom, ntscdViaMDom,
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
    dod, dodDef,
    ntsod, ntsodFastPDom,
    ntiod, ntiodFastPDom, ntiodFastPDomSimpleHeuristic, 
  )

import Data.Graph.Inductive.Arbitrary


import Program.Examples

testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

main      = props

props      = defaultMain                               $ properties
propsX     = defaultMainWithIngredients [antXMLRunner] $ properties

tests      = defaultMain                               $ unitTests

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ ]

properties :: TestTree
properties = testGroup "Properties" [ mkProp $ observation6 ++ observation8]

firmExchange = [
      testPropertySized 60  "ipdom recomputation after 'exchange'"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                        isinkdom = PDOM.isinkdomOfTwoFinger8 g
                    in True
 ]

observation6 = [
      testPropertySized 60  "ntiod reduction to nticd"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom = PDOM.isinkdomOfTwoFinger8 g
                        (cycleOf,cycles) = findCyclesM (fmap fromSet isinkdom)
                        ntiod = ODEP.ntiod g
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
                           let nticd' = NTICD.nticdViaSinkDom (delSuccessorEdges (gNOfNode ! m2) m2) in
                           (∀) ns (\n -> (∃) cycles (\bigM -> m1 ∈ bigM ∧ m2 ∈ bigM ∧ (∃) (isinkdom ! n) (\m -> m ∈ bigM) ∧ m1 /= n ∧ m1 ∈ nticd' ! n))
                         )
                       ∧ (∀) (cycles) (\bigM -> let gN = gNOfNode ! (Set.findMin bigM) in
                           (∀) bigM (\m2 -> let nticd' = NTICD.nticdViaSinkDom (delSuccessorEdges gN m2) in
                             (∀) (Map.assocs nticd') (\(n,ms) -> (∀) ms (\m1 -> (m1 ∈ bigM ∧ m1 /= n) → (n ∈ ntiod ! (m1, m2))))
                           )
                         ),
      testPropertySized 60  "ntiodFastPDom               ≡ ntiod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntiodFastPDom   g ≡
                       ODEP.ntiod           g
  ]
observation8 = [
      testPropertySized 60  "ntiodFastPDom               ≡ ntiod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntiodFastPDomSimpleHeuristic   g ≡
                       ODEP.ntiod                          g
  ]
