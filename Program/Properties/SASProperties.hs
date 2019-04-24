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
import Data.Graph.Inductive.Util (trr, fromSuccMap, toSuccMap, controlSinks, delSuccessorEdges)
import Data.Graph.Inductive (mkGraph, nodes, edges,  suc, Node, labNodes, subgraph, reachable)
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
    wodTEILSliceViaISinkDom, wccSliceViaISinkDom, nticdMyWodSliceViaISinkDom,
  )
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (
    wodTEILSliceViaNticd,    wccSliceViaNticd,    nticdMyWodSlice
  )
import qualified Data.Graph.Inductive.Query.Slices.OrderDependence as SLICE.ODEP (
    nticdMyWodSlice, wodTEILSlice,
  )
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    nticdViaSinkDom, ntscdViaMDom,
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
    dod, dodDef,
    myDod, myDodFastPDom,
    ntiod, ntiodFastPDom, ntiodFastPDomSimpleHeuristic, 
  )

import Data.Graph.Inductive.Arbitrary


testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

main      = props

props      = defaultMain                               $ properties
propsX     = defaultMainWithIngredients [antXMLRunner] $ properties

pdom       = defaultMain                               $ testGroup "pdom"      [ mkProp [pdomProps]]
pdomX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "pdom"      [ mkProp [pdomProps]]

pdf        = defaultMain                               $ testGroup "pdf"       [ mkProp [pdfProps]]
pdfX       = defaultMainWithIngredients [antXMLRunner] $ testGroup "pdf"       [ mkProp [pdfProps]]


ntsod      = defaultMain                               $ testGroup "ntsod"     [ mkProp [ntsodProps]]
ntsodX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "ntsod"     [ mkProp [ntsodProps]]

ntiod      = defaultMain                               $ testGroup "ntiod"     [ mkProp [ntiodProps]]
ntiodX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "ntiod"     [ mkProp [ntiodProps]]

tests      = defaultMain                               $ unitTests

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [                                  ntiodTests]

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
            sinkdom = PDOM.sinkdomOfGfp g
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
            sinkdom = PDOM.sinkdomOfGfp g
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
            sinkdom = PDOM.sinkdomOfGfp g
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
    testPropertySized 60 "mDFFromUpLocalDefViaSinkdoms == mDF"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFFromUpLocalDefViaMdoms g ==
                       PDF.mDF                       g,
    testPropertySized 60 "sinkDFFromUpLocalDefViaSinkdoms == sinkDF"
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
                        ntscd   = NTICD.ntscdViaMDom g
                    in   (∀) (Map.assocs ntscd)   (\(n, ms) -> (∀) ms (\m -> (n /= m) → (n ∈ imDF ! m)))
                       ∧ (∀) (Map.assocs imDF) (\(m, ns) -> (∀) ns (\n -> (n /= m) → (m ∈ ntscd ! n))),
   testProperty   "isinkDFTwoFinger == nticd"
                $ \(ARBITRARY(g)) ->
                    let isinkDF = PDF.isinkDFTwoFinger g
                        sinkdom = PDOM.sinkdomOfGfp g
                        nticd   = NTICD.nticdViaSinkDom g
                    in   (∀) (Map.assocs nticd)   (\(n, ms) -> (∀) ms (\m -> (n /= m) → (n ∈ isinkDF ! m)))
                       ∧ (∀) (Map.assocs isinkDF) (\(m, ns) -> (∀) ns (\n -> (n /= m) → (m ∈ nticd ! n)))
  ]


pdfTests = testGroup "(concerning generalized postdominance frontiers)" $
  []


ntsodProps = testGroup "(concerning nontermination   sensititve order dependence)" (dodIsDodDef ++ lemma4 ++ observation3 ++ observation4)
dodIsDodDef = [
    testPropertySized 40  "dod  == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dod           g ==
                       ODEP.dodDef        g
  ]
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
                           let ntscd' = NTICD.ntscdViaMDom (delSuccessorEdges (gNOfNode ! m2) m2) in
                           (∀) ns (\n -> (∃) cycles (\bigM -> m1 ∈ bigM ∧ m2 ∈ bigM ∧ (∃) (imdom ! n) (\m -> m ∈ bigM) ∧ m1 ∈ ntscd' ! n))
                         )
                       ∧ (∀) (cycles) (\bigM -> let gN = gNOfNode ! (Set.findMin bigM) in
                           (∀) bigM (\m2 -> let ntscd' = NTICD.ntscdViaMDom (delSuccessorEdges gN m2) in
                             (∀) (Map.assocs ntscd') (\(n,ms) -> (∀) ms (\m1 -> (m1 ∈ bigM) → (n ∈ ntsod ! (m1, m2))))
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
                        sinkdom  = PDOM.sinkdomOfGfp g
                        ntiod = ODEP.ntiod g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∈ sinkdom ! m2 ∧ m2 ∈ sinkdom ! m1))
                        ∧ (∀) ns (\n -> (∀) (sinkdom ! n) (\m -> (m /= n) → (
                            (m ∈ sinkdom ! m1) ∧ (m ∈ sinkdom ! m2) ∧ (m1 ∈ sinkdom ! m) ∧ (m2 ∈ sinkdom ! m)
                          )))
                        )
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
theorem5 = [
    testPropertySized 60 "nticdMyWodSlice == nticdMyWodSliceViaNticd == nticdMyWodSliceViaISinkDom ==  for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer0  = SLICE.ODEP.nticdMyWodSlice               g
                    slicer1  = SLICE.NTICD.nticdMyWodSlice              g
                    slicer2  = SLICE.PDOM.nticdMyWodSliceViaISinkDom    g
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
                    ntiod =  ODEP.ntiodFastPDomSimpleHeuristic g
                    slicer = combinedBackwardSlice g (ddep ⊔ nticd) ntiod

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
                    slicer1 = SLICE.PDOM.wccSliceViaISinkDom     g
                    slicer2 = SLICE.NTICD.wccSliceViaNticd g
                in   slicer0 ms == slicer1 ms
                   ∧ slicer1 ms == slicer2 ms,
    testPropertySized 40 "wodTEILSliceViaISinkDom = wodTEILSliceViaNticd == wodTEILSlice for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer0  = SLICE.ODEP.wodTEILSlice               g
                    slicer1  = SLICE.PDOM.wodTEILSliceViaISinkDom    g
                    slicer2  = SLICE.NTICD.wodTEILSliceViaNticd      g
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
                       nticdntiodslicer  = SLICE.ODEP.nticdMyWodSlice g
                       wodslicer         = SLICE.ODEP.wodTEILSlice g
                       wccslicer         = FCACD.wccSlice g
                   in (not $ (∃) cds (\cd -> (∀) (fmap Set.fromList $ sublists $ nodes g) (\ms ->
                        let s = combinedBackwardSlice g cd Map.empty ms in s == wodslicer ms ∨ s == nticdntiodslicer ms ∨ s == wccslicer ms
                      ))) @? ""
  ]
