{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

-- #define USECONNECTED
#ifdef USECONNECTED
#define ARBITRARY(g) (CG _ g) :: (Connected Gr () ())
#else
#define ARBITRARY(g) (g) :: (Gr () ())
#endif

#define UNCONNECTED(g) (g) :: (Gr () ())

module Program.Properties.DissObservations where

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
import Data.Graph.Inductive (mkGraph, nodes, edges,  suc, pre, Node, labNodes, subgraph, reachable)
import Data.Graph.Inductive.PatriciaTree (Gr)

-- import qualified Data.Graph.Inductive.Query.LCA as LCA (lca)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (sinkdomOfGfp, mdomOfLfp,  mdomsOf, sinkdomsOf, onedomOf, isinkdomOfTwoFinger8, imdomOfTwoFinger6)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (
    sinkDF,    mDFFromUpLocalDefViaMdoms,       mDFLocalDef,     mDFLocalViaMdoms,       mDFUpGivenXViaMdoms,        mDFUpDef,     mDFTwoFinger,
    mDF,    sinkDFFromUpLocalDefViaSinkdoms, sinkDFLocalDef,  sinkDFLocalViaSinkdoms, sinkDFUpGivenXViaSinkdoms,  sinkDFUpDef, isinkDFTwoFinger,
    noJoins, stepsCL,
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


testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop

main      = props

props      = defaultMain                               $ properties
propsX     = defaultMainWithIngredients [antXMLRunner] $ properties

mdom       = defaultMain                               $ testGroup "pdom"      [ mkProp [mdomProps]]
mdomX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "pdom"      [ mkProp [mdomProps]]

sdom       = defaultMain                               $ testGroup "pdom"      [ mkProp [sdomProps]]
sdomX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "pdom"      [ mkProp [sdomProps]]


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
properties = testGroup "Properties" [ mdomProps, sdomProps, pdfProps, ntsodProps, ntiodProps]


mdomProps = testGroup "(concerning nontermination   sensitive postdominance)" (lemma_5_2_1 ++ observation_5_2_1 ++ observation_5_2_2 ++ lemma_5_2_2       ++ lemma_5_2_3                            ++ observation_5_2_3)
sdomProps = testGroup "(concerning nontermination insensitive postdominance)" (lemma_5_3_1 ++ observation_5_3_1 ++ observation_5_3_2 ++ observation_5_3_3 ++ observation_5_3_4 ++ observation_5_3_6 ++ observation_5_3_7)


lemma_5_2_1 = [
    testProperty "mdom    is reflexive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            mdom = PDOM.mdomOfLfp g
        in (∀) (nodes g) (\n -> n ∈ mdom ! n),
    testProperty "mdom    is transitive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            mdom = PDOM.mdomOfLfp g
        in (∀) (Map.assocs $ mdom)    (\(x, ys) -> (∀) ys (\y -> (∀) (mdom ! y)     (\z -> z ∈ mdom ! x  )))
  ]
observation_5_2_1 = [
    testProperty "mdom    has transitive reduction that forms a pseudo forest"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            mdom = PDOM.mdomOfLfp g
            redu = (trr $ fromSuccMap $ mdom :: Gr () ())
            clos = toSuccMap $ trc redu
        in (mdom    == clos) ∧ (∀) (Map.assocs $ toSuccMap $ redu) (\(n, ms) -> Set.size ms <= 1)
  ]

observation_5_2_2 = [
    testProperty "ipdom_max transitive closure is mdom"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            mdom = PDOM.mdomOfLfp g
            onedomOf = PDOM.onedomOf mdom
            redu = (trr $ fromSuccMap $ mdom :: Gr () ())
            clos = toSuccMap $ trc redu
            
            mdoms = PDOM.mdomsOf g
            closMdoms = toSuccMap $ trc $ (fromSuccMap $ mdoms :: Gr () ())
        in   True
           ∧ ( (∀) (nodes g) (\x -> onedomOf x == Set.fromList [ z | z <- dfs (suc redu x) redu ]) )
           ∧ ( mdoms == Map.fromList [ (z, Set.fromList [ x | x' <- suc redu z, x <- Set.toList $ mdom ! x', x' ∈ mdom ! x ])  | z <- nodes g] )
           ∧ ( closMdoms == mdom )
  ]
  
lemma_5_2_2 = [  
    testPropertySized 40 "noJoins mdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                    in PDF.noJoins g mdom
  ]

lemma_5_2_3 = [ 
    testPropertySized 40 "stepsCL mdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                    in PDF.stepsCL g mdom
  ]

observation_5_2_3 = [
    testProperty "imdomOfTwoFinger6^* == mdomOfLfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (toSuccMap $ trc $ (fromSuccMap $ PDOM.imdomOfTwoFinger6 g :: Gr () ())) == PDOM.mdomOfLfp g
   
  ]


lemma_5_3_1 = [
    testProperty "sinkdom is reflexive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfGfp g
        in (∀) (nodes g) (\n -> n ∈ sinkdom ! n),
    testProperty "sinkdom    is transitive"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfGfp g
        in (∀) (Map.assocs $ sinkdom) (\(x, ys) -> (∀) ys (\y -> (∀) (sinkdom ! y) (\z -> z ∈ sinkdom ! x)))
  ]

observation_5_3_1 = [
    testProperty "sinkdom has transitive reduction that forms a pseudo forest"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfGfp g
            redu = (trr $ fromSuccMap $ sinkdom :: Gr () ())
            clos = toSuccMap $ trc redu
        in (sinkdom == clos) ∧ (∀) (Map.assocs $ toSuccMap $ redu) (\(n, ms) -> Set.size ms <= 1)
  ]

observation_5_3_2 = [
    testProperty "ipdom_sink transitive closure is sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            sinkdom = PDOM.sinkdomOfGfp g
            onedomOf = PDOM.onedomOf sinkdom
            redu = (trr $ fromSuccMap $ sinkdom :: Gr () ())
            
            sinkdoms = PDOM.sinkdomsOf g
            closSinkdoms = toSuccMap $ trc $ (fromSuccMap $ sinkdoms :: Gr () ())
        in   True
           ∧ ( (∀) (nodes g) (\x -> onedomOf x == Set.fromList [ z | z <- dfs (suc redu x) redu ]) )
           ∧ ( sinkdoms == Map.fromList [ (z, Set.fromList [ x | x' <- suc redu z, x <- Set.toList $ sinkdom ! x', x' ∈ sinkdom ! x ])  | z <- nodes g] )
           ∧ ( closSinkdoms == sinkdom )
  ]


observation_5_3_3 = [  
    testPropertySized 40 "noJoins sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in PDF.noJoins g sinkdom
  ]

observation_5_3_4 = [ 
    testPropertySized 40 "stepsCL sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in PDF.stepsCL g sinkdom
  ]

observation_5_3_6 = [
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


observation_5_3_7 = [
    testProperty "isinkdomOfTwoFinger8^* == sinkdomOfGfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (toSuccMap $ trc $ (fromSuccMap $ PDOM.isinkdomOfTwoFinger8 g :: Gr () ())) == PDOM.sinkdomOfGfp g
   
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
observation1topsort = [
    testProperty   "topsort sinkdom approximation"
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
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∈ mdom ! m2 ∧ m2 ∈ mdom ! m1))
                        ∧ (∀) ns (\n -> (not $ n ∈ mdom ! m1) ∧ (not $ n ∈ mdom ! m2))
                        ∧ (∀) ns (\n -> (∀) (mdom ! n) (\m -> (m /= n) → (
                            (m ∈ mdom ! m1) ∧ (m ∈ mdom ! m2) ∧ (m1 ∈ mdom ! m) ∧ (m2 ∈ mdom ! m)
                          )))
                        )
  ]
observation4 = [
      testPropertySized 60  "ntsod reduction to ntscd"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = PDOM.imdomOfTwoFinger6 g
                        (cycleOf,cycles) = findCyclesM (fmap fromSet imdom)
                        ntsod = ODEP.ntsod g
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
      testProperty  "ntsodFastPDom               ≡ ntsod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntsodFastPDom   g ≡
                       ODEP.ntsod           g
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
    testPropertySized 60 "nticdNTIODSlice == nticdNTIODSliceViaNticd == nticdNTIODSliceViaISinkDom ==  for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer0  = SLICE.ODEP.nticdNTIODSlice               g
                    slicer1  = SLICE.NTICD.nticdNTIODSlice              g
                    slicer2  = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g
                in   slicer0 ms == slicer1 ms
                   ∧ slicer1 ms == slicer2 ms
  ]
observation10 = [
    testPropertySized 60  "nticdNTIODSlice == nticdNTIODSliceViaNticd even when using data dependencies"
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
                    slicer = combinedBackwardSlice (ddep ⊔ nticd) ntiod

                    g' = foldr (flip delSuccessorEdges) g ms
                    nticd' = PDF.isinkDFTwoFinger g'
                    empty = Map.empty
                    slicer' = combinedBackwardSlice (ddep ⊔ nticd') empty
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
                       nticdntiodslicer  = SLICE.ODEP.nticdNTIODSlice g
                       wodslicer         = SLICE.ODEP.wodTEILSlice g
                       wccslicer         = FCACD.wccSlice g
                   in (not $ (∃) cds (\cd -> (∀) (fmap Set.fromList $ sublists $ nodes g) (\ms ->
                        let s = combinedBackwardSlice cd Map.empty ms in s == wodslicer ms ∨ s == nticdntiodslicer ms ∨ s == wccslicer ms
                      ))) @? ""
  ]
