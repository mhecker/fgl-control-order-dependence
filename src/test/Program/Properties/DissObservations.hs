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

import Util(invert'', (≡), findCyclesM, fromSet, sublists, moreSeeds, roots, restrict, sampleFrom)
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

import Data.Graph.Inductive.Query.DFS (dfs, rdfs, rdff, condensation)
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trr, fromSuccMap, toSuccMap, controlSinks, delSuccessorEdges, removeDuplicateEdges)
import Data.Graph.Inductive (mkGraph, nodes, edges,  suc, pre, Node, labNodes, subgraph, reachable, newNodes, efilter)
import Data.Graph.Inductive.PatriciaTree (Gr)

-- import qualified Data.Graph.Inductive.Query.LCA as LCA (lca)
import Data.Graph.Inductive.Query.Util.GraphTransformations (sinkShrinkedGraph)
import qualified Data.Graph.Inductive.Query.PostDominance.GraphTransformations as PDOM.TRANS (isinkdomOfSinkContraction)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (sinkdomOfGfp, mdomOfLfp,  mdomsOf, sinkdomsOf, onedomOf, isinkdomOfTwoFinger8, imdomOfTwoFinger6)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (
    sinkDF,    mDFFromUpLocalDefViaMdoms,       mDFLocalDef,     mDFLocalViaMdoms,       mDFUpGivenXViaMdoms,        mDFUpDef,     mDFTwoFinger,
    mDF,    sinkDFFromUpLocalDefViaSinkdoms, sinkDFLocalDef,  sinkDFLocalViaSinkdoms, sinkDFUpGivenXViaSinkdoms,  sinkDFUpDef, isinkDFTwoFinger,
    noJoins, stepsCL,
 )
import qualified Data.Graph.Inductive.Query.FCACD as FCACD (wccSlice)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import qualified Data.Graph.Inductive.Query.Slices.PostDominance as SLICE.PDOM (
    ntscdNTSODSliceViaIMDom,
    wodTEILSliceViaISinkDom, wccSliceViaISinkDom, nticdNTIODSliceViaISinkDom,
  )
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (
    ntscdNTSODSliceViaNtscd,
    wodTEILSliceViaNticd,    wccSliceViaNticd,    nticdNTIODSlice, nticdSlice, ntscdSlice
  )
import qualified Data.Graph.Inductive.Query.Slices.OrderDependence as SLICE.ODEP (
    ntscdNTSODSlice, 
    nticdNTIODSlice, wodTEILSlice,
  )
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    nticdViaSinkDom, ntscdViaMDom,
    ntindDef, ntsndDef,
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
    dod, dodDef,
    mustOfLfp, mustOfGfp,
    wodTEIL', wodTEIL'PDom,
    dodColoredDagFixed, dodColoredDagFixedFast,
    ntsod, ntsodFastPDom,
    ntiod, ntiodFastPDom, ntiodFastPDomSimpleHeuristic, ntiodFast,
  )

import qualified Data.Graph.Inductive.Query.Slices.OrderDependence as SLICE.ODEP (
    ntscdNTSODFastPDomSlice, 
  )

import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay ( Input(..), allChoices, runInput, observable, infinitelyDelays, isLowEquivalentFor)

import qualified Data.Graph.Inductive.Query.NextObservable as Next (retainsNextObservableOutside, weaklyControlClosed)

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
unitTests  = testGroup "Unit tests" [                                 ntsodTests, ntiodTests]

properties :: TestTree
properties = testGroup "Properties" [ mdomProps, sdomProps, pdfProps, ntsodProps, ntiodProps]


mdomProps = testGroup "(concerning nontermination   sensitive postdominance)" (
    lemma_5_2_1 ++ observation_5_2_1 ++ observation_5_2_2 ++ lemma_5_2_2       ++ lemma_5_2_3                                                 ++ observation_5_2_3
  )
sdomProps = testGroup "(concerning nontermination insensitive postdominance)" (
    lemma_5_3_1 ++ observation_5_3_1 ++ observation_5_3_2 ++ observation_5_3_3 ++ observation_5_3_4 ++ observation_5_3_5 ++ observation_5_3_6 ++ observation_5_3_7 ++ observation_5_4_1 ++ observation_5_4_2
  )


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


observation_5_3_5 = [
    testProperty   "sinks vs roots"
    $ \(ARBITRARY(generatedGraph)) ->
        let g = generatedGraph
            isinkdom = PDOM.isinkdomOfTwoFinger8 g
            isinkdomRoots = Set.fromList $ fmap Set.fromList $ roots isinkdom

            sinks         = Set.fromList $ fmap Set.fromList $ controlSinks g

            -- sinkNodes = Set.fromList [ s | sink <- sinks, s <- sink]
        in   Set.filter (\s -> Set.size s >  1) sinks == Set.filter (\r -> Set.size r  > 1) isinkdomRoots
           ∧ Set.filter (\s -> Set.size s == 1) sinks ⊆  Set.filter (\r -> Set.size r == 1) isinkdomRoots
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




observation_5_4_1 = [
    testProperty "reduction to postdominance trees"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g  = generatedGraph
                        [endNode] = newNodes 1 g
                        
                        gs = sinkShrinkedGraph g endNode

                        sinks     = controlSinks g
                        sinkNodes = Set.fromList [ s | sink <- sinks, s <- sink]
    
                        sinkdom   = PDOM.sinkdomOfGfp g
                        sinkdomGs = PDOM.sinkdomOfGfp gs

                        n = Set.fromList $ nodes g
                        siNodes = Set.fromList (nodes gs) ∖ (Set.insert endNode $ Set.fromList $ nodes g)
                        
                    in (∀) (n ∖ sinkNodes) (\x -> (∀) (n ∖ sinkNodes)    (\m -> (m ∈ sinkdom ! x)  ==  (m ∈ sinkdomGs ! x)))
                     ∧ (∀) (n ∖ sinkNodes) (\x -> (∀) sinks (\s -> (∀) s (\m -> (m ∈ sinkdom ! x)  ==  (x `elem` s   ∨  (head s) ∈ sinkdomGs ! x))))
  ]


observation_5_4_2 = [
    testProperty "reduction to postdominance trees: algorithm"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (toSuccMap $ trc $ (fromSuccMap $ PDOM.TRANS.isinkdomOfSinkContraction g :: Gr () ())) == PDOM.sinkdomOfGfp g
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


ntsodProps = testGroup "(concerning nontermination   sensititve order dependence)" (dodIsDodDef ++ lemma_6_1_2 ++ observation_6_1_1 ++ observation_6_2_1 ++ observation_6_2_2 ++ observation_6_2_3 ++ observation_6_2_4 ++ observation_6_2_5 ++ observation_6_3_1 ++ observation_6_3_2 ++ observation_7_2_1 ++ observation_7_2_2 ++ observation_7_2_3 ++ lemma_7_2_1 ++ observation_7_2_4)

dodIsDodDef = [
    testPropertySized 40  "dod  == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dod           g ==
                       ODEP.dodDef        g,
    testPropertySized 40  "dod  == dodColoredDagFixedFast"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dod           g ==
                       ODEP.dodColoredDagFixedFast        g
  ]

lemma_6_1_2 = [
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

observation_6_1_1 = [
    testProperty  "dodColoredDagFixedFast  == dodColoredDagFixed"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodColoredDagFixedFast g ==
                       ODEP.dodColoredDagFixed     g
  ]

observation_6_2_1 = [
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
                        )
  ]


observation_6_2_2 = [
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
                        )
  ]

  
observation_6_2_3 = [
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


observation_6_2_4 = [
      testProperty  "mdomOfLfp m2  == mustOfLfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfLfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               mdom2 = PDOM.mdomOfLfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ mdom2 ! n)
                           ))
                       )
  ]


observation_6_2_5 = [
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


observation_6_3_1 = [
    testPropertySized 25 "ntscdNTSODFastPDomSlice is sound"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = removeDuplicateEdges generatedGraph
                        n = length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes

                        ms
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        
                        s = SLICE.ODEP.ntscdNTSODFastPDomSlice g ms
                        runInput   = InfiniteDelay.runInput g
                        observable   = InfiniteDelay.observable s
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                     in (if not $ different then id else traceShow (s, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in not differentobservation
  ]


observation_6_3_2 = [
    testPropertySized 25 "ntscdNTSODFastPDomSlice is minimal"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = removeDuplicateEdges generatedGraph
                        n = length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes

                        ms
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        
                        s = SLICE.ODEP.ntscdNTSODFastPDomSlice g ms
                        runInput   = InfiniteDelay.runInput g

                    in (∀) s (\n -> n ∈ ms ∨
                         let s' = Set.delete n s
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                    in different
                                  )
                               ))
                         in differentobservation
                       )
  ]



ntsodTests = testGroup "(concerning nontermination   sensititve order dependence)" (observation_6_3_3)

observation_6_3_3 = [
        testCase ("nontermination sensitive slices cannot in general be computed by binary control dependence") $
                   let g = mkGraph [(0,()),(1,()),(2,())] [(0,1,()),(0,2,()),(2,1,()),(1,2,())] :: Gr () ()
                       edges = [(n,m,()) | n <- nodes g, m <- nodes g ]
                       cds = [ cd | es <- sublists edges, let cdG = mkGraph (labNodes g) es :: Gr () (), let cd = toSuccMap cdG]
                       slicer  = SLICE.ODEP.ntscdNTSODFastPDomSlice g
                   in (not $ (∃) cds (\cd -> (∀) (fmap Set.fromList $ sublists $ nodes g) (\ms ->
                        let s = combinedBackwardSlice cd Map.empty ms in s == slicer ms
                      ))) @? ""
  ]


ntiodProps = testGroup "(concerning nontermination insensititve order dependence)" (observation_6_5_1 ++ observation_6_7_2 ++ observation_6_7_3 ++ observation_6_7_4 ++ observation_6_7_5 ++ observation_6_7_6 ++ observation_6_7_7 ++ observation_6_7_8 ++ observation_6_8_1 ++ observation_6_8_2 ++ observation_6_8_3 ++ observation_6_8_4 ++ observation_6_8_5 ++ observation_7_1_1 ++ observation_7_1_2 ++ observation_7_1_3 ++ observation_7_1_4 ++ observation_7_1_5 ++ observation_7_1_6 ++ observation_7_1_7 ++ observation_7_1_8 ++ observation8 ++ theorem_7_1_1 ++ theorem_7_1_2 ++ observation_7_1_9 ++  observationANON)

observation_6_5_1 = [
    testProperty "retainedOutside implies wcc"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = removeDuplicateEdges generatedGraph
                        n = length $ nodes g
                        s
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    in Next.retainsNextObservableOutside g s ==> Next.weaklyControlClosed g s

  ]

observation_6_7_2 = [
    testPropertySized 60 "ntiod ⊑ wodTEIL'"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiod = ODEP.ntiod g
                        wodTEIL' = ODEP.wodTEIL'PDom g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ns ⊑ (wodTEIL' ! (m1,m2))
                        )
  ]

observation_6_7_3 = [
    testProperty "wodTEIL ⊑ ntiod ∪ nticd*"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    wodTEIL'    = ODEP.wodTEIL'PDom g
                    ntiod       = ODEP.ntiodFastPDomSimpleHeuristic g
                    nticdslicer = SLICE.NTICD.nticdSlice g
                in (∀) (Map.assocs wodTEIL') (\((m1,m2), ns) ->  (∀) ns (\n ->
                       n ∈ ntiod ! (m1,m2)                 ∨  n ∈ ntiod ! (m2,m1)
                    ∨  n ∈ nticdslicer (Set.fromList [m1]) ∨  n ∈ nticdslicer (Set.fromList [m2])
                   ))
  ]

observation_6_7_4 = [
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

observation_6_7_5 = [
      testProperty  "sinkdomOfLfp m2 == mustOfGfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               sinkdom2 = PDOM.sinkdomOfGfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ sinkdom2 ! n)
                           ))
                       )
  ]

  
observation_6_7_6 = [
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

{- The actual observation is implicit in the assertions of function rotatePDomAroundNeighbours in module Data.Graph.Inductive.Query.OrderDependence -}
observation_6_7_7 = [
      testProperty  "ntiodFastPDom* == ntiodFast"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiodFastPDomSimpleHeuristic = ODEP.ntiodFastPDomSimpleHeuristic  g
                        ntiodFastPDom                = ODEP.ntiodFastPDom                 g
                        ntiodFast                    = ODEP.ntiodFast                     g
                    in   True
                       ∧ ntiodFastPDomSimpleHeuristic == ntiodFast
                       ∧ ntiodFastPDom                == ntiodFast
  ]

{- The actual observation is implicit in the assertions of function rotatePDomAroundArbitrary  in module Data.Graph.Inductive.Query.OrderDependence -}
observation_6_7_8 = observation_6_7_7


observation_6_8_1 = [
    testProperty "nticdNTIODFastSlice is sound wrt next Observations"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = generatedGraph
                        n = toInteger $ length $ nodes g
                        ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                        s = SLICE.ODEP.nticdNTIODSlice g ms
                    in Next.retainsNextObservableOutside g s
  ]

observation_6_8_2 = [
    testProperty "nticdNTIODFastSlice is minimal wrt next Observations"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = generatedGraph
                        n = toInteger $ length $ nodes g
                        ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                        s = SLICE.ODEP.nticdNTIODSlice g ms
                    in (∀) s (\n -> n ∈ ms ∨
                         let s' = Set.delete n s in not $ Next.retainsNextObservableOutside g s'
                       )
  ]


observation_6_8_3 = [
    testPropertySized 25 "nticdNTIODSlice is sound wrt infinite delay"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = removeDuplicateEdges generatedGraph
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                        
                        s = SLICE.ODEP.nticdNTIODSlice g ms
                        infinitelyDelays = InfiniteDelay.infinitelyDelays g s
                        runInput         = InfiniteDelay.runInput         g
                        observable       = InfiniteDelay.observable         s
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentFor infinitelyDelays runInput observable input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in different
                                  )
                               ))
                    in not differentobservation
  ]

observation_6_8_4 = [
    testPropertySized 25 "nticdNTIODSlice is minimal wrt infinite delay"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = removeDuplicateEdges generatedGraph
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes

                        ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)

                        s = SLICE.ODEP.nticdNTIODSlice g ms
                        runInput         = InfiniteDelay.runInput g
                    in -- traceShow (length $ nodes g, Set.size s, Set.size $ condNodes) $
                       (∀) s (\n -> n ∈ ms ∨
                         let s' = Set.delete n s
                             infinitelyDelays = InfiniteDelay.infinitelyDelays g s'
                             observable       = InfiniteDelay.observable         s'
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode ->
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentFor infinitelyDelays runInput observable input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                    in different
                                  )
                               ))
                         in differentobservation
                       )
  ]

observation_6_8_5 = [
    testPropertySized 25 "nticdNTIODSlice is termination sensitively sound for always-terminating graphs"
    $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                let     g   = removeDuplicateEdges $ efilter (\(n,m,_) -> n /= m) $ condensation generatedGraph
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        slicer     = SLICE.ODEP.nticdNTIODSlice g
                        -- slicer     = NTICD.wodTEILPDomSlice g

                        ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)

                        s = slicer ms
                        runInput   = InfiniteDelay.runInput         g
                    in let observable   = InfiniteDelay.observable s
                           differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   trace = runInput input
                                   obs   = observable trace
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        trace' = runInput input'
                                        obs'   = observable trace'
                                        different = not $ obs == obs'
                                     in (if not $ different then id else traceShow (s, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                       in not differentobservation
  ]

observation_7_1_1 = [
      testProperty "nticdSlice == ntindDef"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    nticdslicer = SLICE.NTICD.nticdSlice g
                    ntind = NTICD.ntindDef g
                in (∀) (nodes g) (\m ->
                     let ms = Set.fromList [m]
                         s  = (nticdslicer ms) ∖ ms
                         s' = Set.fromList [ n | n <- nodes g, m ∈ ntind ! n ]
                     in s == s'
                   )
  ]

observation_7_1_2 = [
      testPropertySized 40  "sinkdomOfLfp ms  == (∀) mustOfLfp  property"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        n = toInteger $ length $ nodes g

                        ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                        msL = Set.toList ms

                        toMs = rdfs msL g
                        g' = foldr (flip delSuccessorEdges) g msL
                        sinkdom' = PDOM.sinkdomOfGfp g'
                    in (∀) (nodes g) (\n -> (∀) ms (\m0 -> (∀) (nodes g) (\m ->
                                (m == m0)  ∨  ((m ∈ sinkdom' ! n) → ((m,m0) ∈ must ! n))
                       )))
  ]

observation_7_1_3 = [
    testPropertySized 40 "sinkdom g' => sinkdom g"
    $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                let g    = generatedGraph
                    n = toInteger $ length $ nodes g
                    ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                    msL = Set.toList ms

                    toMs = rdfs msL g
                    g' = foldr (flip delSuccessorEdges) g msL
                    
                    sinkdom  = PDOM.sinkdomOfGfp g
                    sinkdom' = PDOM.sinkdomOfGfp g'
                in sinkdom' ⊑ sinkdom
  ]


observation_7_1_4 = [
        testProperty "sinkdom path order"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) ms (\m1 ->  (∀) (ms) (\m2 ->
                           ((m1,m2) ∈ must ! n)
                         ∨ ((m2,m1) ∈ must ! n)
                         ∨ (m1 ∈ sinkdom ! m2 ∧  m2 ∈ sinkdom ! m1)
                       )))
  ]

observation_7_1_5 = [
      testProperty  "isinkdoms path order"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        isinkdoms = PDOM.sinkdomsOf g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) (isinkdoms ! n) (\m1 ->  (∀) (ms) (\m2 ->
                           ((m1,m2) ∈ must ! n)
                         ∨ (m1 ∈ sinkdom ! m2 ∧  m2 ∈ sinkdom ! m1  ∧  m2 ∈ isinkdoms ! n)
                         ∨ (n == m2)
                       )))
  ]

observation_7_1_6 = [
    testPropertySized 40 "technical 1"
    $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                let g    = generatedGraph
                    n = toInteger $ length $ nodes g
                    
                    ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                    msL = Set.toList ms

                    g' = foldr (flip delSuccessorEdges) g msL
                    
                    sinkdom  = PDOM.sinkdomOfGfp g
                    sinkdom' = PDOM.sinkdomOfGfp g'
                in (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m -> let { g'' = delSuccessorEdges g' m ; reachN = reachable n g'' } in 
                         let ok = (m ∈ sinkdom' ! n) ∨ ((∃) ms (\m0 ->  m0 /= m  ∧  m0 `elem` reachN))
                            in (if ok then id else traceShow (g, ms, n, m)) ok
                   ))
  ]



observation_7_1_7 = [
    testPropertySized 40 "technical 2"
    $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                let g    = generatedGraph
                    n = toInteger $ length $ nodes g
                    
                    ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                    msL = Set.toList ms

                    
                    g' = foldr (flip delSuccessorEdges) g msL
                    
                    must = ODEP.mustOfGfp g
                    
                    sinkdom  = PDOM.sinkdomOfGfp g
                    sinkdom' = PDOM.sinkdomOfGfp g'

                    trcG  = trc g
                    trcG' = trc g'
                in (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m ->
                         let ok = (m ∈ sinkdom' ! n) ∨ ((∃) ms (\m0 ->  m0 /= m  ∧  m ∈ sinkdom ! m0  ∧  n `elem` (pre trcG' m0)  ∧  m0 `elem` (pre trcG m)  ∧  (not $ (m, m0) ∈ must ! n )))
                         in (if ok then id else traceShow (g, ms, n, m)) ok
                   ))
  ]

observation_7_1_8 = [
    testPropertySized 40 "technical 3"
    $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                let g    = generatedGraph
                    n = toInteger $ length $ nodes g
                    
                    ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                    msL = Set.toList ms

                    
                    g' = foldr (flip delSuccessorEdges) g msL

                    nticdslicer' = SLICE.NTICD.nticdSlice g'
                    
                    sinkdom' = PDOM.sinkdomOfGfp g'

                in (∀) ms (\m -> (∀) (nticdslicer' (Set.fromList [ m ])) (\n -> (∀) (nodes g) (\n' -> n == n' ∨ (not $ n' ∈ sinkdom' ! n))))
  ]




observation8 = [
      testPropertySized 60  "ntiodFastPDom               ≡ ntiod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntiodFastPDomSimpleHeuristic   g ≡
                       ODEP.ntiod                          g
  ]

theorem_7_1_1 = [
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

theorem_7_1_2 = theorem_7_1_1


observation_7_1_9 = [
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

lemma_7_1_1 = theorem_7_1_1


observation_7_2_1 = [
    testPropertySized 30 "ntscdNTSODSlice == ntscdNTSODSliceViaNticd == ntscdNTSODSliceViaIMDom for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.ODEP.ntscdNTSODSlice               g
                    slicer2  = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g
                    slicer3  = SLICE.PDOM.ntscdNTSODSliceViaIMDom       g

                in   slicer1 ms == slicer2 ms
                   ∧ slicer1 ms == slicer3 ms
  ]

observation_7_2_2 = [
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
                   )
  ]

observation_7_2_3 = [
    testPropertySized 40 "technical 4"
    $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                let g    = generatedGraph
                    n = toInteger $ length $ nodes g
                    
                    ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                    msL = Set.toList ms

                    
                    g' = foldr (flip delSuccessorEdges) g msL

                    ntscdslicer' = SLICE.NTICD.ntscdSlice g'
                    
                    mdom' = PDOM.mdomOfLfp g'

                in (∀) ms (\m -> (∀) (ntscdslicer' (Set.fromList [ m ])) (\n -> (∀) (nodes g) (\n' -> n == n' ∨ (not $ n' ∈ mdom' ! n))))
  ]

lemma_7_2_1 = observation_7_2_1


observation_7_2_4 = [
      testPropertySized 25  "ntscdNTSODSlice == ntscdNTSODSliceViaNtscd even when using data dependencies"
                $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) seed1 seed2 ->
                   let g = generatedGraph
                       n    = length $ nodes g
                       ms
                        | n == 0 = Set.empty
                        | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                       ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                         where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)
                       ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                       ntscd = PDF.mDFTwoFinger g
                       ntsod =  ODEP.ntsodFastPDom g
                       slicer = combinedBackwardSlice (ddep ⊔ ntscd) ntsod

                       g' = foldr (flip delSuccessorEdges) g ms
                       ntscd' = PDF.mDFTwoFinger g'
                       empty = Map.empty
                       slicer' = combinedBackwardSlice (ddep ⊔ ntscd') empty
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



ntiodTests = testGroup "(concerning nontermination insensititve order dependence)" (observation_6_7_1)
observation_6_7_1 =  [
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
