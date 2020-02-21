{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE CPP #-}

-- #define USECONNECTED
#ifdef USECONNECTED
#define ARBITRARY(g) (CG _ g) :: (Connected Gr () ())
#else
#define ARBITRARY(g) (g) :: (Gr () ())
#endif

#define UNCONNECTED(g) (g) :: (Gr () ())
#define REDUCIBLE(g) (RedG g) :: (Reducible Gr () ())

module Program.Properties.DissObservations where

import Prelude hiding (all)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad (filterM)
import Control.Monad.Random(evalRandIO)
import Control.Exception.Base (assert)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map

import IRLSOD (Array(..), CFGNode, CFGEdge(..), Name(..), use, def, isGlobalName, globalEmpty, Val(..), Var(..), VarFunction(..) )
import Program (Program(..))
import Program.For (compileAllToProgram, For(..), twoAddressCode)
-- import Program.Generator (toProgram, , toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))
import Program.Generator (toCodeSimpleWithArrays, toProgramIntra)


import Algebra.Lattice
import Unicode

import qualified Test.QuickCheck as QC (Arbitrary (..), Gen, resize, elements)

import Util(invert'', (≡), findCyclesM, fromSet, sublists, moreSeeds, roots, restrict, sampleFrom, pathsUpToLength)
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

import Data.Graph.Inductive.Arbitrary.Reducible

import Data.Graph.Inductive.Query.DFS (dfs, rdfs, rdff, condensation)
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Util (trr, fromSuccMap, toSuccMap, controlSinks, delSuccessorEdges, removeDuplicateEdges, withUniqueEndNode, costFor)
import Data.Graph.Inductive (mkGraph, nodes, edges,  suc, pre, Node, labNodes, subgraph, reachable, newNodes, efilter, noNodes)
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

import qualified Data.Graph.Inductive.Query.FCACD as FCACD (wccSlice, wdSlice, nticdNTIODViaWDSlice)
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

import qualified Data.Graph.Inductive.Query.TSCD  as TSCD (
    tscdSliceFast, timdomOfLfp, timDFFromUpLocalDefViaTimdoms, timDF, timDFLocalViaTimdoms, timDFLocalDef, timDFUpGivenXViaTimdoms, timDFUpGivenXViaTimdomsDef,
    timdomsFromItimdomMultipleOf, timdomsOf, validTimdomLfp, timDFFromFromItimdomMultipleOfFast, tscdSlice,
    timdomMultipleOfNaiveLfp, itimdomMultipleOfTwoFinger, validTimdomFor, cost1F,
    itimdomOfTwoFingerTransitive, itimdomMultipleOfTwoFingerCost,
    timingCorrection, tscdCostSlice, timingLeaksTransformation,
  )

import qualified Data.Graph.Inductive.Query.PureTimingDependence as PTDEP (ntscdTimingSlice, nticdTimingSlice, timingDependenceFromITimdom, timingDependenceFromTimdom)

import Data.Graph.Inductive.Arbitrary
import Program.Examples (interestingTimingDep)

import CacheSlice (cacheTimingSlice)
import CacheExecution(initialCacheState, CacheSize, prependFakeInitialization, prependInitialization, cacheExecutionLimit, CachedObject(..), alignedIndices)

import qualified CacheStateDependence               as Precise   (csdMergeDirectOf)
import qualified CacheStateDependenceAgeSetsDataDep as AgeSetsDD (AbstractCacheState, csdFromDataDepJoined, cacheDepsSlowDef, cacheDepsFast,defsForSlowPsuedoDef2, defsForFast, defsForFastSimple)
import qualified CacheStateDependenceAgeSets        as AgeSets (AbstractCacheState, Age(..), Ages(..),cacheOnlyStepFor)
import CacheStateDependenceAgeSets (Age(..))

import Program.Properties.Analysis (allSoundIntraMulti)
import Program.Analysis (
  isSecureTimingClassificationAtUses, isSecureMinimalClassification, isSecureSimonClassification,
  precomputedUsing, idomDefaultFor,
  minimalClassificationFor,   timingClassificationAtUses,
  minimalClassificationNodes, timingClassificationAtUsesNodes,
 )


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


timing      = defaultMain                               $ testGroup "timing"     [ mkProp [timingProps]]
timingX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "timing"     [ mkProp [timingProps]]


probni      = defaultMain                               $ testGroup "probni"     [ mkProp [probniProps]]
probniX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "probni"     [ mkProp [probniProps]]


cache      = defaultMain                               $ testGroup "cache"     [ mkProp [cacheProps]]
cacheX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "cache"     [ mkProp [cacheProps]]



tests      = defaultMain                               $ unitTests

mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"

unitTests :: TestTree
unitTests  = testGroup "Unit tests" [                                 ntsodTests, ntiodTests]

properties :: TestTree
properties = testGroup "Properties" [ mdomProps, sdomProps, pdfProps, ntsodProps, ntiodProps, timingProps, cacheProps, probniProps]


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
    testPropertySized 40 "ipdom_max transitive closure is mdom"
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


ntiodProps = testGroup "(concerning nontermination insensititve order dependence)" (observation_6_5_1 ++ observation_6_7_2 ++ observation_6_7_3 ++ observation_6_7_4 ++ observation_6_7_5 ++ observation_6_7_6 ++ observation_6_7_7 ++ observation_6_7_8 ++ observation_6_8_1 ++ observation_6_8_2 ++ observation_6_8_3 ++ observation_6_8_4 ++ observation_6_8_5 ++ observation_7_1_1 ++ observation_7_1_2 ++ observation_7_1_3 ++ observation_7_1_4 ++ observation_7_1_5 ++ observation_7_1_6 ++ observation_7_1_7 ++ observation_7_1_8 ++ observation8 ++ theorem_7_1_1 ++ theorem_7_1_2 ++ observation_7_1_9 ++  observation_7_4_1 ++ observationANON)

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


observation_7_4_1 = [
    testPropertySized 40 "wodTEILSlice == wdSlice"
    $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                let g    = generatedGraph
                    n = toInteger $ length $ nodes g
                    ms = if n == 0 then Set.empty else Set.fromList $ sampleFrom seed (seed2 `mod` n) (nodes g)
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice g
                    wdslicer         = FCACD.wdSlice      g
                in wodteilslicer ms == wdslicer ms
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


timingProps = testGroup "(concerning timing sensitive dependency notions)" (observation_9_1_2 ++  observation_9_2_1 ++ observation_9_2_2 ++ observation_9_2_3 ++ observation_9_2_4 ++ observation_9_2_5 ++ observation_9_3_1 ++ observation_9_3_2 ++ observation_9_3_3 ++ observation_9_3_4 ++ observation_9_4_1 ++ algorithm_10 ++ algorithm_11 ++ algorithm_itimdomOfTwoFingerTransitive ++ observation_9_6_1 ++ observation_9_6_2 ++ observation_10_1_1 ++ observation_10_2_1 ++ observation_11_3_1 ++ observation_12_1_1 ++ observation_12_2_1)

observation_9_1_2 = [
    testProperty   "ntscdNTSODSlice ⊆ tscdSlice for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                          | n == 0 = Set.empty
                          | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd   g
                        tscdslicer        = TSCD.tscdSliceFast g
                    in ntscdntsodslicer ms ⊆ tscdslicer ms
  ]

observation_9_2_1 = [
    testProperty "fmap (Set.map fst) $ timdomOfLfp is transitive in reducible CFG"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                in (∀) (Map.assocs $  timdom) (\(x, ys) -> (∀) ys (\y -> (∀) (timdom ! y) (\z -> z ∈ timdom ! x )))
  ]
  
observation_9_2_2 = [
    testProperty "fmap (Set.map fst) $ timdomOfLfp is transitive in unique exit node cfg"
    $ \(ARBITRARY(generatedGraph)) ->
                let (_, g) = withUniqueEndNode () () generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                in (∀) (Map.assocs $  timdom) (\(x, ys) -> (∀) ys (\y -> (∀) (timdom ! y) (\z -> z ∈ timdom ! x )))
 ]

observation_9_2_3 = [
    testProperty   "timDFFromUpLocalDefViaTimdoms == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromUpLocalDefViaTimdoms g ==
                       TSCD.timDF                         g
  ]


observation_9_2_4 = [
    testPropertySized 40 "stepsCL timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    in PDF.stepsCL g timdom,
    testProperty   "timDFLocalViaTimdoms    == timDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFLocalViaTimdoms  g ==
                       TSCD.timDFLocalDef         g

 ]

observation_9_2_5 = [
    testPropertySized 40 "noJoins timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    in PDF.noJoins g timdom,
    testProperty   "timDFUpGivenXViaTimdoms == timDFUpGivenXViaTimdomsDef"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFUpGivenXViaTimdoms    g ==
                       TSCD.timDFUpGivenXViaTimdomsDef g
  ]

observation_9_3_1 = [
    testProperty "timdomMultiple is transitive"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    nr = toInteger $ 2 * noNodes g
                    timdomMultiple = TSCD.timdomMultipleOfNaiveLfp g
                in (∀) (Map.assocs $ timdomMultiple) (\(x, ys) -> (∀) ys (\(y,k) -> (∀) (timdomMultiple ! y) (\(z,k') -> k + k' > nr ∨ (z, k+k') ∈ timdomMultiple ! x )))
  ]

observation_9_3_2 = [
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp one step"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                         (∃) [0..n] (\fuel ->
                           (∀) ys (\(y, steps) -> 
                             ((y, steps)  ∈ timdom ! x)    ↔  (steps <= fuel)
                           )
                         )
                   )
  ]

observation_9_3_3 = [
    testProperty "timdomMultipleOfNaiveLfp step vs fuel"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    -- timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g
                    valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdom (Set.fromList $ nodes g)

                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdom ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdom
                    cycleNodes = (∐) cycles
                in (∀) (Map.assocs itimdom) (\(n, ms) -> (∀) (ms) (\(m, steps) ->
                          False
                        ∨ (n == m)
                        ∨ (n ∈ entries ∧ m ∈ cycleNodes)
                        ∨ ((not $ n ∈ cycleNodes) ∧ (not $ m ∈ cycleNodes) ∧ (valid ! n == valid ! m + steps))
                        ∨ (   (m ∈ (Set.map fst $ timdom ! n))
                            ∧ (n ∈ (Set.map fst $ timdom ! m))
                            ∧ (∀) (Set.filter ((==m) . fst) $ timdom ! n) (\(_,k)  ->
                              (∀) (Set.filter ((==n) . fst) $ timdom ! m) (\(_,k') ->
                                  True
                                ∧ (k == steps)
                                ∧ (k + k' == (valid ! m) + k)
                              ))
                          )
                   ))
  ]

observation_9_3_4 = [
      testProperty   "timdomsFromItimdomMultipleOf == timdomsOf"
                $ \(ARBITRARY(g)) ->
                       TSCD.timdomsFromItimdomMultipleOf  g ==
                       TSCD.timdomsOf                     g
  ]

observation_9_4_1 = [
      testProperty "validTimdomDef == validTimdomLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    validlfp = TSCD.validTimdomLfp g
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                         let fuel = head $ [ fuel | fuel <- [0..n], 
                               (∀) ys (\(y, steps) -> 
                                 ((y, steps)  ∈ timdom ! x)    ↔  (steps <= fuel)
                               )
                              ]
                         in fuel == validlfp ! x
                   )
  ]

algorithm_10 = [
    testProperty "validTimdomFor == validTimdomLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    itimmultiple = TSCD.itimdomMultipleOfTwoFinger g
                    valid    = TSCD.validTimdomFor g (TSCD.cost1F g) itimmultiple (Set.fromList $ nodes g)
                    validlfp = TSCD.validTimdomLfp g 
                in valid == validlfp
  ]

algorithm_11 = [
    testProperty "timDFFromFromItimdomMultipleOfFast == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromFromItimdomMultipleOfFast  g ==
                       TSCD.timDF                               g
  ]

isTransitive timdom = (∀) (Map.assocs $ timdom) (\(x, ys) -> (∀) ys (\y -> (∀) (timdom ! y) (\z -> z ∈ timdom ! x )))


algorithm_itimdomOfTwoFingerTransitive =  [
    testProperty "itimdomOfTwoFingerTransitive^* == itimdomOfLfp in reducible cfg"
                $ \(REDUCIBLE(g)) ->
                let
                     costF = TSCD.cost1F g
                     timdom  =                                  fmap (Set.map fst) $ TSCD.timdomOfLfp g
                     timdom' = toSuccMap $ trc $ (fromSuccMap $ fmap (Set.map fst) $ TSCD.itimdomOfTwoFingerTransitive g costF :: Gr () ())
                in (isTransitive timdom) ∧ (timdom == timdom'),
    testProperty "itimdomOfTwoFingerTransitive^* == itimdomOfLfp in unique exit node cfg"
                $ \(ARBITRARY(generatedGraph)) ->
                let  (_, g) = withUniqueEndNode () () generatedGraph
                     costF = TSCD.cost1F g
                     timdom  =                                  fmap (Set.map fst) $ TSCD.timdomOfLfp g
                     timdom' = toSuccMap $ trc $ (fromSuccMap $ fmap (Set.map fst) $ TSCD.itimdomOfTwoFingerTransitive g costF :: Gr () ())
                in (isTransitive timdom) ∧ (timdom == timdom')
    -- testProperty "itimdomOfTwoFingerTransitive^* == itimdomOfLfp in cfg with transitive timdom"
    --             $ \(ARBITRARY(g)) ->
    --             let  costF = TSCD.cost1F g
    --                  timdom  =                                  fmap (Set.map fst) $ TSCD.timdomOfLfp g
    --                  timdom' = toSuccMap $ trc $ (fromSuccMap $ fmap (Set.map fst) $ TSCD.itimdomOfTwoFingerTransitive g costF :: Gr () ())
    --             in (isTransitive timdom) ==> (timdom == timdom')
  ]
  
observation_9_6_1 = [
    testProperty "timdomMultipleOfNaiveLfp == timdom in unique exit node cfg"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                        timdom     = fmap (Set.map fst) $ TSCD.timdomOfLfp              g
                        timdomMult = fmap (Set.map fst) $ TSCD.timdomMultipleOfNaiveLfp g
                    in timdom == timdomMult
  ]

observation_9_6_2 = [
    testProperty "timdomMultipleOfNaiveLfp == timdom in reducible cfg"
                $ \(REDUCIBLE(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                        timdom     = fmap (Set.map fst) $ TSCD.timdomOfLfp              g
                        timdomMult = fmap (Set.map fst) $ TSCD.timdomMultipleOfNaiveLfp g
                    in timdom == timdomMult
  ]



observation_10_1_1 = [
    testProperty "nticdTimingSlice == ntscdTimingSlice == tscdSlice == tscdSliceFast"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    ntscdtimingslicer  = PTDEP.ntscdTimingSlice g
                    nticdtimingslicer  = PTDEP.nticdTimingSlice g
                    tscdslicer         = TSCD.tscdSlice        g
                    tscdslicerfast     = TSCD.tscdSliceFast    g
                in (∀) (nodes g) (\m ->
                     let ms = Set.fromList [m]
                         s1 = nticdtimingslicer ms
                         s2 = ntscdtimingslicer ms
                         s3 = tscdslicer        ms
                         s4 = tscdslicerfast    ms
                     in s1 == s2  ∧  s2 == s3  ∧  s3 == s4
                   )
  ]

{- The first equation is implicit in the assertions of the function timingDependenceFromTimdom from module Data.Graph.Inductive.Query.PureTimingDependence --}
observation_10_2_1 = [
      testProperty  "timingDependenceFromTimdom  == timingDependenceFromITimdom for n /= m"
                $ \(ARBITRARY(g)) ->
                       let tdepfromTwoFinger = Map.mapWithKey Set.delete $ PTDEP.timingDependenceFromITimdom g
                           tdepfromTimdom    = Map.mapWithKey Set.delete $ PTDEP.timingDependenceFromTimdom g
                       in  tdepfromTimdom == tdepfromTwoFinger
  ]


observation_11_3_1 = [
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in CFG with empty ntsod"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    ntsod = ODEP.ntsodFastPDom   g

                    cost0 = costFor g seed3
                    (cost, _) = TSCD.timingCorrection g cost0
                      
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                    ntsodIsEmpty = (∀) (Map.assocs ntsod) (\(_,ns) -> Set.null ns)
                in ntsodIsEmpty   ==>   (s == s') ∧ ((∀) (Map.assocs cost0) (\(nm,c0) -> c0 <= cost ! nm) ∧ (∀) (Map.assocs cost) (\(nm,c) -> c >= cost0 ! nm))
  ]



observation_12_1_1 = [
    testProperty "timingCorrection tscdCostSlice  g[ms -/> ] ms == ntscdNTSODSlice g ms for random slice criteria of random size"
    -- $ \seed1 seed2 seed3 -> (∀) interestingTimingDep (\(exampleName, generatedGraph) ->
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    n = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    cost0 = costFor g seed3
                    
                    g' = foldr (flip delSuccessorEdges) g ms
                    (cost, _) = TSCD.timingCorrection          g' cost0
                    costF n m = cost ! (n,m)

                    tscdcostslicer    = TSCD.tscdCostSlice                  g   costF  
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

    
                    s    = tscdcostslicer    ms
                    s'   = ntscdntsodslicer  ms
                in (s == s') ∧ ((∀) (Map.assocs cost0) (\(nm,c0) -> c0 <= cost ! nm) ∧ (∀) (Map.assocs cost) (\(nm,c) -> c >= cost0 ! nm))
  ]


observation_12_2_1 = [
    testProperty "timingLeaksTransformation tscdCostSlice g ms == ntscdNTSODSlice ms for random slice criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    n = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    cost0 = costFor g seed3
                    
                    (cost,   _) = TSCD.timingLeaksTransformation g   cost0 ms
                    costF n m = cost ! (n,m)
                    
                    tscdcostslicer    = TSCD.tscdCostSlice                  g   costF  
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

    
                    s    = tscdcostslicer    ms
                    s'   = ntscdntsodslicer  ms
                in (s == s') ∧ ((∀) (Map.assocs cost0) (\(nm,c0) -> c0 <= cost ! nm) ∧ (∀) (Map.assocs cost) (\(nm,c) -> c >= cost0 ! nm))
  ]


cacheProps = testGroup "(concerning micro-architectural dependencies)" (observation_13_5_1 ++ observation_15_2_1 ++ observation_15_3_1 ++ observation_15_5_1)
observation_13_5_1 = [
    testPropertySized 25 "cacheTimingSlice is sound [slow]"
                $ \generated seed1 seed2 seed3 seed4 ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b'
                          where (a,b) = toCodeSimpleWithArrays generated
                                b' = fmap twoAddressCode b
                    in isSound cacheTimingSlice pr seed1 seed2 seed3 seed4
  ]

observation_15_5_1 = [
    testPropertySized 25 "csdMergeDirectOf ⊑ AgeSets.csdFromDataDepJoined"
                $ \generated ->
                    let pr :: Program Gr
                        pr = compileAllToProgram a b'
                          where (a,b) = toCodeSimpleWithArrays generated
                                b' = fmap twoAddressCode b
                        g = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        csdM   = Precise.csdMergeDirectOf       propsCacheSize g n0
                        csdMAS = AgeSetsDD.csdFromDataDepJoined propsCacheSize g n0
                    in  csdM ⊑ csdMAS
  ]

-- Map CachedObject Ages
newtype ArrayAbstractCacheState = ArrayAbstractCacheState AgeSets.AbstractCacheState

arrayCacheStateGenerator ::  Int -> QC.Gen AbstractCacheState
arrayCacheStateGenerator 0 = return $ AbstractCacheState $ Map.empty
arrayCacheStateGenerator n = do
    nrArrs <- elements [0 .. min 3 n ]
    cos <- sublistOf  [ CachedArrayRange (Array ("a" ++ show a)) i | a <- [0.. nrArrs - 1 ], i <- alignedIndices :: [Val] ]
    assocs <- mapM f cos
    return $ AbstractCacheState $ Map.fromList assocs
  where f :: CachedObject -> Gen (CachedObject, AgeSets.Ages)
        f co = do
                Ages as <- QC.resize n arbitrary
                return (co, as)

        sublistOf xs = filterM (\_ -> choose (False, True)) xs

newtype Ages = Ages AgeSets.Ages deriving Show
instance QC.Arbitrary Ages where
  arbitrary = do
    is <- (listOf arbitrary :: Gen [Int])
    hasNothing <- elements [True, False]
    let mis = if hasNothing then Nothing : (fmap Just is) else fmap Just is
    return $ Ages $ (Set.fromList $ fmap (AgeSets.Age . (fmap abs)) $ mis)

newtype AbstractCacheState = AbstractCacheState AgeSets.AbstractCacheState deriving Show
instance QC.Arbitrary  AbstractCacheState where
  arbitrary = sized arrayCacheStateGenerator


observation_15_2_1 = [
  testPropertySized 25 "cacheDepsFast == cacheDepsSlowDef" $
    \(AbstractCacheState cache0) seed ->
      let
          cache = Map.filter (not . Set.null) $ fmap (Set.filter isValid) cache0 :: AgeSets.AbstractCacheState
          CachedArrayRange a i = (cycle $ Map.keys cache0) !! (abs seed)
          e1 = Assign (Register 0) (ArrayRead a (Var $ Register 1))
          e2 = Assign (Register 0) (ArrayRead a (Val $ 0))
      in (not $ Map.null cache0)
         ==> (noMinMax $ AgeSetsDD.cacheDepsFast propsCacheSize e1 cache) == AgeSetsDD.cacheDepsSlowDef propsCacheSize e1 cache
           ∧ (noMinMax $ AgeSetsDD.cacheDepsFast propsCacheSize e2 cache) == AgeSetsDD.cacheDepsSlowDef propsCacheSize e2 cache
 ]
  where isValid (AgeSets.Age Nothing)  = True
        isValid (AgeSets.Age (Just x)) = x < propsCacheSize

        {- cacheDepsFast also computes bounds (min, max) of ranges on which the dependency applies. Delete those bounds. -}
        noMinMax = Map.filter (not . Set.null) . Map.mapWithKey (\coUse cos -> Set.delete coUse $ Set.map first $ cos)
          where first (co,_,_) = co



observation_15_3_1 = [
  testPropertySized 25 "defsForFast == defsForSlowPseudoDef2" $
    \(AbstractCacheState cache0) seed ->
      let
          cache  = Map.filter (not . Set.null) $ fmap (Set.filter isValid) cache0 :: AgeSets.AbstractCacheState
          CachedArrayRange a i = (cycle $ Map.keys cache0) !! (abs seed)

          cache' = (∐) [ cache' | (_, cache') <- AgeSets.cacheOnlyStepFor propsCacheSize e cache ]

          e = Assign (Register 0) (ArrayRead a (Var $ Register 1))

      in (not $ Map.null cache0)
         ==> (Map.keysSet $ AgeSetsDD.defsForFast propsCacheSize fst (0, e, cache, cache')) == AgeSetsDD.defsForSlowPsuedoDef2 propsCacheSize fst (0, e, cache, cache'),

  testPropertySized 25 "defsForFastSimple == defsForSlowPseudoDef2" $
    \(AbstractCacheState cache0) seed ->
      let
          cache  = Map.filter (not . Set.null) $ fmap (Set.filter isValid) cache0 :: AgeSets.AbstractCacheState
          CachedArrayRange a i = (cycle $ Map.keys cache0) !! (abs seed)

          cache' = (∐) [ cache' | (_, cache') <- AgeSets.cacheOnlyStepFor propsCacheSize e cache ]

          e = Assign (Register 0) (ArrayRead a (Var $ Register 1))

      in (not $ Map.null cache0)
         ==> AgeSetsDD.defsForFastSimple propsCacheSize fst (0, e, cache, cache') == AgeSetsDD.defsForSlowPsuedoDef2 propsCacheSize fst (0, e, cache, cache')

 ]
  where isValid (AgeSets.Age Nothing)  = True
        isValid (AgeSets.Age (Just x)) = x < propsCacheSize


type Slicer =
     CacheSize
  -> Gr CFGNode CFGEdge
  -> Node
  -> Set Node
  -> Set Node

propsCacheSize = 4

isSound :: Slicer -> Program Gr -> Int -> Int -> Int -> Int -> Bool
isSound slicerFor pr seed1 seed2 seed3 seed4 =
                    let
                        g0 = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        
                        vars  = Set.fromList [ var | n <- nodes g0, name@(VarName   var) <- Set.toList $ use g0 n ∪ def g0 n, isGlobalName name]
                        varsA = Set.fromList [ arr | n <- nodes g0, name@(ArrayName arr) <- Set.toList $ use g0 n ∪ def g0 n, isGlobalName name]
                        (newN0:new) = (newNodes ((Set.size vars) + (Set.size varsA) + 1) g0)
                        varToNode = Map.fromList $ zip ((fmap VarName $ Set.toList vars) ++ (fmap ArrayName $ Set.toList varsA)) new
                        nodeToVar = Map.fromList $ zip new ((fmap VarName $ Set.toList vars) ++ (fmap ArrayName $ Set.toList varsA))

                        g = prependFakeInitialization g0 n0 newN0 varToNode
                        slicer = slicerFor propsCacheSize g newN0


                        initialFullState   = ((globalEmpty, Map.empty, ()), initialCacheState, 0)
                        prependActualInitialization = prependInitialization g0 n0 newN0 varToNode

                        initialGlobalState1  = Map.fromList $ zip (Set.toList vars ) (            fmap (`rem` 32)   $ moreSeeds seed1 (Set.size vars))
                        initialGlobalState1A = Map.fromList $ zip (Set.toList varsA) (      fmap (fmap (`rem` 32))  $ vals                           )
                          where aSeeds = moreSeeds seed4 (Set.size varsA)
                                vals = fmap (Map.fromList . zip [0..]) $ fmap (`moreSeeds` 256) aSeeds
                        g1 = prependActualInitialization initialGlobalState1 initialGlobalState1A


                        limit = 9000
                        (execution1, limited1) = assert (length es == 1) $ (head es, (length $ head es) >= limit)
                          where es = cacheExecutionLimit propsCacheSize limit g1 initialFullState newN0

                        ms = [ nodes g0 !! (m `mod` (length $ nodes g0)) | m <- moreSeeds seed2 100]
                    in (∀) ms (\m ->
                         let s = slicer (Set.fromList [m])
                             notInS  = (Set.map ((varToNode !) . VarName  ) vars ) ∖ s
                             notInSA = (Set.map ((varToNode !) . ArrayName) varsA) ∖ s
                             initialGlobalState2  = (Map.fromList $ zip [ var | n <- Set.toList notInS,  let VarName   var = nodeToVar ! n] newValues) `Map.union` initialGlobalState1
                               where newValues =       fmap (`rem` 32)  $ moreSeeds (seed3 + m) (Set.size notInS)
                             initialGlobalState2A = (Map.fromList $ zip [ arr | n <- Set.toList notInSA, let ArrayName arr = nodeToVar ! n] newValues) `Map.union` initialGlobalState1A
                               where aSeeds = moreSeeds (seed4 + m) (Set.size notInSA)
                                     newValues = fmap (fmap (`rem` 32)) $ fmap (Map.fromList . zip [0..]) $ fmap (`moreSeeds` 256) aSeeds
                             g2 = prependActualInitialization initialGlobalState2 initialGlobalState2A

                             (execution2, limited2) = assert (length es == 1) $ (head es, (length $ head es) >= limit)
                               where es = cacheExecutionLimit propsCacheSize limit g2 initialFullState newN0

                             exec1Obs = filter (\(n,_) -> n ∈ s) $ execution1
                             exec2Obs = filter (\(n,_) -> n ∈ s) $ execution2

                          in limited1 ∨ limited2 ∨ (exec1Obs == exec2Obs)
                        )



probniProps = testGroup "(concerning criteria for probabilistic non-interference)" (observation_16_4_1 ++ observation_16_6_2)

observation_16_4_1 = [
    testPropertySized 15
         ("allSoundIntraMulti [isSecureTimingClassificationAtUses, isSecureMinimalClassification, isSecureSimonClassification] [slow]")
         ( allSoundIntraMulti [isSecureTimingClassificationAtUses, isSecureMinimalClassification, isSecureSimonClassification])
  ]

observation_16_6_1 = observation_16_4_1

observation_16_6_2 = [
    testPropertySized 30  "cl timing ⊑ cl minimal"
                $ \generated -> let p :: Program Gr = toProgramIntra generated
                                    pc = precomputedUsing idomDefaultFor p
                                    clMinimal            = minimalClassificationFor   pc p
                                    (clTiming,clTiming2) = timingClassificationAtUses pc p
                                in   (clTiming ⊑ clMinimal)
                                   ∧ (∀) (Map.assocs clTiming2) (\((m1,m2), clTiming2) -> (clTiming2 ⊑ (clMinimal ! m1))  ∨  (clTiming2 ⊑ (clMinimal ! m2))),
    testPropertySized 20  "cl timing ⊑ cl minimal w.r.t. node sets"
                $ \generated -> let p :: Program Gr = toProgramIntra generated
                                    pc = precomputedUsing idomDefaultFor p
                                    clMinimal            = minimalClassificationNodes   pc p
                                    (clTiming,clTiming2) = timingClassificationAtUsesNodes pc p
                                in   (clTiming ⊑ clMinimal)
                                   ∧ (∀) (Map.assocs clTiming2) (\((m1,m2), clTiming2) ->  clTiming2  ⊆  clMinimal ! m1 ∪ clMinimal ! m2)
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
