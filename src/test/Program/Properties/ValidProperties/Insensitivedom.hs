{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Insensitivedom where


import Debug.Trace (traceShow, trace)
import Control.Exception.Base (assert)
import Control.Monad.Random (randomR, getStdRandom)

import qualified Data.List as List
import Data.List (sortOn)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Tree as Tree
import Data.Ord (Down(..))

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Runners.AntXML

import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, lsuc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph, delEdges, insEdge, newNodes)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Arbitrary
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Query.DFS (scc, dfs, rdff)

import Unicode
import Util(sampleFrom, invert'', invert''', moreSeeds, restrict, toSet, fromSet, treeLevel, findCyclesM)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, interestingIsinkdomTwoFinger, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)


import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (isinkdomOf, isinkdomOfGfp2, joinUpperBound, sinkdomOfJoinUpperBound, sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkdomNaiveGfp, sinkdomNaiveGfpFullTop, sinkdomOfisinkdomProperty, imdomOf, imdomOfLfp, mdomOf, mdomOfLfp, mdomNaiveLfp, mdomOfimdomProperty, onedomOf, mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, isinkdomOftwoFinger8Up,  imdomOfTwoFinger6, imdomOfTwoFinger7)
import qualified Data.Graph.Inductive.Query.NTICD.Program as PROG (
    sinkDFF2GraphP, sinkDFGraphP, sinkDFFromUpLocalDefGraphP, sinkDFFromUpLocalGraphP,
       mDFF2GraphP,    mDFGraphP,    mDFFromUpLocalDefGraphP,    mDFFromUpLocalGraphP,
    nticdSinkContractionGraphP,
    nticdDefGraphP, ntscdDefGraphP,
    nticdF3GraphP, nticdF3'GraphP, nticdF3'dualGraphP,
    nticdF3WorkListGraphP,
    nticdF3WorkListSymbolicGraphP, nticdF3'dualWorkListSymbolicGraphP, nticdFig5GraphP, nticdF5GraphP,  nticdF3'dualWorkListGraphP,
    ntscdF4GraphP, ntscdF3GraphP, ntscdF4WorkListGraphP,
    ntacdDefGraphP,
  )
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (
    isinkDFTwoFinger, mDFTwoFinger,  noJoins, stepsCL,
    sinkDFF2cd,  sinkDFcd,  sinkDFFromUpLocalDefcd, sinkDFFromUpLocalcd,  isinkdomTwoFingercd,
    sinkDFUp, sinkDFUpDef, sinkDFUpDefViaSinkdoms,
    sinkDFLocal, sinkDFLocalDef, sinkDFLocalViaSinkdoms, sinkDFUpGivenX, sinkDFUpGivenXViaSinkdoms,
    sinkDFFromUpLocalDefViaSinkdoms, sinkDF,
    idomToDF, idomToDFFast,
    mDFF2cd,        mDFcd,       mDFFromUpLocalDefcd,         mDFFromUpLocalcd,         imdomTwoFingercd,
    mDFUp, mDFUpDef, mDFUpDefViaMdoms, mDFUpGivenXViaMdoms,
    mDFLocal, mDFLocalDef, mDFLocalViaMdoms, mDFUpGivenX, 
    mDFFromUpLocalDefViaMdoms, mDF,
 )
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges as CEDGE (nticdSliceNumberedViaCEdgesFast, ntscdSliceViaCEdgesFast, dfViaCEdges, idfViaCEdgesFast, nticdSliceViaCEdgesFast, nticdSliceViaCEdgesFastFor)
import qualified Data.Graph.Inductive.Query.PostDominance.Numbered as PDOMNumbered (iPDom, pdom, numberForest)
import qualified Data.Graph.Inductive.Query.PostDominance.GraphTransformations as PDOM.TRANS (isinkdomOfSinkContraction)
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (
    nticdNTIODSlice, nticdSlice,  ntscdSlice,
    ntscdNTSODSliceViaNtscd, wodTEILSliceViaNticd,
    wccSliceViaNticd,
  )
import qualified Data.Graph.Inductive.Query.Slices.PostDominanceFrontiers as SLICE.PDF (nticdSliceFor)
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    nticdViaSinkDom,
    ntscdViaMDom,
    ntindDef, ntsndDef,
    nticdDef, 
    ntscdDef, 
  )
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, 
    nticdF3'dualWorkList, snmF3'dual,
    ntscdF4, ntscdF3, ntscdF4WorkList
  )

insensitivedom    = defaultMain                               $ testGroup "insensitiveDom"   [ mkTest [insensitiveDomTests],  mkProp [insensitiveDomProps]]
insensitivedomX   = defaultMainWithIngredients [antXMLRunner] $ testGroup "insensitiveDom"   [ mkTest [insensitiveDomTests],  mkProp [insensitiveDomProps]]


insensitiveDomProps = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" [
    testProperty   "nticdViaSinkDom          == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.nticdViaSinkDom g ==
                       SNM.nticdF3          g,
    testPropertySized 20 "sinkdom g_{M/->}^{M->*} ⊆ (sinkdom g)|{M->*}"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 -> let ms = [m1,m2,m3] in
                         let fromMs = dfs ms g
                             g' = foldr (flip delSuccessorEdges) (subgraph fromMs g) ms
                             sinkdom' = PDOM.sinkdomOfGfp g'
                         in sinkdom' ⊑ restrict sinkdom (Set.fromList fromMs)
                       ))),
    testProperty "sinkdom g^{M->*}^{M->*} ⊆ (sinkdom g)|{M->*} for random sets M of random Size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                        n  = length $ nodes g
                        ms
                         | n == 0 = []
                         | n /= 0 = [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        fromMs = dfs ms g
                        g' = foldr (flip delSuccessorEdges) (subgraph fromMs g) ms
                        sinkdom' = PDOM.sinkdomOfGfp g'
                    in sinkdom' ⊑ restrict sinkdom (Set.fromList fromMs),
    testPropertySized 20 "sinkdom g^{M->*} == (sinkdom g)|{M->*}"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                        nticd = NTICD.nticdViaSinkDom g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 -> let ms = [m1,m2,m3] in
                         let fromMs = dfs ms g
                             g' = subgraph fromMs g
                             sinkdom' = PDOM.sinkdomOfGfp g'
                             nticd' = NTICD.nticdViaSinkDom g'
                         in   sinkdom' == restrict sinkdom (Set.fromList fromMs)
                            ∧ nticd'   == restrict nticd   (Set.fromList fromMs)
                       ))),
    testProperty "sinkdom g^{M->*} == (sinkdom g)|{M->*} for random sets M of random Size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                        nticd = NTICD.nticdViaSinkDom g
                        n  = length $ nodes g
                        ms
                         | n == 0 = []
                         | n /= 0 = [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        fromMs = dfs ms g
                        g' = subgraph fromMs g
                        sinkdom' = PDOM.sinkdomOfGfp g'
                        nticd' = NTICD.nticdViaSinkDom g'
                    in   sinkdom' == restrict sinkdom (Set.fromList fromMs)
                       ∧ nticd'   == restrict nticd   (Set.fromList fromMs),
    testPropertySized 40 "stepsCL sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in PDF.stepsCL g sinkdom,
    testPropertySized 40 "noJoins sinkdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfGfp g
                    in PDF.noJoins g sinkdom,
    testProperty   "dfs numbering properties"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        n = length $ nodes g
                        sinks = controlSinks g
                        
                        forest = rdff [ s| (s:_) <- sinks] g
                        tree = Tree.Node undefined forest
                        
                        (_, nforest) = PDOMNumbered.numberForest 1 forest
                        ntree = Tree.Node undefined nforest
                        fromNode = Map.fromList $ zip (tail $ Tree.flatten  tree) (tail $ Tree.flatten ntree)
                        toNode   = Map.fromList $ zip (tail $ Tree.flatten ntree) (tail $ Tree.flatten  tree)
                        sinkSuccs = [ (s1, s2) | sink@(_:_:_) <- sinks, let (s:sorted) = sortOn Down $ fmap (fromNode Map.!) sink, (s1,s2) <- zip (s:sorted) (sorted ++ [s]) ]
                        sinkOf        = Map.fromList [ (s, s0)  | sink@(s0:_) <- sinks, s <- sink ]
                        sinkNodes = Set.fromList [ s | sink <- sinks, s <- sink]

                        sinkdom = PDOM.sinkdomOfGfp g
                    in (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m ->
                           (       n ∈ sinkNodes   ∧  m ∈ sinkNodes  ∧  sinkOf ! n == sinkOf ! m) 
                         ∨ ((not $ n ∈ sinkNodes)  ∧  m ∈ sinkNodes  ∧  (fromNode ! (sinkOf ! m) >= fromNode ! m))
                         ∨ (fromNode ! m >= fromNode ! n)
                       )),
    testProperty   "nticdSliceNumbered  == nticdSliceNumberedViaCEdgesFast for ladder-graphs and randomly selected nodes"
    $ \(size :: Int) seed1 seed2 seed3 ->
                let n0 = (abs size) `div` 2
                    g = ladder n0  :: Gr () ()
                    idom = assert (n == 2*n0 + 3) $ 
                                       Map.fromList [(i, Just (i+2))| i <- [1,3 ..(n-3)]]
                           `Map.union` Map.fromList [(i, Nothing)   | i <- [0   ..(n-1)]]
                    roots = assert (idom == fmap fromSet (PDOM.isinkdomOfTwoFinger8 g)) $
                            fmap (\n -> [n]) $  Map.keys $ Map.filter (== Nothing) idom
                    
                    nrSlices = 1
                    n = length $ nodes g
                    mss = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    nticdslicer        = SLICE.PDF.nticdSliceFor              roots g idom
                    nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFastFor roots g idom
                in (∀) mss (\ms -> nticdslicer ms == nticdslicerCEdges ms),
    testProperty   "nticdSlice  == nticdSliceViaCEdgesFast for CFG-shaped graphs and randomly selected nodes"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 seed3 ->
  --               let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
  --                   [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
  --                   g = insEdge (exit, entry, ()) generatedGraph
                let g = generatedGraph
                    nrSlices = 10
                    n = length $ nodes g
                    mss = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    nticdslicer        = SLICE.NTICD.nticdSlice              g
                    nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                in (∀) mss (\ms -> nticdslicer ms == nticdslicerCEdges ms),
    testPropertySized 60 "idfViaCEdgesFast properties"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinkdom = PDOM.sinkdomOfLfp g
                        isinkdomsOf = PDOM.sinkdomsOf g
                        idom = fmap fromSet $ PDOM.isinkdomOfTwoFinger8 g
                        idom'  = invert''' idom
                        (cycleOfM, cycles) = findCyclesM idom
                        roots = foldr (\(n,m) roots -> if m == Nothing then Set.fromList [n] : roots else roots) cycles (Map.assocs idom)
                        levelOf = Map.fromList [ (n,l) | nl <- treeLevel idom' roots, (n,l) <- nl]
                        cEdges = Map.fromList [(z, [ y | y <- pre g z, not $ z ∈ isinkdomsOf ! y ]) | z <- nodes g]
                    in   (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  sinkdom ! x   ⊃   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                      ∧  (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  not $  x   ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                      ∧  (∀) (nodes g) (\z -> (∀) (sinkdom ! z) (\x -> (∀) (cEdges ! z) (\y -> (       x   ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])
                                                                                   ↔ (not $ sinkdom ! x    ⊃   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])
                         )))
                      ∧  (∀) (nodes g) (\z -> (∀) (sinkdom ! z) (\x -> (∀) (cEdges ! z) (\y ->
                           (   ( (sinkdom ! x  ⊃  (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])  ∧  (not $ x  ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                             ∨ ( (sinkdom ! x  ⊆  (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y])  ∧  (      x  ∈   (∐) [ sinkdom ! y' | y' <- Set.toList $ isinkdomsOf ! y]))
                           )
                         ∧ (let ok = ((x /= y)  ∧  (not $ Set.null $ sinkdom ! y ∩ sinkdom ! x)) → ((not $ x ∈ sinkdom ! y) ↔ (levelOf ! y <= levelOf ! x)) in (if ok then id else traceShow (g,x,y,z, levelOf)) ok
                           )
                         ))),
    testProperty   "nticdSlice  == nticdslicerCEdges"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticdslicer        = SLICE.NTICD.nticdSlice              g
                        nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> let ms = Set.fromList [m1,m2] in
                              nticdslicer ms == nticdslicerCEdges ms
                    )),
    testProperty   "nticdSlice  == nticdslicerCEdges for CFG like graphs for random slice-criteria of random size"
                $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        n    = length $ nodes g
                        ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        nticdslicer        = SLICE.NTICD.nticdSlice              g
                        nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                    in  nticdslicer ms == nticdslicerCEdges ms,
    testProperty   "nticdSlice  == nticdslicerCEdges for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        nticdslicer        = SLICE.NTICD.nticdSlice              g
                        nticdslicerCEdges  = CEDGE.nticdSliceViaCEdgesFast g
                    in  nticdslicer ms == nticdslicerCEdges ms,
    testProperty   "idomToDFFast _ == dfViaCEdges _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                         let dfViaJ = CEDGE.dfViaCEdges g (fmap fromSet isinkdom) in
                         PDF.idomToDFFast g isinkdom == Map.fromList [ (n, dfViaJ n) | n <- nodes g]
                    ),
    testProperty   "nticd*  _ == dfViaCEdges _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticd = NTICD.nticdViaSinkDom g
                        isinkdom = PDOM.isinkdomOfTwoFinger8 g
                        dfViaJ = CEDGE.dfViaCEdges g (fmap fromSet isinkdom)
                    in (∀) (nodes g) (\n -> (∀) (nodes g) (\m -> if m == n then True else
                         (n ∈ dfViaJ m)  == (m ∈ nticd ! n)
                    )),
    testProperty   "idomToDFFast _ isinkdom == sinkDF _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g isinkdom ==
                       PDF.sinkDF       g),
    testProperty   "idomToDFFast _ isinkdom == idomToDF _ isinkdom"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g                isinkdom ==
                       PDF.idomToDF     g (fromSuccMap $ isinkdom :: Gr () ())),
    testProperty   "DF of isinkdom Cycles are all the same"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = fromSuccMap $ PDOM.TRANS.isinkdomOfSinkContraction g :: Gr () ()
                        isinkdom2 = fromSuccMap $ PDOM.isinkdomOfTwoFinger8      g :: Gr () ()
                        df1    = PDF.idomToDF g isinkdom1
                        idomSccs1 = scc isinkdom1
                        cycles1 = [ cycle | cycle <- idomSccs1, length cycle > 1 ]
                        df2    = PDF.idomToDF g isinkdom2
                        idomSccs2 = scc isinkdom2
                        cycles2 = [ cycle | cycle <- idomSccs2, length cycle > 1 ]
                    in (∀) [(isinkdom1, cycles1, df1), (isinkdom2, cycles2, df2)] (\(isinkdom, cycles, df) ->
                       (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))),
    testProperty   "iPDom^*  == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ fromSuccMap $ fmap toSet $ Map.fromList $
                              PDOMNumbered.iPDom  g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "pdom  == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (      fromSuccMap $ fmap Set.fromList $ Map.fromList $ 
                              PDOMNumbered.pdom  g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "isinkdomOfSinkContraction is intransitive"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom1 = fromSuccMap $ PDOM.TRANS.isinkdomOfSinkContraction g :: Gr () ()
                        isinkdom2 = fromSuccMap $ PDOM.isinkdomOfTwoFinger8      g :: Gr () ()
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                         (∀) (nodes isinkdom) (\n -> length (suc isinkdom n) <= 1)),
    testProperty   "isinkdomOfSinkContraction^*  == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ fromSuccMap $
                              PDOM.TRANS.isinkdomOfSinkContraction  g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "isinkdomOf^*          == isinkdomOfTwoFinger8^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.isinkdomOfTwoFinger8       g),
    testProperty   "isinkdomOf^*          == isinkdomOfSinkContraction^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.TRANS.isinkdomOfSinkContraction g),
    testProperty   "joinUpperBound always computes an upper bound"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sinks = controlSinks g
                    in (∀) (Map.assocs $ PDOM.joinUpperBound g) (\(n,maybeNs) -> maybeNs /= Nothing ∨   (∃) (sinks) (\sink -> n ∊ sink)),
    testProperty   "isinkdomOf^*          == sinkdomOfJoinUpperBound^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                              PDOM.sinkdomOfJoinUpperBound g),
    testProperty   "isinkdomOf^*          == isinkdomOfGfp2^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.isinkdomOf                 g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        PDOM.isinkdomOfGfp2             g),
    testProperty   "sinkdomOf reduces, in some sense,  to a multi-rooted tree"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom = PDOM.isinkdomOf g :: Gr () ()
                    in   (∀) (nodes isinkdom) (\n -> length (suc isinkdom n) <= 1),
    testProperty   "sinkdomOf             == sinkdomOfisinkdomProperty"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf                  g ==
                       PDOM.sinkdomOfisinkdomProperty  g,
    testProperty   "sinkdomOf             == sinkdomNaiveLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomNaiveGfp        g,
    testProperty   "sinkdomOf             == sinkdomOfLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomOfLfp           g,
    testProperty   "sinkdomOf             == sinkdomOfGfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomOfGfp           g,
    testProperty   "sinkdomOf             == sinkdomNaiveGfpFullTop for graphs with unique end node property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (exit, g) = withUniqueEndNode () () generatedGraph
                    in PDOM.sinkdomOf              g ==
                       PDOM.sinkdomNaiveGfpFullTop g,
    testProperty   "sinkDFFromUpLocalDefViaSinkdoms == sinkDF"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFFromUpLocalDefViaSinkdoms g ==
                       PDF.sinkDF                          g,
    testProperty   "sinkDFUpGivenXViaSinkdoms == sinkDFUpGivenX"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFUpGivenXViaSinkdoms  g ==
                       PDF.sinkDFUpGivenX             g,
    testProperty   "sinkDFUpDefViaSinkdoms == sinkDFUpDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFUpDefViaSinkdoms  g ==
                       PDF.sinkDFUpDef             g,
    testProperty   "sinkDFUpGivenX ! (x,z) is independent of choice of x for given z"
                $ \(ARBITRARY(g)) ->
                    let sinkDFUp = PDF.sinkDFUpGivenX g
                    in (∀) (Map.assocs sinkDFUp) (\((x,z), dfUp) ->
                         (∀) (Map.assocs sinkDFUp) (\((x',z'), dfUp') ->
                           (z == z') → (dfUp == dfUp')
                         )
                       ),
    testProperty   "sinkDFUpGivenX ! (x,z) == sinkDFUpDef ! z"
                $ \(ARBITRARY(g)) ->
                    let sinkDFUp    = PDF.sinkDFUpGivenX g
                        sinkDFUpDef = PDF.sinkDFUpDef    g
                    in (∀) (Map.assocs sinkDFUp) (\((x,z), dfUp) ->
                         dfUp == sinkDFUpDef ! z
                       )
                    ∧  (∀) (Map.assocs sinkDFUpDef) (\(z, dfUp) ->
                         (∀) [ (x, dfUp') | ((x,z'), dfUp') <- Map.assocs sinkDFUp, z == z'] (\(x, dfUp') ->
                           dfUp == dfUp'
                         )
                       ),
    testProperty   "sinkDFUp              == sinkDFUpDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFUp                g ==
                       PDF.sinkDFUpDef             g,
    testProperty   "sinkDFLocalViaSinkdoms == sinkDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFLocalViaSinkdoms  g ==
                       PDF.sinkDFLocalDef          g,
    testProperty   "sinkDFLocal            == sinkDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.sinkDFLocal             g ==
                       PDF.sinkDFLocalDef          g,
    testProperty   "sinkDFcd              == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFcd         g ==
                       SNM.nticdF3          g,
    testProperty   "isinkdomTwoFingercd   == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.isinkdomTwoFingercd g ==
                       SNM.nticdF3             g,
    testProperty   "sinkDFFromUpLocalDefcd== nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFFromUpLocalDefcd  g==
                       SNM.nticdF3                 g,
    testProperty   "sinkDFFromUpLocalcd   == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFFromUpLocalcd     g ==
                       SNM.nticdF3                 g,
    testProperty   "sinkDFF2cd            == nticdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.sinkDFF2cd       g ==
                       SNM.nticdF3          g
  ]




insensitiveDomTests = testGroup "(concerning nontermination-insensitive control dependence via dom-like frontiers )" $
  [  testCase    ( "idomToDFFast _ isinkdom == sinkDF _ for " ++ exampleName)
            $       let isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g isinkdom ==
                       PDF.sinkDF       g) @? ""
  | (exampleName, g) <- interestingIsinkdomTwoFinger
  ] ++
  [  testCase    (  "sinkDFLocal == sinkDFLocalDef for " ++ exampleName)
            $          PDF.sinkDFLocal    g ==
                       PDF.sinkDFLocalDef g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "sinkDFFromUpLocalDefViaSinkdoms == sinkDF for " ++ exampleName)
            $          PDF.sinkDFFromUpLocalDefViaSinkdoms g ==
                       PDF.sinkDF                          g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "sinkDFUpGivenXViaMdoms == sinkDFUpGivenX for " ++ exampleName)
            $          PDF.sinkDFUpGivenXViaSinkdoms     g ==
                       PDF.sinkDFUpGivenX             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "sinkDFUpDefViaMdoms == sinkDFUpDef for " ++ exampleName)
            $            PDF.sinkDFUpDefViaSinkdoms     g ==
                         PDF.sinkDFUpDef             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ isinkdom == sinkDF _ for " ++ exampleName)
            $       let isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                       PDF.idomToDFFast g isinkdom ==
                       PDF.sinkDF       g) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ isinkdom == idomToDF _ isinkdom for " ++ exampleName)
            $       let isinkdom1 = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdom2 = PDOM.isinkdomOfTwoFinger8      g
                    in (∀) [isinkdom1, isinkdom2] (\isinkdom ->
                        PDF.idomToDFFast g isinkdom ==
                        PDF.idomToDF     g (fromSuccMap isinkdom :: Gr () ())) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "DF of isinkdom Cycles are all the same for " ++ exampleName)
            $       let isinkdom = fromSuccMap $ PDOM.TRANS.isinkdomOfSinkContraction g :: Gr () ()
                        df    = PDF.idomToDF g isinkdom
                        idomSccs = scc isinkdom
                        cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                    in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "sinkDFGraphP              ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFGraphP p            == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFFromUpLocalGraphP   ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFFromUpLocalGraphP p == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFFromUpLocalDefGraphP==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFFromUpLocalDefGraphP p
                                              ==
                                                 PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  [  testCase    ( "sinkDFF2GraphP            ==       nticdF3GraphP for " ++ exampleName)
            $ PROG.sinkDFF2GraphP p          == PROG.nticdF3GraphP p @? ""
  | (exampleName, p) <- testsuite
  ] ++
  []



