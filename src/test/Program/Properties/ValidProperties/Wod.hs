{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Wod where


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
import Util(sampleFrom, invert'', moreSeeds, restrict, reachableFromTree, invert''', fromSet, toSet, isReachableFromTree, foldM1)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)



import qualified Data.Dequeue as Dequeue
import Data.Graph.Inductive.Query.DFS (reachable, dfs, rdfs)
import qualified Data.Graph.Inductive.Query.NTIODSlice as NTIODSlice
import qualified Data.Graph.Inductive.Query.LCA as LCA (lca)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (isinkdomOf, isinkdomOfGfp2, joinUpperBound, sinkdomOfJoinUpperBound, sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkdomNaiveGfp, sinkdomNaiveGfpFullTop, sinkdomOfisinkdomProperty, imdomOf, imdomOfLfp, mdomOf, mdomOfLfp, mdomNaiveLfp, mdomOfimdomProperty, onedomOf, mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, isinkdomOftwoFinger8Up,  imdomOfTwoFinger6, imdomOfTwoFinger7)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (noJoins, isinkDFTwoFinger)
import qualified Data.Graph.Inductive.Query.FCACD as FCACD (wccSlice, wdSlice, nticdNTIODViaWDSlice, wodTEILSliceViaBraunF2)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import qualified Data.Graph.Inductive.Query.PostDominance.GraphTransformations as PDOM.TRANS (isinkdomOfSinkContraction)
import qualified Data.Graph.Inductive.Query.Slices.GraphTransformations as SLICE.TRANS (
    nticdNTIODSliceViaCutAtRepresentatives, nticdNTIODSliceViaEscapeNodes, nticdNTIODSliceViaCutAtRepresentativesNoTrivial, nticdNTIODSliceViaChoiceAtRepresentatives
 )
import qualified Data.Graph.Inductive.Query.Slices.PostDominance as SLICE.PDOM (nticdNTIODSliceViaISinkDom, ntscdNTSODSliceViaIMDom)
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (
    nticdNTIODSlice, nticdSlice,  ntscdSlice,
    ntscdNTSODSliceViaNtscd, wodTEILSliceViaNticd,
    wccSliceViaNticd,
  )
import qualified Data.Graph.Inductive.Query.Slices.OrderDependence as SLICE.ODEP (
    nticdNTIODFastSlice, wodTEILPDomSlice, 
    ntiodFastPDomSimpleHeuristicSlice, ntiodFastSlice, nticdNTIODSlice, wodTEILSlice, ntscdDodSlice, ntscdNTSODSlice, ntscdNTSODFastPDomSlice, 
    wccSliceViaNticdNTIODPDomSimpleHeuristic, nticdNTIODPDomSimpleHeuristic,
  )
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (ntindDef, nticdViaSinkDom)
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, 
    nticdF3'dualWorkList, snmF3'dual,
    ntscdF4, ntscdF3, ntscdF4WorkList
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
    mustOfLfp, mustOfGfp, mmayOf, mmayOf', rotatePDomAround, Color(..), smmnFMustDod, smmnFMustWod, colorLfpFor, colorFor,
    smmnGfp, smmnLfp, fMust, fMustBefore, fMustNoReachCheck,
    dod, dodDef, dodFast, dodColoredDagFixed, dodColoredDagFixedFast,
    ntiod, ntiodFast, ntiodFastPDom, ntiodFastPDomSimpleHeuristic,  ntsod, ntsodFast, ntsodFastPDom, wodTEIL', wodTEIL'PDom, wodDef, wodFast, fMay, fMay'
  )
import qualified Data.Graph.Inductive.Query.NTICDUnused  as NTICDUnused (ntacdDef, wodMyEntryWodMyCDSlice, myCD, myCDFromMyDom, myDom, allDomNaiveGfp, ntiodFromMay, mayNaiveGfp, possibleIntermediateNodesFromiXdom, withPossibleIntermediateNodesFromiXdom)

wod        = defaultMain                               $ testGroup "wod"       [ mkTest [wodTests], mkProp [wodProps]]
wodX       = defaultMainWithIngredients [antXMLRunner] $ testGroup "wod"       [ mkTest [wodTests], mkProp [wodProps]]



wodProps = testGroup "(concerning weak order dependence)" [
    testProperty "nticdNTIODSlice ⊆ nticdNTIODSliceViaCutAtRepresentatives = nticdNTIODSliceViaCutAtRepresentativesNoTrivial ⊆ nticdNTIODSliceViaEscapeNodes ⊆ nticdNTIODSliceViaChoiceAtRepresentatives for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer0  = SLICE.NTICD.nticdNTIODSlice                        g
                    slicer1  = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentatives g
                    slicer1' = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentativesNoTrivial g
                    slicer2  = SLICE.TRANS.nticdNTIODSliceViaEscapeNodes          g
                    slicerNX = SLICE.TRANS.nticdNTIODSliceViaChoiceAtRepresentatives g
                    s0 = slicer0  ms
                    s1 = slicer1  ms
                    s1'= slicer1' ms
                    s2 = slicer2  ms
                    sNX= slicerNX ms
                    ok = s0 ⊆ s1
                       ∧ s1 == s1'
                       ∧ s1 ⊆ s2
                       ∧ s2 ⊆ sNX
                in -- (if Set.size s0 /= Set.size s1 ∨ Set.size s1 /= Set.size s2 then traceShow (Set.size ms, Set.size s0, Set.size s1, Set.size s2, ms, g) else id) $
                   -- (if Set.size s0 < Set.size sNX then trace ((show $ length $ nodes $ g) ++ ",\t" ++ (show $ Set.size ms) ++ ",\t" ++ (show $ Set.size s0) ++ ",\tGO,\t" ++ (show $ Set.size s1) ++ ",\t" ++ (show $ Set.size s1') ++ ",\t" ++ (show $ Set.size s2) ++ ",\t" ++ (show $ Set.size sNX)) else id) $
                  (if ok then id else traceShow (g, ms)) ok,
    testPropertySized 60 "nticdNTIODSlice ⊆ nticdNTIODSliceViaCutAtRepresentatives = nticdNTIODSliceViaCutAtRepresentativesNoTrivial ⊆ nticdNTIODSliceViaEscapeNodes ⊆ nticdNTIODSliceViaChoiceAtRepresentatives for random slice-criteria of random size and CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (max 2 $ seed1 `mod` n)]
                    slicer0  = SLICE.NTICD.nticdNTIODSlice                        g
                    slicer1  = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentatives g
                    slicer1' = SLICE.TRANS.nticdNTIODSliceViaCutAtRepresentativesNoTrivial g
                    slicer2  = SLICE.TRANS.nticdNTIODSliceViaEscapeNodes          g
                    slicerNX = SLICE.TRANS.nticdNTIODSliceViaChoiceAtRepresentatives g
                    s0 = slicer0  ms
                    s1 = slicer1  ms
                    s1'= slicer1' ms
                    s2 = slicer2  ms
                    sNX= slicerNX ms
                    ok = s0 ⊆ s1
                       ∧ s1 == s1'
                       ∧ s1 ⊆ s2
                       ∧ s2 ⊆ sNX
                in -- (if Set.size s0 /= Set.size s1 ∨ Set.size s1 /= Set.size s2 then traceShow (Set.size ms, Set.size s0, Set.size s1, Set.size s2, ms, g) else id) $
                   -- (if Set.size s0 < Set.size sNX then trace ((show $ length $ nodes $ g) ++ ",\t" ++ (show $ Set.size ms) ++ ",\t" ++ (show $ Set.size s0) ++ ",\tGO,\t" ++ (show $ Set.size s1) ++ ",\t" ++ (show $ Set.size s1') ++ ",\t" ++ (show $ Set.size s2) ++ ",\t" ++ (show $ Set.size sNX)) else id) $ 
                   (if ok then id else traceShow (g, ms)) ok,
    testProperty "wccSlice == wccSliceViaNticd for random slice-criteria of random size and CFG-shaped graphs"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
    -- testProperty "wccSlice == wccSliceViaNticd for random slice-criteria of random size and CFG-shaped graphs with exit->entry edge"
    -- $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
    --             let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
    --                 [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
    --                 g = insEdge (exit, entry, ()) generatedGraph
                    n  = length $ nodes g
                    ms = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    wccslicer   = FCACD.wccSlice g
                    wccslicer'  = SLICE.NTICD.wccSliceViaNticd g
                in wccslicer ms == wccslicer'  ms,
    testProperty "wccSlice == * for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
                    n  = length $ nodes g
                    ms
                      | n == 0 = []
                      | n /= 0 = List.nub [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    msS = Set.fromList ms

                    wccslicer   = FCACD.wccSlice g
                    wccslicer'  = SLICE.NTICD.wccSliceViaNticd g

                    fromMs =  dfs ms g
                    g'    = subgraph fromMs g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g'

                    toMs   = rdfs ms g
                    g''    = foldr (flip delSuccessorEdges) (subgraph fromMs $ subgraph toMs g) ms
                    nticdslicer = SLICE.NTICD.nticdSlice g''

                in   wccslicer msS == wodslicer   msS
                   ∧ wccslicer msS == nticdslicer msS
                   ∧ wccslicer msS == wccslicer'  msS,
    testProperty "nticdNTIODSlice == nticdNTIODSliceViaISinkDom  for random slice-criteria of random size, and CFG-shaped graphs"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.NTICD.nticdNTIODSlice               g
                    slicer2  = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g
                in   slicer1  ms == slicer2  ms,
    testProperty "nticdNTIODSlice == nticdNTIODSliceViaISinkDom  for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.NTICD.nticdNTIODSlice              g
                    slicer2  = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g
                    slicer1' = SLICE.NTICD.nticdNTIODSlice              g'
                    slicer2' = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g'
                in   slicer1  ms == slicer2  ms
                   ∧ slicer1' ms == slicer2' ms,
    testPropertySized 20 "nticdNTIODSlice == nticdNTIODSliceViaISinkDom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    slicer1  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    slicer2  = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g
                    slicer1' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    slicer2' = SLICE.PDOM.nticdNTIODSliceViaISinkDom    g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let ms = Set.fromList [m1, m2] in -- -} (∀) (nodes g) (\m3 -> let ms = Set.fromList [m1, m2, m3] in 
                       slicer1  ms == slicer2  ms
                     ∧ slicer1' ms == slicer2' ms
                   ))),
      testProperty  "sinkdoms' (slicer' m) = ∅"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        m0S
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    -- in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->   (∀) (nodes g) (\m3 -> let m0S = Set.fromList [m1, m2, m3] in
                    in 
                           let m0s = Set.toList m0S
                               g' = foldr (flip delSuccessorEdges) g m0s
                               slicer' = SLICE.NTICD.nticdSlice g'
                               sinkdoms' = PDOM.sinkdomsOf g'
                               sinkdom'  = PDOM.sinkdomOfGfp g'
                           in  (∀) (slicer' m0S) (\n -> Set.null $ sinkdoms' ! n)
                             ∧ (∀) (slicer' m0S) (\n ->            sinkdom'  ! n == Set.fromList [n])
                        -- )))
                    ,
    testProperty "nticdNTIODSlice == nticdNTIODSliceViaNticd for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    slicer2  = SLICE.NTICD.nticdNTIODSlice              g
                    slicer1' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    slicer2' = SLICE.NTICD.nticdNTIODSlice              g'
                in   slicer1  ms == slicer2  ms
                   ∧ slicer1' ms == slicer2' ms,
    testPropertySized 40 "sinkdoms g' => sinkdoms g"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    sinkdoms = PDOM.sinkdomsOf g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  let m0S = Set.fromList [m1, m2] in -- (∀) (nodes g) (\m3 -> let m0S = Set.fromList [m1, m2, m3] in
                     let  m0s = Set.toList m0S
                          toM0s = rdfs m0s g
                          g' = foldr (flip delSuccessorEdges) g m0s
                          sinkdoms' = PDOM.sinkdomsOf g'
                     in   (sinkdoms' ⊑ sinkdoms)
                   )),
      testProperty  "isinkdoms path order"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        isinkdoms = PDOM.sinkdomsOf g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) (isinkdoms ! n) (\m1 ->  (∀) (ms) (\m2 ->
                         let ok  =   ((m1,m2) ∈ must ! n)
                                   ∨ (m1 ∈ sinkdom ! m2 ∧  m2 ∈ sinkdom ! m1  ∧  m2 ∈ isinkdoms ! n)
                                   ∨ (n == m2)
                         in (if ok  then id else traceShow (g, n, m1, m2)) ok
                       ))),
      testProperty  "sinkdom path order"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        -- isinkdoms = NTICD.sinkdomsOf g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) ms (\m1 ->  (∀) (ms) (\m2 ->
                         let ok  =   ((m1,m2) ∈ must ! n)
                                   ∨ ((m2,m1) ∈ must ! n)
                                   ∨ (m1 ∈ sinkdom ! m2 ∧  m2 ∈ sinkdom ! m1)
                         in (if ok  then id else traceShow (g, n, m1, m2)) ok
                       ))),
      testProperty  "sinkdom path order for CFG with unique exit node"
                $ \(SIMPLECFG(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        -- isinkdoms = NTICD.sinkdomsOf g
                    in (∀) (Map.assocs sinkdom) (\(n,ms) -> (∀) ms (\m1 ->  (∀) (ms) (\m2 ->
                         let ok  =   ((m1,m2) ∈ must ! n)
                                   ∨ ((m2,m1) ∈ must ! n)
                                   ∨ (m1 == m2)
                         in (if ok  then id else traceShow (g, n, m1, m2)) ok
                       ))),
      testPropertySized 25  "nticd nticdNTIOD Proof"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                        sinkdom = PDOM.sinkdomOfGfp g
                        isinkdoms = PDOM.sinkdomsOf g
                        ntind = NTICD.ntindDef g
                    in (∀) (nodes g) (\m0 -> (∀) (nodes g) (\n0 -> (∀) (nodes g) (\n' -> (∀) (nodes g) (\n -> (∀) (suc g n) (\x -> (∀) (suc g n) (\x' ->
                         let okn0m0 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must    ! x)
                                   ∧  (       n0      ∈ sinkdom ! x)
                                   ) →  (n0 ∈ sinkdom ! m0)
                             ok00 = (  True
                                   ∧  (Set.size (isinkdoms ! n) > 1)
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n /= m0)
                                   ) →  ((m0 ∈ ntind ! n)  ∧  (not $ m0 ∈ isinkdoms ! n))
                             ok0 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   -- ∧  (      n0 ∈ sinkdom ! m0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n /= m0)
                                   ) →  (m0 ∈ ntind ! n)
                             ok1 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n' ∈ isinkdoms ! n)
                                   ) →  (n' /= x)
                             ok2 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   ∧  (n' ∈ isinkdoms ! n)
                                   ) →  (n' /= n)
                             ok3 = (  True 
                                   ∧  (n /= n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n' ∈ isinkdoms ! n)
                                   ) →  (n0 ∈ sinkdom ! n')
                             ok4 = (  True 
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n')
                                   ∧  (n' ∈ sinkdom ! n)
                                   ∧  (n' /= n)
                                   ) →  (n' /= x)
                             ok5 = (  True
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (n0 ∈ sinkdom ! n)
                                   ∧  (n' ∈ sinkdom ! n)
                                   ∧  (n /= n0)
                                   -- ∧  (n' /= x)
                                   ∧  (n' /= n)
                                   ) → ((not $ (n', m0) ∈ must ! x) ∧  (n' /= x))
                             ok6 = (  True
                                   ∧  (not $ (n0, m0) ∈ must ! x )
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   -- ∧  (not $ m0 ∈ sinkdom ! n0)
                                   ∧  (      (n', m0) ∈ must ! x)
                                   ∧  (      n' ∈ sinkdom ! x')
                                   ∧  (      n0 ∈ sinkdom ! x )
                                   ) → ( m0 ∈ sinkdom ! x' ∧  m0 ∈ sinkdom ! n' ∧ m0 ∈ sinkdom ! x)
                                     -- ) → ((not $ (n', m0) ∈ must ! x))
                             ok7 = (  True
                                   ∧  (      (n0, m0) ∈ must ! x')
                                   ∧  (         m0 ∈ sinkdom ! x')
                                   ) → ( m0 ∈ sinkdom ! n0)
                         in (if okn0m0 ∧ ok00 ∧ ok0 ∧ ok1 ∧ ok2 ∧ ok3 ∧ ok4 ∧ ok5 ∧ ok6 ∧ ok7  then id else traceShow (g, m0, n0, n', n, x, x')) (okn0m0 ∧ ok00 ∧ ok0 ∧ ok1 ∧ ok2 ∧ ok3 ∧ ok4 ∧ ok5 ∧ ok6 ∧ ok7 )
                       )))))),
    testProperty   "ntiod size for looping ladders"
    $ \(size :: Int) ->
                let msum = Map.foldr (\ns s -> Set.size ns + s) 0

                    n0 = (abs size) `div` 2
                    g = fullLadder n0  :: Gr () ()
                    n = length $ nodes g
                    ntiod = assert (n == 2*n0 + 3) $
                            ODEP.ntiodFastPDomSimpleHeuristic g
                    even = [ n | n <- nodes g, n `mod` 2 == 0]
                    odd  = [ n | n <- nodes g, n `mod` 2 /= 0]
                in -- traceShow (n, msum ntiod, sum [ (n `div` 2) * ((m1+1) `div` 2) | m1 <- odd], ((((n-1) `div` 2 + 1  ) * (n - 1)) `div` 4  ) * (n `div` 2))   $
                     (∀) odd (\m1 ->
                       let left  = Set.fromList [ (m1,m2,n) | m2 <- even, n <- Set.toList $ ntiod ! (m1,m2)  ]
                           right = Set.fromList [ (m1,m2,n) | m2 <- even, n <- even, n < m1, n /= m2 ]
                           size = (n `div` 2) * ((m1+1) `div` 2)
                       in   (left == right)
                          ∧ (Set.size right == size)
                     )
                   ∧ (msum ntiod >= ((((n-1) `div` 2 + 1  ) * (n - 1)) `div` 4  ) * (n `div` 2)),
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
                   ),
      testPropertySized 40  "sinkdomOfLfp ms                 == (∀) mustOfLfp  property"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  let m0S = Set.fromList [m1, m2] in
                           let m0s = Set.toList m0S
                               toM0s = rdfs m0s g
                               g' = foldr (flip delSuccessorEdges) g m0s
                               sinkdom' = PDOM.sinkdomOfGfp g'
                           in (∀) (nodes g) (\n -> (∀) m0s (\m0 -> (∀) (nodes g) (\m ->
                                let ok = (m == m0)  ∨  ((m ∈ sinkdom' ! n) → ((m,m0) ∈ must ! n))
                                in (if ok then id else traceShow (g, m0S, n, m, m0)) ok
                           )))
                       )),
    testProperty "nticdNTIOD == nticdMyViaNticd properties"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g    = generatedGraph
                    trcG = trc g
                    nticd = NTICD.nticdViaSinkDom g
                    sinkdom = PDOM.sinkdomOfGfp g
                    ntiod =  ODEP.ntiodFastPDomSimpleHeuristic g
                    must = ODEP.mustOfGfp g
                    slicer  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    nticdslicer = SLICE.NTICD.nticdSlice g
                    sinkdoms = PDOM.sinkdomsOf g
                    onPathBetween ss ts = fwd
                      where gTs = foldr (flip delSuccessorEdges) g ts
                            fwd = Set.fromList $  dfs ss gTs
                    m0S
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                     where n    = length $ nodes g
                in
                -- in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let m0S = Set.fromList [m1, m2] in  -- -} (∀) (nodes g) (\m3 -> (∀) (nodes g) (\m4 -> let m0S = Set.fromList [m1, m2, m3, m4] in
                     let  m0s = Set.toList m0S
                          toM0s = rdfs m0s g
                          g' = foldr (flip delSuccessorEdges) g m0s
                          trcG' = trc g'
                          nticd' = NTICD.nticdViaSinkDom g'
                          nticd'slicer = SLICE.NTICD.nticdSlice g'
                          sinkdom' = PDOM.sinkdomOfGfp g'
                          sinkdoms' = PDOM.sinkdomsOf g'
                          onPathBetween' ss ts = fwd
                            where g'Ts = foldr (flip delSuccessorEdges) g' ts
                                  fwd = Set.fromList $  dfs ss g'Ts
                          s = slicer m0S
                     in   (sinkdom' ⊑ sinkdom)
                        ∧ (∀) s (\n -> (n ∈ m0S)   ∨   (∃) (nticd' ! n) (\n0 -> n0 ∈ s ∧  n0 /= n) ∧ (∀) (nticd' ! n  ∩ s) (\n0 -> if n0 == n then True else
                             n0 ∈ s   ∧  ((n0 ∈ nticd ! n)  ∨  (   True 
                                                                  ∧ (∀) (suc g n) (\x -> n0 ∈ sinkdom ! x)
                                                                  ∧ (n0 ∈ sinkdom ! n)
                                                                  -- ∧ (∀) m0S (\m0 ->  m0 ∈ sinkdom ! n0)
                                                                  ∧ (∃) (suc g n) (\x -> (∃) m0S (\m0 ->
                                                                        m0 /= n0   ∧  n0 ∈ sinkdom ! m0
                                                                      ∧ x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG n0)
                                                                      ∧ (not $ (n0, m0) ∈ must ! x )
                                                                    ))
                                                                  ∧ (∀) (suc g n) (\x -> (∀) m0S (\m0 ->
                                                           let ok = (
                                                                        m0 /= n0   ∧  n0 ∈ sinkdom ! m0
                                                                      ∧ x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG n0)
                                                                      ∧ (not $ (n0, m0) ∈ must ! x )
                                                                    ) → (
                                                                        ((      m0 ∈ sinkdom ! n0)  ∧  (n ∈ ntiod ! (n0,m0)                )                                           )
                                                                      ∨ ((not $ m0 ∈ sinkdom ! n0)  ∧  (n ∈ nticdslicer (Set.fromList [m0]))
                                                                                                    ∧  ((n == m0) ∨ 
                                                                                                        (   (      m0 ∈ onPathBetween [x]       (Set.toList   $ sinkdoms ! n)) 
                                                                                                          ∧ (not $ m0 ∈                         (Set.insert n $ sinkdoms ! n)) ))      )
                                                                    )
                                                           in (if ok then id else traceShow (g,  n,  n0,  x,  m0)) ok
                                                                    ))
                                                               )
                                         )
                          ))
                        ∧ (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m ->
                            let ok = (m ∈ sinkdom' ! n) ∨ ((∃) m0S (\m0 ->  m0 /= m  ∧  m ∈ sinkdom ! m0  ∧  n `elem` (pre trcG' m0)  ∧  m0 `elem` (pre trcG m)  ∧  (not $ (m, m0) ∈ must ! n )))
                            in (if ok then id else traceShow (g, m0S, n, m)) ok
                          ))
                        ∧ (∀) (Map.assocs sinkdom) (\(n, ms) -> (∀) ms (\m -> let { g'' = delSuccessorEdges g' m ; reachN = reachable n g'' } in 
                            let ok = (m ∈ sinkdom' ! n) ∨ ((∃) m0S (\m0 ->  m0 /= m  ∧  m0 `elem` reachN))
                            in (if ok then id else traceShow (g, m0S, n, m)) ok
                          ))
                        ∧ (∀) (Map.assocs nticd') (\(n, ms) -> (∀) ms (\m ->
                          let ok =   ((m ∈ nticd ! n)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (not $ m ∈ sinkdom' ! x)))
                                   ∧ ((m ∈ nticd ! n)  ∨  (m ∈ sinkdom ! n))
                                   ∧ ((m ∈ nticd ! n)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (∃) m0S (\m0 ->  m0 /= m  ∧  m ∈ sinkdom ! m0  ∧  x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG m) ∧  (not $ (m, m0) ∈ must ! n ) ) ))
                          in (if ok then id else traceShow (g, m0S, n, m)) ok
                        ))
                        ∧ (∀) (Map.assocs nticd) (\(n, ms) -> (∀) ms (\m ->
                          let ok =   ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (not $ m ∈ sinkdom' ! x)))
                                   ∧ ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (∀) (suc g n) (\x -> not $ m ∈ sinkdom' ! x))
                                   ∧ ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (sinkdom' ! n == Set.fromList [n]))
                                   ∧ ((m ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨  (∃) (suc g n) (\x ->  (m ∈ sinkdom ! x) ∧ (∃) m0S (\m0 ->  m0 /= m  ∧  m ∈ sinkdom ! m0  ∧  x `elem` (pre trcG m0)  ∧  m0 `elem` (pre trcG m) ∧  (not $ (m, m0) ∈ must ! n ) ) ))
                          in (if ok then id else traceShow (g, m0S, n, m)) ok
                        ))
                        ∧ (∀) s (\n -> (n ∈ m0S)
                                     ∨ (∃) s (\m1 -> (∃) s (\m2 -> m1 /= m2  ∧  n /= m2  ∧  n ∈ ntiod ! (m1,m2))) ∧  (∀) s (\m1 -> (∀) s (\m2 -> if m1 == m2  ∨  n == m2  ∨  (not $ n ∈ ntiod ! (m1,m2)) then True else
                                         m1 ∈ s   ∧  m2 ∈ s   ∧
                                           (∃) m0S (\m0 ->          n `elem` (pre trcG' m0))
                                         ∧
                                           (∀) m0S (\m0 -> if not $ n `elem` (pre trcG' m0) then True else
                                            let ok = n ∈ nticd'slicer (Set.fromList [m0]) in (if ok then id else traceShow (g, m0s, n,  m1,  m2, m0)) ok
                                           )
                                         ∧ ( (m1 ∈ nticd' ! n) ∨ (∀) (suc g n) (\x -> not $ m1 ∈ sinkdom' ! x) ∧ (∃) (suc g n) (\x -> (m1,m2) ∈ must ! x) ∧ (∀) (suc g n) (\x -> if not $ (m1,m2) ∈ must ! x then True else
                                             let ok = x /= m1 ∧ (∃) (reachable x (delSuccessorEdges g' m1)) (\m0 -> m0 ∈ m0S ∧ m0 /= m1)in (if ok then id else traceShow (g, m0s, n,  m1,  m2, x)) ok
                                           ))
                                         ∧ let ok =  not $ m1 ∈ sinkdom' ! m2  in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                         -- ∧ let ok =  (n ∈ nticd'slicer (Set.fromList [m2]))  ∨  (∃) m0S (\m0 -> (m0 /= m1 ∧ n ∈ ntiod ! (m1,m0)))  in (if ok then id else traceShow ("lol", g, m0s, n,  m1,  m2)) ok
                                         ∧ let ok = Set.null $ sinkdoms' ! n in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                         ∧ let ok = sinkdom' ! n == Set.fromList [n] in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                         ∧ let ok = False
                                                  ∨ ( (      m2 ∈ m0S) ∧ True)
                                                  ∨ ( (not $ m2 ∈ m0S) ∧ True)
                                           in (if ok then id else traceShow (g, m0s, n,  m1,  m2)) ok
                                       ))
                                     ∨ (∃) (nticd ! n) (\n0 -> n0 ∈ s ∧  n0 /= n) ∧ (∀) (nticd ! n  ∩ s) (\n0 -> if n0 == n then True else
                                         (Set.null $ sinkdoms' ! n) ∧ (sinkdom' ! n == Set.fromList [n]) ∧
                                         n0 ∈ s   ∧  ((n0 ∈ nticd' ! n)  ∨  (n ∈ m0S)  ∨
                                                                (   True 
                                                                  ∧ (∀) (suc g n) (\x -> not $ n0 ∈ sinkdom' ! x)
                                                                  ∧ (sinkdom' ! n == Set.fromList [n])
                                                                  ∧ (Set.null $ sinkdoms' ! n)
                                                                  ∧ (∃) (suc g n) (\x -> (n0 ∈ sinkdom ! x)  ∧  (∃) m0S (\m0 ->
                                                                        m0 /= n0   ∧  m0 `elem`  reachable x (delSuccessorEdges g' n0)
                                                                    ))
                                                                  ∧ (∀) (suc g n) (\x -> if (not $ n0 ∈ sinkdom ! x) then True else (∀) m0S (\m0 ->
                                                           let ok = (
                                                                        m0 /= n0   ∧  m0 `elem`  reachable x (delSuccessorEdges g' n0)
                                                                    ) → ( True
                                                                      ∧ (n ∈ nticd'slicer (Set.fromList [m0]))
                                                                      ∧ ((n == m0) ∨ 
                                                                          (   (      m0 ∈ onPathBetween' [x]      (Set.toList   $ sinkdoms' ! n)) 
                                                                            ∧ (not $ m0 ∈                         (Set.insert n $ sinkdoms' ! n)) ))
                                                                    )
                                                           in (if ok then id else traceShow (g, m0s, n,  n0,  x,  m0)) ok
                                                                    ))
                                                               )
                                                     )
                                     )
                           )
                   -- )))),
                   ,
    testPropertySized 25 "nticdNTIODSlice == nticdNTIODSliceViaNticd"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    slicer1  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    slicer2  = SLICE.NTICD.nticdNTIODSlice              g
                    slicer1' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    slicer2' = SLICE.NTICD.nticdNTIODSlice              g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let ms = Set.fromList [m1, m2] in -- -} (∀) (nodes g) (\m3 -> let ms = Set.fromList [m1, m2, m3] in 
                       slicer1  ms == slicer2  ms
                     ∧ slicer1' ms == slicer2' ms
                   ))),
      testPropertySized 30  "nticdNTIODSlice == nticdNTIODSliceViaNticd even when using data dependencies"
                $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) ->
                   let g = generatedGraph
                       ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                         where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)
                       ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                       nticd = PDF.isinkDFTwoFinger g
                       ntiod =  ODEP.ntiodFastPDomSimpleHeuristic g
                       slicer = combinedBackwardSlice (ddep ⊔ nticd) ntiod 
                   in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 ->
                        let ms  = [m1, m2, m3]
                            msS = Set.fromList ms
                            g' = foldr (flip delSuccessorEdges) g ms
                            nticd' = PDF.isinkDFTwoFinger g'
                            empty = Map.empty
                            slicer' = combinedBackwardSlice (ddep ⊔ nticd') empty
                        in slicer msS == slicer' msS
                      ))),
      testProperty "nticdNTIODSlice == nticdNTIODSliceViaNticd even when using data dependencies, for random slice-criteria of random size "
                $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) seed1 seed2->
                   let g = generatedGraph
                       n  = length $ nodes g
                       ms
                         | n == 0 = []
                         | n /= 0 = [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                       ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                         where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)
                       ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                       nticd = PDF.isinkDFTwoFinger g
                       ntiod =  ODEP.ntiodFastPDomSimpleHeuristic g
                       slicer = combinedBackwardSlice (ddep ⊔ nticd) ntiod
                       
                       msS = Set.fromList ms
                       g' = foldr (flip delSuccessorEdges) g ms
                       nticd' = PDF.isinkDFTwoFinger g'
                       empty = Map.empty
                       slicer' = combinedBackwardSlice (ddep ⊔ nticd') empty
                   in slicer msS == slicer' msS,
    testProperty "wodTEIL ⊑ ntiod ∪ nticd*"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    wodTEIL'    = ODEP.wodTEIL'PDom g
                    ntiod       = ODEP.ntiodFastPDomSimpleHeuristic g
                    nticdslicer = SLICE.NTICD.nticdSlice g
                in (∀) (Map.assocs wodTEIL') (\((m1,m2), ns) ->  (∀) ns (\n ->
                       n ∈ ntiod ! (m1,m2)                 ∨  n ∈ ntiod ! (m2,m1)
                    ∨  n ∈ nticdslicer (Set.fromList [m1]) ∨  n ∈ nticdslicer (Set.fromList [m2])
                   )),
      testProperty  "sinkdomOfLfp m2                 == mustOfLfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfGfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               sinkdom2 = PDOM.sinkdomOfGfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ sinkdom2 ! n)
                           ))
                       ),
    testProperty "unique node property for nticdNTIODPDomSimpleHeuristic"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    ntiodslicer   = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    wodteilslicer = SLICE.ODEP.wodTEILPDomSlice g
                    property1 s s' g' unique = (∀) s' (\n -> (length (unique ! n) <= 1))
                    property2 s s' g' unique = (∀) s' (\n -> (∀) (suc g n) (\n' ->
                                                 (n' ∈ s) ∨ (unique ! n == unique ! n')
                                               ))
                    uniqueOf s s' g' = Map.fromList [ (n, [ m | m <- reachable n g', m ∈ s]) | n <- Set.toList s' ]

                in   (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       let ms = Set.fromList [m1,m2]
                           s  = ntiodslicer ms
                           s' = Set.fromList (nodes g) ∖ s
                           g' = efilter ((\(n,m,_) -> n ∈ s')) g
                           unique = uniqueOf s s' g'
                       in   property1 s s' g' unique
                          ∧ property2 s s' g' unique
                          ∧ (∀) s (\n -> n ∈ ms  ∨
                              let sn  = Set.delete n s
                                  sn' = Set.insert n s'
                                  gn' = efilter ((\(n,m,_) -> n ∈ sn')) g
                                  uniquen = uniqueOf sn sn' gn'
                              in  (not $ property1 sn sn' gn' uniquen)
                                ∨ (not $ property2 sn sn' gn' uniquen)
                           )
                     ))
                   ∧ (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       let ms = Set.fromList [m1,m2]
                           s  = wodteilslicer ms
                           s' = Set.fromList (nodes g) ∖ s
                           g' = efilter ((\(n,m,_) -> n ∈ s')) g
                           unique = uniqueOf s s' g'
                       in   property1 s s' g' unique
                          ∧ (∀) s (\n -> n ∈ ms  ∨
                              let sn  = Set.delete n s
                                  sn' = Set.insert n s'
                                  gn' = efilter ((\(n,m,_) -> n ∈ sn')) g
                                  uniquen = uniqueOf sn sn' gn'
                              in  (not $ property1 sn sn' gn' uniquen)
                           )
                     )),
    testPropertySized 40 "noJoins mmay'"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (∀) (nodes g) (\m ->
                         PDF.noJoins g $ ODEP.mmayOf' g m
                       ),
    testProperty "nticdNTIODPDomSimpleHeuristic == nticdNTIODViaWDSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    ntiodteilslicer  = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g
                    wdslicer         = FCACD.nticdNTIODViaWDSlice          g
                    ntiodteilslicer' = SLICE.ODEP.nticdNTIODPDomSimpleHeuristic g'
                    wdslicer'        = FCACD.nticdNTIODViaWDSlice          g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       ntiodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ ntiodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testPropertySized 30 "wodTEILSlice  == wodTEILSliceViaBraunF2"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice           g
                    wdslicer         = FCACD.wodTEILSliceViaBraunF2 g
                    wodteilslicer'   = SLICE.ODEP.wodTEILSlice           g'
                    wdslicer'        = FCACD.wodTEILSliceViaBraunF2 g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> if m1 == m2 then True else
                       wodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ wodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testPropertySized 40 "wodTEILSlice  == wdSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice g
                    wdslicer         = FCACD.wdSlice      g
                    wodteilslicer'   = SLICE.ODEP.wodTEILSlice g'
                    wdslicer'        = FCACD.wdSlice      g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       wodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ wodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testProperty "wodTEILSlice = wodTEILSliceViaNticd for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice g
                    wodteilslicer'   = SLICE.NTICD.wodTEILSliceViaNticd g
                in wodteilslicer ms  == wodteilslicer' ms,
    testProperty "wodTEILSliceViaNticd  == wdSlice for CFG-shaped graphs and randomly selected nodes"
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
                    wdslicer  = FCACD.wdSlice g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g
                in (∀) mss (\ms ->
                     wdslicer ms == wodslicer ms
                   ),
    testProperty "wodTEILSliceViaNticd  ∩ fromM == wccSlice for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g = generatedGraph
                    n  = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    fromMs = Set.fromList $ dfs (Set.toList ms) g
                    wccslicer  = FCACD.wccSlice g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g
                in wccslicer ms == wodslicer ms ∩ fromMs,
    testProperty "wodTEILSliceViaNticd  == wdSlice for randomly selected nodes"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    nrSlices = 10
                    n = length $ nodes g
                    mss
                      | n == 0 = []
                      | n /= 0 = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    wdslicer  = FCACD.wdSlice g
                    wodslicer = SLICE.NTICD.wodTEILSliceViaNticd g
                in (∀) mss (\ms ->
                     wdslicer ms == wodslicer ms
                   ),
    testProperty "wodTEILSliceViaNticd  == wdSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    wodteilslicer    = SLICE.NTICD.wodTEILSliceViaNticd g
                    wdslicer         = FCACD.wdSlice      g
                    wodteilslicer'   = SLICE.NTICD.wodTEILSliceViaNticd g'
                    wdslicer'        = FCACD.wdSlice      g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                       wodteilslicer  (Set.fromList [m1, m2]) == wdslicer  (Set.fromList [m1, m2])
                     ∧ wodteilslicer' (Set.fromList [m1, m2]) == wdslicer' (Set.fromList [m1, m2])
                   )),
    testProperty "wccSliceViaNticdNTIODPDomSimpleHeuristic  == wccSlice for randomly selected nodes"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                    wccSlicer  = FCACD.wccSlice g
                    wccSlicer' = SLICE.ODEP.wccSliceViaNticdNTIODPDomSimpleHeuristic g
                in wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2]),
    testPropertySized 40 "wccSliceViaNticdNTIODSliceSimple  == wccSlice for randomly selected nodes"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                    wccSlicer  = FCACD.wccSlice g
                    wccSlicer' = NTIODSlice.wccSliceViaNticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g
                in -- traceShow (length $ nodes g) $
                   wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2]),
    testPropertySized 70 "wccSliceViaNticdNTIODSliceSimple  == wccSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                    wccSlicer  = FCACD.wccSlice g
                    wccSlicer' = NTIODSlice.wccSliceViaNticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g
                in wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2]),
    testPropertySized 70 "wccSliceViaNticdNTIODSliceSimple  == wccSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g   =      generatedGraph
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                     let wccSlicer  = FCACD.wccSlice g
                         wccSlicer' = NTIODSlice.wccSliceViaNticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g
                     in wccSlicer' (Set.fromList [m1, m2]) == wccSlicer (Set.fromList [m1, m2])
                   )),
    testPropertySized 40 "wodTEILSlice g ms = nticdNTIODFastSlice g{ n | n ->* ms} ms"
    $ \(ARBITRARY(generatedGraph)) ->
                let g   =      generatedGraph
                    rev = grev generatedGraph
                    wodteilslicer    = SLICE.ODEP.wodTEILSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                     let g' = subgraph (List.nub $ (reachable m1 rev) ++ (reachable m2 rev)) g
                         nticdntiodslicer  = SLICE.ODEP.nticdNTIODFastSlice g'
                     in wodteilslicer (Set.fromList [m1, m2]) == nticdntiodslicer (Set.fromList [m1, m2])
                   )),
    testProperty "wodTEILPDomSlice = wodTEILSliceViaNticd"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    nrSlices = 10
                    n = length $ nodes g
                    mss
                      | n == 0 = []
                      | n /= 0 = [ Set.fromList [m1, m2, m3] | (s1,s2,s3) <- zip3 (moreSeeds seed1 nrSlices) (moreSeeds seed2 nrSlices) (moreSeeds seed3 nrSlices),
                                                        let m1 = nodes g !! (s1 `mod` n),
                                                        let m2 = nodes g !! (s2 `mod` n),
                                                        let m3 = nodes g !! (s3 `mod` n)
                          ]
                    wodteilslicer    = SLICE.ODEP.wodTEILPDomSlice g
                    wodteilslicer'   = SLICE.NTICD.wodTEILSliceViaNticd g
                in (∀) mss (\ms ->
                     wodteilslicer ms  == wodteilslicer' ms
                   ),
    testPropertySized 60 "wodTEILPDomSlice g ms = nticdNTIODSliceSimple g{ n | n ->* ms} ms"
    $ \(ARBITRARY(generatedGraph)) ->
                let g   =      generatedGraph
                    rev = grev generatedGraph
                    wodteilslicer    = SLICE.ODEP.wodTEILPDomSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->
                     let g' = subgraph (List.nub $ (reachable m1 rev) ++ (reachable m2 rev)) g
                         nticdntiodslicer  = NTIODSlice.nticdNTIODSliceSimple NTIODSlice.cutNPasteIfPossible g'
                     in wodteilslicer (Set.fromList [m1, m2]) == nticdntiodslicer (Set.fromList [m1, m2])
                   )),
    testProperty "wodTEIL  in sinks via pdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = controlSinks g0
                in (∀) sinks (\sink ->
                     let g = subgraph sink g0
                         wodTEIL'  = ODEP.wodTEIL' g
                         condNodes = [ n | n <- sink, (length $ suc g n) > 1 ]
                     in wodTEIL' == (∐) [ Map.fromList [ ((m1,m2), ns), ((m2,m1), ns) ] 
                                                | m2 <- nodes g,
                                                  let pdom = PDOM.sinkdomOfGfp $ delSuccessorEdges g m2,
                                                  m1 <- nodes g,
                                                  m1 /= m2,
                                                  let ns = Set.fromList [ n | n <- condNodes, n /= m1, n /= m2, not $ (∀) (suc g n) (\x -> m1 ∈ pdom ! x), (∃) (suc g n) (\x ->  m1 ∈ pdom ! x) ]
                                        ]
                   ),
    testProperty "wodTEIL == ntiod in sink subgraphs"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = controlSinks g0
                in (∀) sinks (\sink ->
                     let g = subgraph sink g0
                         wodTEIL'  = ODEP.wodTEIL' g
                         ntiod     = ODEP.ntiodFast g
                         ntiodSym  = (∐) [ Map.fromList [ ((m1,m2), ns), ((m2,m1), ns) ] | ((m1,m2),ns) <- Map.assocs ntiod ]
                     in wodTEIL' == ntiodSym
                   ),
    testPropertySized 40 "lfp fMay                 == lfp fMay'"
    $ \(ARBITRARY(g)) ->
                    let lfp      = ODEP.smmnLfp g ODEP.fMay
                        lfp'     = ODEP.smmnLfp g ODEP.fMay'
                    in  lfp                  == lfp',
    testPropertySized 40 "wodDef                    == wodFast"
    $ \(ARBITRARY(g)) ->
                    let wodDef   = ODEP.wodDef  g
                        wodFast  = ODEP.wodFast g
                    in  wodDef == wodFast,
    testPropertySized 60 "ntiod ⊑ wodTEIL'"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiod = ODEP.ntiod g
                        wodTEIL' = ODEP.wodTEIL' g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ns ⊑ (wodTEIL' ! (m1,m2))
                        ),
     testProperty  "ntiodFromSliceStep == ntiodFast"
     $ \(ARBITRARY(generatedGraph)) ->
                 let g0 = generatedGraph
                     sinks = controlSinks g0
                 in
                    (∀) sinks (\sink ->
                      let g = subgraph sink g0
                          ntiod = ODEP.ntiodFast g
                      in (∀) sink (\m1 -> (∀) sink (\m2 -> (m1 == m2) ∨
                           (NTIODSlice.ntiodFromSliceStep g m1 m2) == ntiod ! (m1,m2) ∪ ntiod ! (m2,m1)
                         ))
                    ),
    testPropertySized 60 "ntiodSlice == ntiodFastSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = controlSinks g0
                in
                   (∀) sinks (\sink ->
                     let g = subgraph sink g0
                         ntiodslicer     = NTIODSlice.ntiodSlice g
                         ntiodfastslicer = SLICE.ODEP.ntiodFastSlice g
                     in (∀) sink (\m1 -> (∀) sink (\m2 -> (m1 == m2) ∨
                          ntiodslicer m1 m2 == ntiodfastslicer (Set.fromList [m1, m2])
                        ))
                   ),
    testPropertySized 20 "ntiodSlice == ntiodFastPDomSimpleHeuristicSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodslicer     = NTIODSlice.ntiodSlice g
                    ntiodpdomslicer = SLICE.ODEP.ntiodFastPDomSimpleHeuristicSlice g
                in  (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                       ntiodslicer m1 m2 == ntiodpdomslicer (Set.fromList [m1, m2])
                    )),
     testProperty  "ntiodFromSimpleSliceStep cutNPasteIfPossible == ntiodFast"
     $ \(ARBITRARY(generatedGraph)) ->
                 let g = generatedGraph
                     ntiod = ODEP.ntiodFast g
                     ntiodslicestep = NTIODSlice.ntiodFromSimpleSliceStep NTIODSlice.cutNPasteIfPossible g
                 in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                           ntiodslicestep m1 m2 == ntiod ! (m1,m2) ∪ ntiod ! (m2,m1)
                    )),
    testProperty  "ntiodSliceSimple cutNPasteIfPossible == ntiodFastSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.cutNPasteIfPossible g
                    ntiodfastslicer   = SLICE.ODEP.ntiodFastSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                          ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodfastslicer (Set.fromList [m1, m2])
                   )),
    testPropertySized 15  "ntiodSliceSimple cutNPasteIfPossible == ntiodFastPDomSimpleHeuristicSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.cutNPasteIfPossible g
                    ntiodpdomslicer = SLICE.ODEP.ntiodFastPDomSimpleHeuristicSlice g
                in  (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                       ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodpdomslicer (Set.fromList [m1, m2])
                    )),
    testProperty  "ntiodFromSimpleSliceStep recompute == ntiodFast"
     $ \(ARBITRARY(generatedGraph)) ->
                 let g = generatedGraph
                     ntiod = ODEP.ntiodFast g
                     ntiodslicestep = NTIODSlice.ntiodFromSimpleSliceStep NTIODSlice.recompute g
                  in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                           ntiodslicestep m1 m2 == ntiod ! (m1,m2) ∪ ntiod ! (m2,m1)
                  )),
    testProperty  "ntiodSliceSimple recompute == ntiodFastSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.recompute g
                    ntiodfastslicer   = SLICE.ODEP.ntiodFastSlice g
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                          ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodfastslicer (Set.fromList [m1, m2])
                   )),
    testPropertySized 30  "ntiodSliceSimple recompute           == ntiodFastPDomSimpleHeuristicSlice for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodsimpleslicer = NTIODSlice.ntiodSliceSimple NTIODSlice.recompute g
                    ntiodpdomslicer = SLICE.ODEP.ntiodFastPDomSimpleHeuristicSlice g
                in  (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (m1 == m2) ∨
                       ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodpdomslicer (Set.fromList [m1, m2])
                    )),
    testPropertySized 40  "ntiodSliceSimple recompute           == ntiodSliceSimple recomputecutNPasteIfPossible for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    ntiodsimpleslicer  = NTIODSlice.ntiodSliceSimple NTIODSlice.recompute           g
                    ntiodsimpleslicer' = NTIODSlice.ntiodSliceSimple NTIODSlice.cutNPasteIfPossible g
                    m1 = (cycle $ nodes g) !! 32904
                    m2 = (cycle $ nodes g) !! 87653
                in  ntiodsimpleslicer (Set.fromList [m1, m2]) == ntiodsimpleslicer' (Set.fromList [m1, m2]),
    testPropertySized 60 "wodTEIL' == wodTeil'PDom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.wodTEIL'       g ==
                       ODEP.wodTEIL'PDom   g,
    testPropertySized 20 "dominator trees of (gN|{m |  m ->* n}) from dominator trees of gN in CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(g)) ->
                let nodeS = Set.fromList $ nodes g
                    [entry] = [ n | n <- nodes g, pre g n == [] ]
                    [exit]  = [ n | n <- nodes g, suc g n == [] ]
                    g' = insEdge (exit, entry, ()) g
                in (∀) (nodes g) (\n ->  n == entry   ∨   n == exit   ∨
                     let gN   = delSuccessorEdges g  n
                         g'N  = delSuccessorEdges g' n

                         gToN = subgraph keep' gN
                         
                         isinkdom  = PDOM.isinkdomOfTwoFinger8 gToN
                         isinkdom' = PDOM.isinkdomOfTwoFinger8 g'N
                         keep' = reachable n (grev gN)
                     in  isinkdom == restrict isinkdom' (Set.fromList keep')
                   ),
    testProperty  "cut and re-validate property in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = [ (g, gn, sink, ipdom, condNodes) | sink <-  controlSinks g0,
                                                let towardsSink = [ n | n <- nodes g0, (∃) sink (\s -> s `elem` reachable n g0) ],
                                                let g = subgraph towardsSink g0,
                                                let gn   = Map.fromList [ (n, delSuccessorEdges       g  n)    | n <- towardsSink ],
                                                let condNodes = Map.fromList [ (n, succs) | n <- towardsSink, let succs = suc g n, length succs > 1],
                                                let ipdom = Map.fromList [ (n, PDOM.isinkdomOfTwoFinger8 $ gn  ! n)    | n <- towardsSink ]
                            ]
                in (∀) sinks (\(g,gn,sink, ipdom, condNodes) ->
                            (∀) sink (\m -> 
                              (∀) sink (\n ->
                                   if (m == n) then True else
                                   let -- ipdomM'   = Map.union (Map.fromList [(n', Set.fromList [m]) | n' <- pre g m ]) (ipdom ! n)
                                       ipdomM''  = Map.insert m Set.empty (ipdom ! n)
                                       succs    = [ x | x <- suc g n, isReachableFromTree ipdomM'' m x]
                                       mz = foldM1 (LCA.lca (fmap fromSet ipdomM'')) succs
                                       ipdomM''' = Map.insert n (toSet mz) ipdomM''
                                  in if List.null succs then
                                       let nIsCond = Map.member n condNodes
                                           nonSinkCondNodes = Map.fromList [ (c, succs) | (c, succs) <- Map.assocs condNodes, c /= m]
                                           processed0 = Set.fromList [ x            | x <- nodes (gn ! m), m ∈ reachableFromTree ipdomM'' x]
                                           imdom0     = (if nIsCond then id else Map.insert n (fromSet $ Set.fromList $ suc (gn ! m) n)) $
                                                        Map.fromList [ (x, Nothing)   | x <- nodes (gn ! m), not $ x ∈ processed0, Map.member x nonSinkCondNodes] `Map.union` (fmap fromSet ipdomM'')
                                           worklist0  = Dequeue.fromList [ (x, succs) | x <- nodes (gn ! m), not $ x ∈ processed0, Just succs <- [Map.lookup x nonSinkCondNodes]]
                                           ipdomM'''' = -- traceShow (Map.size nonSinkCondNodes, Seq.length worklist0) $
                                                        fmap toSet $ PDOM.isinkdomOftwoFinger8Up (gn ! m) nonSinkCondNodes worklist0 processed0 (invert''' imdom0) imdom0
                                       in (∀) sink (\y ->
                                               reachableFromTree  ipdomM''''  y
                                            ⊇  reachableFromTree (ipdom ! m) y
                                          )
                                     else
                                       assert (mz /= Nothing) $
                                       (∀) sink (\y ->
                                             reachableFromTree  ipdomM'''  y
                                          ⊇  reachableFromTree (ipdom ! m) y
                                       )
                              ))
                   ),
    testProperty  "pmay properties in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = [ (g, sink, pdom, pmay, dom, condNodes) | sink <-  controlSinks g0,
                                                   let g = subgraph sink g0,
                                                   let gn   = Map.fromList [ (n, delSuccessorEdges       g  n)    | n <- sink ],
                                                   let gn'  = Map.fromList [ (n, delSuccessorEdges (grev g) n)    | n <- sink ],
                                                   let pdom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn  ! n)    | n <- sink ],
                                                   let  dom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn' ! n)    | n <- sink ],
                                                   let pmay = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn  ! n)    | n <- sink ],
                                                   let condNodes = Set.fromList [ n | n <- sink, length (suc g n) > 1]
                            ]
                in (∀) sinks (\(g,sink, pdom, pmay, dom, condNodes) ->
                            (∀) sink (\n -> (∀) condNodes (\c -> (∀) sink (\m2 -> if (c == m2) then True else
                               ((∀) (suc g c) (\x -> not $ m2 ∈ (pmay ! n) ! x))   ↔   ((n /= m2) ∧ (n /= c) ∧ (not $ m2 ∈ (pmay ! n) ! c))
                            )))
                   ),
    testProperty  "pdom swap properties in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g0 = generatedGraph
                    sinks = [ (sink, pdom, pmay, dom) | sink <-  controlSinks g0,
                                                   let g = subgraph sink g0,
                                                   let gn   = Map.fromList [ (n, delSuccessorEdges       g  n)    | n <- sink ],
                                                   let gn'  = Map.fromList [ (n, delSuccessorEdges (grev g) n)    | n <- sink ],
                                                   let pdom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn  ! n)    | n <- sink ],
                                                   let  dom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn' ! n)    | n <- sink ],
                                                   let pmay = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn  ! n)    | n <- sink ]
                            ]
                in (∀) sinks (\(sink, pdom, pmay, dom) ->
                            (∀) sink (\x -> (∀) sink (\m1 -> (∀) sink (\m2 -> (∀) sink (\n -> if (m1 == m2 ∨ m1 == x ∨ m2 == x) ∨ (m2 == n) then True else
                               ((not $ m2 ∈ (pmay ! n) ! m1) →
                                                  (( let b0 = m2 ∈ (pmay ! n) ! x
                                                         b1 = m1 ∈ (pdom ! n) ! x
                                                     in (not b0) ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((       x ∈ ( dom ! n) ! m2) →
                                                  (( let b0 = x  ∈ ( dom ! n) ! m1
                                                         b1 = m1 ∈ ( dom ! n) ! m2
                                                     in b0 ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((not $ m2 ∈ (pmay ! n) ! x) →                       -- useless??
                                                   ((let b0 = m1 ∈ (pdom ! n) ! x
                                                         b1 = m1 ∈ ( dom ! n) ! m2
                                                     in b0 ∨ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((not $ m1 ∈ (pmay ! n) ! x) →
                                                   ((let b0 = m2 ∈ (pmay ! n) ! x
                                                         b1 = m1 ∈ ( dom ! n) ! m2
                                                     in (not b0) ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                             ∧ ((      m2 ∈ (pdom ! n) ! x) →
                                                  (( let b0 = m1 ∈ (pdom ! n) ! x
                                                         b1 = m2 ∈ (pdom ! n) ! m1
                                                     in b0 ∧ b1
                                                   )  ↔  (m1 ∈ (pdom ! m2) ! x)))
                    ))))),
    testProperty  "dom/may swap properties in control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g0 = generatedGraph
                        sinks = controlSinks g0
                    in (∀) sinks (\sink ->
                         let g = subgraph sink g0
                             gn   = Map.fromList [ (n,        delSuccessorEdges    g n) | n <- sink ]
                             gn'  = Map.fromList [ (n, grev $ delPredecessorEdges  g n) | n <- sink ]
                             pdom = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn  ! n)    | n <- sink ]
                             pmay = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn  ! n)    | n <- sink ]
                             dom  = Map.fromList [ (n, PDOM.sinkdomOfGfp $ gn' ! n)    | n <- sink ]
                             may  = Map.fromList [ (n, NTICDUnused.mayNaiveGfp  $ gn' ! n)    | n <- sink ]
                         in (∀) sink (\n -> (∀) sink (\m1 -> (∀) sink (\m2 -> if (n == m1 ∨ n == m2 ∨ m1 == m2) then True else
                               (  (m1 ∈ (pdom ! n) ! m2)     ↔     (      m1 ∈ ( dom ! m2) ! n )  )
                             ∧ (  (m1 ∈ (pdom ! n) ! m2)     ↔     (not $ n  ∈ (pmay ! m1) ! m2)  )
                             ∧ (  (m1 ∈ ( dom ! n) ! m2)     ↔     (not $ n  ∈ ( may ! m1) ! m2)  )
                             ∧ (  (m1 ∈ (pmay ! n) ! m2)     ↔     (      m2 ∈ ( may ! n ) ! m1)  )
                            )))
                       ),
  testProperty  "allDom ! n == pdom ! n"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        allDom = NTICDUnused.allDomNaiveGfp g
                    in  (∀) (nodes g) (\n ->
                         let pdom = PDOM.sinkdomOfGfp (delSuccessorEdges g n)
                         in (∀) (nodes g) (\m -> (m ∈ pdom ! n)   ==   (Map.member m (allDom ! n)   ∧   n ∈ allDom ! n ! m))
                        ),
  testProperty  "isTransitive myDom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in  isTransitive $ (fromSuccMap $ NTICDUnused.myDom g :: Gr () ()),
  testPropertySized 40  "isTransitive myDom  for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                    in  isTransitive $ (fromSuccMap $ NTICDUnused.myDom g :: Gr () ()),
  testProperty  "myCDFromMyDom == myCD"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                    in  (Set.fromList $ edges myCDFromMyDomTrc) == (Set.fromList $ edges myCDTrc),
  testPropertySized 40  "myCDFromMyDom == myCD  for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                    in  (Set.fromList $ edges myCDFromMyDomTrc) == (Set.fromList $ edges myCDTrc),
  testPropertySized 50  "wodTEILSlice is contained in wodMyEntryWodMyCDSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticdWodSlice   = NTICDUnused.wodMyEntryWodMyCDSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice           g
                    in  (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice (Set.fromList [m1, m2]) ⊆ nticdWodSlice (Set.fromList [m1, m2])
                        )),
  testPropertySized 30  "wodTEILSlice is contained in wodMyEntryWodMyCDSlice for CFG-shaped graphs with exit->entry edge " 
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        nticdWodSlice   = NTICDUnused.wodMyEntryWodMyCDSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice           g
                    in  (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          let s  = wodTEILSlice (Set.fromList [m1, m2])
                              s' = nticdWodSlice (Set.fromList [m1, m2])
                          in s ⊆ s'
                        )),
  testPropertySized 30  "wodTEILSlice is contained in nticdNTIODSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        nticdWodSlice   = SLICE.ODEP.nticdNTIODSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice g
                    in (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice (Set.fromList [m1, m2]) ⊑   nticdWodSlice (Set.fromList [m1, m2])
                        )),
    testProperty  "ntiod is contained in isinkdom sccs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        isinkdom  = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        ntiod = ODEP.ntiod g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc isinkdomTrc m2 ∧ m1 ∊ suc isinkdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc isinkdomTrc n2) → (
                                   (n1 == n2) ∨ let [n1'] = Set.toList $ isinkdom ! n1 in n1 ∊ suc isinkdomTrc n1'
                              )
                          ))
                        ∧ (∀) ns (\n -> (∀) (isinkdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc isinkdomTrc m1 ∧ m1 ∊ suc isinkdomTrc m   ∧   m ∊ suc isinkdomTrc m2 ∧ m2 ∊ suc isinkdomTrc m)
                          ))
                        ),
    testProperty  "snmF3Gfp reachable          == isinkdom reachable "
                $ \(ARBITRARY(generatedGraph)) ->
                    let graph     = generatedGraph
                        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
                        s3        = SNM.snmF3 graph
                        isinkdom     = PDOM.TRANS.isinkdomOfSinkContraction graph
                        isinkdomTrc  = trc $ (fromSuccMap isinkdom :: Gr () ())
                    in (∀) (nodes graph) (\m ->
                         (∀) condNodes (\n ->     ((n == m) ∨ (Set.size (s3 ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)))
                                               ↔ (m ∊ (suc isinkdomTrc n))
                         )
                       ),
    testProperty  "rotatePDomAround g (pdom_n) (n->m)  == pdom_m in arbitrary control sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                    let sinks = controlSinks generatedGraph
                    in (∀) sinks (\sink -> let g = subgraph sink generatedGraph in
                         (∀) (nodes g) (\n ->
                           let gn   = efilter (\(x,y,_) -> x /= n) g
                               pdom = fmap fromSet $ PDOM.isinkdomOfTwoFinger8 gn
                               condNodes = Map.fromList [ (x, succs) | x <- nodes g, let succs = suc g x, length succs  > 1 ]
                           in    (∀) (suc g n) (\m -> if m == n then True else
                                  let pdom' = fmap fromSet $ PDOM.isinkdomOfTwoFinger8 gm
                                        where gm = delSuccessorEdges g m
                                      rpdom' = ODEP.rotatePDomAround g condNodes pdom (n,m)
                                  in pdom' == rpdom'
                                 )
                         )
                       ),
    testPropertySized 20  "ntiodFromMay            == ntiodFast for CFG-shaped graphs with exit->entry edge"  -- but: see InvalidProperties.hs
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        ntiodFromMay = NTICDUnused.ntiodFromMay g
                        ntiodFast    = ODEP.ntiodFast    g
                    in ntiodFromMay == ntiodFast,
    testProperty  "ntiodFastPDom*            == ntiodFast"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiodFastPDomSimpleHeuristic = ODEP.ntiodFastPDomSimpleHeuristic  g
                        ntiodFastPDom                = ODEP.ntiodFastPDom                 g
                        ntiodFast                    = ODEP.ntiodFast                     g
                    in   True
                       ∧ ntiodFastPDomSimpleHeuristic == ntiodFast
                       ∧ ntiodFastPDom                == ntiodFast,
    testPropertySized 20  "ntiodFastPDom*            == ntiodFast for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        ntiodFastPDomSimpleHeuristic  = ODEP.ntiodFastPDomSimpleHeuristic   g
                        ntiodFastPDom                 = ODEP.ntiodFastPDom                  g
                        ntiodFast                     = ODEP.ntiodFast                      g
                    in   True
                       ∧ ntiodFastPDomSimpleHeuristic  == ntiodFast
                       ∧ ntiodFastPDom                 == ntiodFast,
     testProperty  "ntiodFastPDom*            == ntiodFastPDom* for arbitrary graphs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntiodFastPDomSimpleHeuristic = ODEP.ntiodFastPDomSimpleHeuristic  g
                        ntiodFastPDom                = ODEP.ntiodFastPDom                 g
                    in   True
                       ∧ ntiodFastPDomSimpleHeuristic == ntiodFastPDom,
    testPropertySized 30  "ntiodFastPDom*             == ntiodFastPDom* for CFG-shaped graphs with exit->entry edge"
    $ \(SIMPLECFG(generatedGraph)) ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        ntiodFastPDomSimpleHeuristic  = ODEP.ntiodFastPDomSimpleHeuristic   g
                        ntiodFastPDom                 = ODEP.ntiodFastPDom                  g
                        n = length $ nodes g
                    in -- traceShow (n, sum $ fmap (\s -> if Set.null s then 0 else 1) $ Map.elems ntiodFastPDomSimpleHeuristic, n*n, sum $ fmap Set.size $ Map.elems ntiodFastPDomSimpleHeuristic) $
                         True
                       ∧ ntiodFastPDomSimpleHeuristic  == ntiodFastPDom,
    testProperty  "ntiodFastPDom             == ntiod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntiodFastPDom   g ==
                       ODEP.ntiod           g,
    testProperty  "ntiodFast                 == ntiod"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntiodFast       g ==
                       ODEP.ntiod           g
  ]
wodTests = testGroup "(concerning weak order dependence)" $
  [  testCase    ( "ntiod ⊑ wodTEIL' for " ++ exampleName)
            $       let ntiod = ODEP.ntiod g
                        wodTEIL' = ODEP.wodTEIL' g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ns ⊑ (wodTEIL' ! (m1,m2))
                        )@? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "wodTEILSlice is contained in nticdNTIODSlice for " ++ exampleName)
            $       let nticdWodSlice   = SLICE.ODEP.nticdNTIODSlice g
                        wodTEILSlice    = SLICE.ODEP.wodTEILSlice g
                    in  (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          wodTEILSlice (Set.fromList [m1, m2])  ⊑  nticdWodSlice (Set.fromList [m1, m2])
                        )) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiod is contained in isinkdom sccs  for " ++ exampleName)
            $       let isinkdom  = PDOM.TRANS.isinkdomOfSinkContraction g
                        isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: Gr () ())
                        ntiod = ODEP.ntiod g
                    in  (∀) (Map.assocs ntiod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc isinkdomTrc m2 ∧ m1 ∊ suc isinkdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc isinkdomTrc n2) → (
                                   (n1 == n2) ∨ let [n1'] = Set.toList $ isinkdom ! n1 in n1 ∊ suc isinkdomTrc n1'
                              )
                          ))
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "myCDFromMyDom == myCD for " ++ exampleName) $
                   let  myCDFromMyDom    = NTICDUnused.myCDFromMyDom g
                        myCD             = NTICDUnused.myCD          g
                        myCDTrc          = trc $ (fromSuccMap $ myCD          :: Gr () ())
                        myCDFromMyDomTrc = trc $ (fromSuccMap $ myCDFromMyDom :: Gr () ())
                   in  (Set.fromList $ edges myCDFromMyDomTrc)  == (Set.fromList $ edges myCDTrc) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "isTransitive myDom for " ++ exampleName) $
                   isTransitive (fromSuccMap $ NTICDUnused.myDom g :: Gr () ()) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiodFastPDom               == ntiodFast for " ++ exampleName)
            $ ODEP.ntiodFastPDom g             == ODEP.ntiodFast g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiodFastPDom               == ntiod for " ++ exampleName)
            $ ODEP.ntiodFast g                 == ODEP.ntiod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntiodFastPDom               == ntiod for " ++ exampleName)
            $ ODEP.ntiodFastPDom g             == ODEP.ntiod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []

