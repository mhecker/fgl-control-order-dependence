{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Dod where


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
import Util(sampleFrom, invert'', moreSeeds, restrict, (≡), the)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)


import Data.Graph.Inductive.Query.DFS (scc, reachable, rdfs)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (mdomOfLfp, imdomOfTwoFinger6)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (mDFTwoFinger)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
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
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (
    nticdViaSinkDom,
    ntscdViaMDom,
    ntindDef, ntsndDef,
    nticdDef, 
    ntscdDef, 
  )
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (snmF3Lfp)
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (
     mustOfLfp, mustOfGfp, mmayOf, mmayOf', rotatePDomAround, Color(..), smmnFMustDod, smmnFMustWod, colorLfpFor, colorFor,
    smmnGfp, smmnLfp, fMust, fMustBefore, fMustNoReachCheck,
    dod, dodDef, dodFast, dodColoredDagFixed, dodColoredDagFixedFast,
    ntiod, ntiodFast, ntiodFastPDom, ntiodFastPDomSimpleHeuristic,  ntsod, ntsodFast, ntsodFastPDom, wodTEIL', wodTEIL'PDom, wodDef, wodFast, fMay, fMay'
  )

dod        = defaultMain                               $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]
dodX       = defaultMainWithIngredients [antXMLRunner] $ testGroup "dod"       [ mkTest [dodTests], mkProp [dodProps]]

dodProps = testGroup "(concerning decisive order dependence)" [
    testProperty "ntscdNTIOD == ntscdNTSODViaNtscd properties"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                let g    = generatedGraph
                    trcG = trc g
                    m0S
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                     where n    = length $ nodes g
                in
                -- in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  {- let m0S = Set.fromList [m1, m2] in  -- -} (∀) (nodes g) (\m3 -> (∀) (nodes g) (\m4 -> let m0S = Set.fromList [m1, m2, m3, m4] in
                     let  m0s = Set.toList m0S
                          toM0s = rdfs m0s g
                          g' = foldr (flip delSuccessorEdges) g m0s
                          ntscd' = NTICD.ntscdViaMDom g'
                          nticd'slicer = SLICE.NTICD.ntscdSlice g'
                          mdom' = PDOM.mdomOfLfp g'
                     in (∀) m0S (\m -> (∀) (nticd'slicer (Set.fromList [m])) (\n -> 
                          let ok = (mdom' ! n == Set.fromList [n])
                          in (if ok then id else traceShow (g, m0S, n, m)) ok
                        ))
                   -- )))),
                   ,
  testProperty "ntscdNTSODSlice == ntscdNTSODSliceViaIMDom  for random slice-criteria of random size, and CFG-shaped graphs"
    $ \(SIMPLECFG(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.NTICD.ntscdNTSODSliceViaNtscd   g
                    slicer2  = SLICE.PDOM.ntscdNTSODSliceViaIMDom    g
                in   slicer1  ms == slicer2  ms,
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
                   ),
    testPropertySized 30 "ntscdNTSODSlice == ntscdNTSODSliceViaNticd for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                let g    = generatedGraph
                    g'   = grev g
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    slicer1  = SLICE.ODEP.ntscdNTSODSlice               g
                    slicer2  = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g
                    slicer1' = SLICE.ODEP.ntscdNTSODSlice               g'
                    slicer2' = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g'
                in   slicer1  ms == slicer2  ms
                   ∧ slicer1' ms == slicer2' ms,
    testPropertySized 40 "ntscdNTSODSlice == ntscdNTSODSliceViaNtscd"
    $ \(ARBITRARY(generatedGraph)) ->
                let g    = generatedGraph
                    g'   = grev g
                    slicer1  = SLICE.ODEP.ntscdNTSODFastPDomSlice       g
                    slicer2  = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g
                    slicer1' = SLICE.ODEP.ntscdNTSODFastPDomSlice       g'
                    slicer2' = SLICE.NTICD.ntscdNTSODSliceViaNtscd      g'
                in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 ->  let ms = Set.fromList [m1, m2] in -- (∀) (nodes g) (\m3 -> let ms = Set.fromList [m1, m2, m3] in 
                       slicer1  ms == slicer2  ms
                     ∧ slicer1' ms == slicer2' ms
                   )), -- ),
      testPropertySized 25  "ntscdNTSODSlice == ntscdNTSODSliceViaNtscd even when using data dependencies"
                $ \(ARBITRARY(generatedGraph)) (UNCONNECTED(ddep0)) ->
                   let g = generatedGraph
                       ddepG = mkGraph (labNodes g) [ (n',m',()) | (n,m) <- edges ddep0, let n' = toG ! n, let m' = toG ! m, n' `elem` reachable m' g ] :: Gr ()()
                         where toG = Map.fromList $ zip (nodes ddep0) (cycle $ nodes g)
                       ddep = Map.fromList [ (n, Set.fromList $ suc ddepG n) | n <- nodes ddepG ]
                       ntscd = PDF.mDFTwoFinger g
                       ntsod =  ODEP.ntsodFastPDom g
                       slicer = combinedBackwardSlice (ddep ⊔ ntscd) ntsod 
                   in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> (∀) (nodes g) (\m3 ->
                        let ms  = [m1, m2, m3]
                            msS = Set.fromList ms
                            g' = foldr (flip delSuccessorEdges) g ms
                            ntscd' = PDF.mDFTwoFinger g'
                            empty = Map.empty
                            slicer' = combinedBackwardSlice (ddep ⊔ ntscd') empty
                        in slicer msS == slicer' msS
                      ))),
      testProperty  "mdomOfLfp m2                 == mustOfLfp"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.mustOfLfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               mdom2 = PDOM.mdomOfLfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ mdom2 ! n)
                           ))
                       ),
    testProperty  "|ntsodFastPDom|             >= |dodColoredDagFixedFast|"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        must = ODEP.smmnFMustDod g
                        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               mdom2 = PDOM.mdomOfLfp g2
                           in (∀) condNodes (\n -> (∀) (nodes g) (\m1 -> if m1 == m2 ∨ m1 == n ∨ m2 == n then True else
                                let s12n = must ! (m1,m2,n) in
                                (Set.size s12n == (Set.size $ Set.fromList $ suc g n)) ↔ (m1 ∈ mdom2 ! n)
                           ))
                       ),
    testProperty  "|ntsodFastPDom|             >= |dodColoredDagFixedFast|"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        sum = Map.foldr (\ns s -> Set.size ns + s) 0
                    in (sum $ ODEP.ntsodFastPDom          g) >=
                       (sum $ ODEP.dodColoredDagFixedFast g),
    testProperty  "ntsodFastPDom               ≡ ntsodFast"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntsodFastPDom   g ≡
                       ODEP.ntsodFast       g,
    testProperty  "ntsodFastPDom               ≡ ntsod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntsodFastPDom   g ≡
                       ODEP.ntsod           g,
    testProperty  "ntsodFast                 == ntsod"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.ntsodFast       g ==
                       ODEP.ntsod           g,
    testProperty  "ntsod is contained in imdom sccs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ),
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
                        ),
    testProperty  "ntscdDodSlice == ntscdNTSODSlice"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        ntscdDodSlice     = SLICE.ODEP.ntscdDodSlice g
                        ntscdNTSODSlice   = SLICE.ODEP.ntscdNTSODSlice g
                    in  -- traceShow (length $ nodes g) $
                        (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          ntscdDodSlice   (Set.fromList [m1, m2]) ==
                          ntscdNTSODSlice (Set.fromList [m1, m2])
                        )),
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
                        ),
    testProperty  "dod is contained in imdom sccs "
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom  = PDOM.imdomOfTwoFinger6 g
                        dod = ODEP.dod g
                        imdomSccs = scc (fromSuccMap imdom :: Gr () ())
                        imdomCycleOf m =  the (m ∊) $ imdomSccs
                    in  (∀) (nodes g) (\m1 ->
                          (∀) (List.delete m1 $ nodes g) (\m2 ->
                            let c1 = imdomCycleOf m1
                                c2 = imdomCycleOf m2
                            in (not (c1 == c2 ∧ length c1 > 1) ) → (Set.null $ dod ! (m1,m2))
                          )
                        ),
    testProperty  "dod is contained in imdom sccs, and only possible for immediate entries into sccs"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        dod = ODEP.dod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ),
    testProperty  "snmF3Lfp reachable          == imdom reachable "
                $ \(ARBITRARY(generatedGraph)) ->
                    let graph     = generatedGraph
                        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
                        s3        = SNM.snmF3Lfp graph
                        imdom     = PDOM.imdomOfTwoFinger6 graph
                        imdomTrc  = trc $ (fromSuccMap imdom :: Gr () ())
                    in (∀) (nodes graph) (\m ->
                         (∀) condNodes (\n ->     ((n == m) ∨ (Set.size (s3 ! (m,n)) == (Set.size $ Set.fromList $ suc graph n)))
                                               ↔ (m ∊ (suc imdomTrc n))
                         )
                       ),
    testProperty  "dodColoredDagFixedFast     == dodFast"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodColoredDagFixedFast g ==
                       ODEP.dodFast                 g,
    testProperty  "dodColoredDagFixedFast     == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodColoredDagFixedFast g ==
                       ODEP.dodDef                 g,
    testProperty  "dodColoredDagFixed         == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodColoredDagFixed g ==
                       ODEP.dodDef             g,
    testProperty  "dod                       == dodDef"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dod           g ==
                       ODEP.dodDef        g,
    testProperty  "dodFast                   == dodDef"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.dodFast       g ==
                       ODEP.dodDef        g,
    testProperty  "lfp fMustNoReachCheck      == lfp fMust"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in ODEP.smmnLfp g ODEP.fMustNoReachCheck        ==
                       ODEP.smmnLfp g ODEP.fMust
  ]
dodTests = testGroup "(concerning decisive order dependence)" $
  [  testCase    ( "mdomOfLfp m2              == mustOfLfp for " ++ exampleName)
            $       let  must = ODEP.mustOfLfp g
                    in  (∀) (nodes g) (\m2 ->
                           let g2    = delSuccessorEdges g m2
                               mdom2 = PDOM.mdomOfLfp g2
                           in (∀) (nodes g) (\n -> (∀) (nodes g) (\m1 ->  if m1 == m2  then True else
                                ((m1,m2) ∈ must ! n) ↔ (m1 ∈ mdom2 ! n)
                           ))
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsodFastPDom             ≡ ntsodFast for " ++ exampleName)
            $ ODEP.ntsodFastPDom      g      ≡ ODEP.ntsodFast g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsodFastPDom             ≡ ntsod for " ++ exampleName)
            $ ODEP.ntsodFastPDom      g      ≡ ODEP.ntsod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsodFast                 == ntsod for " ++ exampleName)
            $ ODEP.ntsodFast          g      == ODEP.ntsod g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsod is contained in imdom sccs  for " ++ exampleName)
            $       let imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntscdDodSlice == ntscdNTSODSlice property for " ++ exampleName)
            $       let ntsod = ODEP.ntsod g
                        ntscd = NTICD.ntscdViaMDom g
                        ntscdTrc = trc $ (fromSuccMap ntscd :: Gr () ())
                    in  (∀) (Map.assocs ntsod) (\((m1,m2), ns) ->
                          (∀) ns (\n -> n ∈ ntsod ! (m2,m1) ∨
                                        (∃) (ns ∩ (ntsod ! (m2, m1))) (\n' -> n' ∊ (suc ntscdTrc n))
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntscdDodSlice == ntscdNTSODSlice for " ++ exampleName)
            $       let ntscdDodSlice     = SLICE.ODEP.ntscdDodSlice g
                        ntscdNTSODSlice   = SLICE.ODEP.ntscdNTSODSlice g
                    in  -- traceShow (length $ nodes g) $
                        (∀) (nodes g) (\m1 ->  (∀) (nodes g) (\m2 ->
                          ntscdDodSlice   (Set.fromList [m1, m2]) ==
                          ntscdNTSODSlice (Set.fromList [m1, m2])
                        )) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dod implies ntsod for " ++ exampleName)
            $       let dod = ODEP.dod g
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          (∀) ns (\n -> n ∈ ntsod ! (m1,m2) ∧
                                        n ∈ ntsod ! (m2,m1)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "ntsod implies dod for " ++ exampleName)
            $       let dod = ODEP.dod g
                        ntsod = ODEP.ntsod g
                    in  (∀) (Map.keys ntsod) (\(m1,m2) ->
                          (∀) (ntsod ! (m1,m2)  ⊓  ntsod ! (m2,m1)) (\n -> n ∈ dod ! (m1,m2)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dod is contained in imdom sccs, and only possible for immediate entries into sccs for " ++ exampleName)
            $       let imdom  = PDOM.imdomOfTwoFinger6 g
                        imdomTrc = trc $ (fromSuccMap $ imdom :: Gr () ())
                        dod = ODEP.dod g
                    in  (∀) (Map.assocs dod) (\((m1,m2), ns) ->
                          ((not $ Set.null ns) → (m1 ∊ suc imdomTrc m2 ∧ m1 ∊ suc imdomTrc m2))
                        ∧ (∀) ns (\n1 -> (∀) ns (\n2 ->
                              (n1 ∊ suc imdomTrc n2 ∨ n2 ∊ suc imdomTrc n1) → (n1 == n2)
                          ))
                        ∧ (∀) ns (\n -> (∀) (imdom ! n) (\m ->
                              (m == n) ∨ (m ∊ suc imdomTrc m1 ∧ m1 ∊ suc imdomTrc m   ∧   m ∊ suc imdomTrc m2 ∧ m2 ∊ suc imdomTrc m)
                          ))
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ suc imdomTrc m1 ∨ n  ∊ suc imdomTrc m2)
                          )
                        ∧ (∀) ns (\n ->
                              not $
                              (n  ∊ reachable m1 g  ∨ n  ∊ reachable m2 g)
                          )
                        ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dodColoredDagFixedFast        == dodDef for " ++ exampleName)
            $ ODEP.dodColoredDagFixedFast g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dodColoredDagFixed        == dodDef for " ++ exampleName)
            $ ODEP.dodColoredDagFixed g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dod                       == dodDef for " ++ exampleName)
            $ ODEP.dod                g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "dodFast                   == dodDef for " ++ exampleName)
            $ ODEP.dodFast            g      == ODEP.dodDef g @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []
