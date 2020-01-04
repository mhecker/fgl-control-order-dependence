{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Sensitivedom where


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
import Util(sampleFrom, invert'', moreSeeds, restrict, fromSet, invert''', treeLevel, findCyclesM)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, interestingImdomTwoFinger, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation)


import Data.Graph.Inductive.Query.DFS (scc)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (isinkdomOf, isinkdomOfGfp2, joinUpperBound, sinkdomOfJoinUpperBound, sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkdomNaiveGfp, sinkdomNaiveGfpFullTop, sinkdomOfisinkdomProperty, imdomOf, imdomOfLfp, mdomOf, mdomOfLfp, mdomNaiveLfp, mdomOfimdomProperty, onedomOf, mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, isinkdomOftwoFinger8Up,  imdomOfTwoFinger6, imdomOfTwoFinger7)
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
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (
    nticdNTIODSlice, nticdSlice,  ntscdSlice,
    ntscdNTSODSliceViaNtscd, wodTEILSliceViaNticd,
    wccSliceViaNticd,
  )
import qualified Data.Graph.Inductive.Query.NTICD as NTICD (ntscdViaMDom)
import qualified Data.Graph.Inductive.Query.NTICD.SNM as SNM (
    snmF3, snmF3Lfp,
    snmF4WithReachCheckGfp,
    nticdF3WorkList, nticdF3WorkListSymbolic, nticdF3'dualWorkListSymbolic,  nticdF3, nticdF5, nticdFig5, nticdF3', nticdF3'dual, 
    nticdF3'dualWorkList, snmF3'dual,
    ntscdF4, ntscdF3, ntscdF4WorkList
  )

sensitivedom      = defaultMain                               $ testGroup "sensitiveDom"     [ mkTest [sensitiveDomTests],  mkProp [sensitiveDomProps]]
sensitivedomX     = defaultMainWithIngredients [antXMLRunner] $ testGroup "sensitiveDom"     [ mkTest [sensitiveDomTests],  mkProp [sensitiveDomProps]]



sensitiveDomProps = testGroup "(concerning nontermination-sensitive control dependence via dom-like frontiers )" [
    testProperty   "ntscdViaMDom          == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in NTICD.ntscdViaMDom g ==
                       SNM.ntscdF3        g,
    testPropertySized 40 "stepsCL mdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                    in PDF.stepsCL g mdom,
    testPropertySized 40 "noJoins mdom"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                    in PDF.noJoins g mdom,
    testProperty   "idomToDFFast _ imdom6  == idomToDFFast _ imdom7  for CFG-shaped graphs with exit->entry edge"
                $ \(SIMPLECFG(generatedGraph)) ->
                let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                    [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                    g = insEdge (exit, entry, ()) generatedGraph
                    imdom6 = PDOM.imdomOfTwoFinger6 g
                    imdom7 = PDOM.imdomOfTwoFinger7 g
                in PDF.idomToDFFast g imdom6 == PDF.idomToDFFast g imdom7,
    testProperty   "idomToDFFast _ imdom6  == idomToDFFast _ imdom7"
                $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    imdom6 = PDOM.imdomOfTwoFinger6 g
                    imdom7 = PDOM.imdomOfTwoFinger7 g
                in PDF.idomToDFFast g imdom6 == PDF.idomToDFFast g imdom7,
    testPropertySized 60 "idfViaCEdgesFast properties"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        mdom = PDOM.mdomOfLfp g
                        imdomsOf = PDOM.mdomsOf g
                        idom = fmap fromSet $ PDOM.imdomOfTwoFinger7 g
                        idom'  = invert''' idom
                        (cycleOfM, cycles) = findCyclesM idom
                        roots = foldr (\(n,m) roots -> if m == Nothing then Set.fromList [n] : roots else roots) cycles (Map.assocs idom)
                        levelOf = Map.fromList [ (n,l) | nl <- treeLevel idom' roots, (n,l) <- nl]
                        cEdges = Map.fromList [(z, [ y | y <- pre g z, not $ z ∈ imdomsOf ! y ]) | z <- nodes g]
                    in   (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  mdom ! x   ⊃   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                      ∧  (∀) (nodes g)                       (\x -> (∀) (cEdges ! x) (\y ->  not $  x   ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                      ∧  (∀) (nodes g) (\z -> (∀) (mdom ! z) (\x -> (∀) (cEdges ! z) (\y -> (       x   ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])
                                                                                   ↔ (not $ mdom ! x    ⊃   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])
                         )))
                      ∧  (∀) (nodes g) (\z -> (∀) (mdom ! z) (\x -> (∀) (cEdges ! z) (\y ->
                           (   ( (mdom ! x  ⊃  (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])  ∧  (not $ x  ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                             ∨ ( (mdom ! x  ⊆  (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y])  ∧  (      x  ∈   (∐) [ mdom ! y' | y' <- Set.toList $ imdomsOf ! y]))
                           )
                         ∧ (let lvlY' = case idom ! y of { Nothing -> -1 ; Just y' -> levelOf ! y' } in
                            let ok = ((x /= y)  ∧  (not $ Set.null $ mdom ! y ∩ mdom ! x)) → ((not $ x ∈ mdom ! y) ↔ (lvlY' < levelOf ! x)) in (if ok then id else traceShow (g,x,y,z, levelOf)) ok
                           )
                         ))),
    testProperty   "ntscdSlice  == idfViaCEdgesFast"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom    = PDOM.imdomOfTwoFinger7  g
                        idfViaJ  = CEDGE.idfViaCEdgesFast g (fmap fromSet imdom)
                        ntscdslicer = SLICE.NTICD.ntscdSlice g
                    in (∀) (nodes g) (\m1 -> (∀) (nodes g) (\m2 -> let ms = Set.fromList [m1,m2] in
                              ntscdslicer ms == idfViaJ ms
                    )),
    testProperty   "ntscdSlice  == ntscdslicerCEdges for CFG like graphs for random slice-criteria of random size"
                $ \(SIMPLECFG(generatedGraph)) seed1 seed2 ->
                    let [entry] = [ n | n <- nodes generatedGraph, pre generatedGraph n == [] ]
                        [exit]  = [ n | n <- nodes generatedGraph, suc generatedGraph n == [] ]
                        g = insEdge (exit, entry, ()) generatedGraph
                        n    = length $ nodes g
                        ms  = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        ntscdslicer        = SLICE.NTICD.ntscdSlice              g
                        ntscdslicerCEdges  = CEDGE.ntscdSliceViaCEdgesFast g
                    in  ntscdslicer ms == ntscdslicerCEdges ms,
    testProperty   "ntscdSlice  == ntscdslicerCEdges for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                         | n == 0 = Set.empty
                         | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        ntscdslicer        = SLICE.NTICD.ntscdSlice              g
                        ntscdslicerCEdges  = CEDGE.ntscdSliceViaCEdgesFast g
                    in  ntscdslicer ms == ntscdslicerCEdges ms,
    testProperty   "idomToDFFast _ == dfViaCEdges _"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom7] (\imdom ->
                         let dfViaJ = CEDGE.dfViaCEdges g (fmap fromSet imdom) in
                         PDF.idomToDFFast g imdom == Map.fromList [ (n, dfViaJ n) | n <- nodes g]
                    ),
    testPropertySized 80   "mDFFromUpLocalDefViaSMdoms == mDF"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFFromUpLocalDefViaMdoms g ==
                       PDF.mDF                       g,
    testProperty   "idomToDFFast _ imdom == idomToDF _ imdom"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g              imdom ==
                         PDF.idomToDF     g (fromSuccMap imdom :: Gr () ())
                       ),
    testProperty   "idomToDFFast _ imdom  == mDF _ "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g imdom ==
                         PDF.mDF          g
                       ),
    testProperty   "DF of imdom Cycles are all the same"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom6 = fromSuccMap $ PDOM.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ PDOM.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         let df    = PDF.idomToDF g imdom
                             idomSccs = scc imdom
                             cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                         in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))
                       ),
    testProperty   "imdomOfTwoFinger7^*   == imdomOfTwoFinger6^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ fromSuccMap $
                        PDOM.imdomOfTwoFinger7            g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        PDOM.imdomOfTwoFinger6            g),
    testProperty   "imdomOfLfp^*          == imdomOfTwoFinger6^*"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in (trc $ PDOM.imdomOfLfp             g :: Gr () ()) ==
                       (trc $ fromSuccMap $
                        PDOM.imdomOfTwoFinger6            g),
    testPropertySized 50   "mdomOf             == mdomNaiveLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.mdomOf              g ==
                       PDOM.mdomNaiveLfp        g,
    testPropertySized 50   "mdomOf             == mdomOfLfp "
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.mdomOf              g ==
                       PDOM.mdomOfLfp           g,
    testProperty   "mdomOfLfp reduces, in some sense,  to a multi-rooted tree"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        imdom = PDOM.imdomOfLfp g :: Gr () ()
                    in   (∀) (nodes imdom) (\n -> length (suc imdom n) <= 1),
    testProperty   "mdomOfLfp           == mdomOfimdomProperty"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDOM.mdomOfLfp            g ==
                       PDOM.mdomOfimdomProperty  g,
    testPropertySized 50   "mDFUpGivenXViaMdoms == mDFUpGivenX"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFUpGivenXViaMdoms     g ==
                       PDF.mDFUpGivenX             g,
    testPropertySized 50   "mDFUpDefViaMdoms == mDFUpDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFUpDefViaMdoms     g ==
                       PDF.mDFUpDef             g,
    testProperty   "mDFUpGivenX ! (x,z) is independent of choice of x for given z"
                $ \(ARBITRARY(g)) ->
                    let mDFUp = PDF.mDFUpGivenX g
                    in (∀) (Map.assocs mDFUp) (\((x,z), dfUp) ->
                         (∀) (Map.assocs mDFUp) (\((x',z'), dfUp') ->
                           (z == z') → (dfUp == dfUp')
                         )
                       ),
    testProperty   "mDFUpGivenX ! (x,z) == mDFUpDef ! z"
                $ \(ARBITRARY(g)) ->
                    let mDFUp    = PDF.mDFUpGivenX g
                        mDFUpDef = PDF.mDFUpDef    g
                    in (∀) (Map.assocs mDFUp) (\((x,z), dfUp) ->
                         dfUp == mDFUpDef ! z
                       )
                    ∧  (∀) (Map.assocs mDFUpDef) (\(z, dfUp) ->
                         (∀) [ (x, dfUp') | ((x,z'), dfUp') <- Map.assocs mDFUp, z == z'] (\(x, dfUp') ->
                           dfUp == dfUp'
                         )
                       ),
    testProperty   "mDFUp              == mDFUpDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFUp                g ==
                       PDF.mDFUpDef             g,
    testPropertySized 50   "mDFLocalViaMdoms   == mDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFLocalViaMdoms     g ==
                       PDF.mDFLocalDef          g,
    testProperty   "mDFLocal           == mDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       PDF.mDFLocal             g ==
                       PDF.mDFLocalDef          g,
    testProperty   "mDFcd              == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFcd            g ==
                       SNM.ntscdF3          g,
    testProperty   "mDFFromUpLocalDefcd== ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFFromUpLocalDefcd  g ==
                       SNM.ntscdF3              g,
    testProperty   "mDFFromUpLocalcd   == ntisdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFFromUpLocalcd     g ==
                       SNM.ntscdF3              g,
    testProperty   "imdomTwoFingercd     == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.imdomTwoFingercd   g ==
                       SNM.ntscdF3          g,
    testProperty   "mDFF2cd            == ntscdF3"
                $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                    in PDF.mDFF2cd              g ==
                       SNM.ntscdF3              g
  ]
sensitiveDomTests = testGroup "(concerning nontermination-sensitive control dependence via dom-like frontiers )"  $
  [  testCase    ( "idomToDFFast _ mdom == mDF _ for " ++ exampleName)
            $       let imdom6 = PDOM.imdomOfTwoFinger6  g
                        imdom7 = PDOM.imdomOfTwoFinger7  g
                    in (∀) [imdom6, imdom7] (\imdom ->
                       PDF.idomToDFFast g imdom ==
                       PDF.mDF       g) @? ""
  | (exampleName, g) <- interestingImdomTwoFinger
  ] ++
  [  testCase    (  "mDFLocal == mDFLocalDef for " ++ exampleName)
            $          PDF.mDFLocal    g ==
                       PDF.mDFLocalDef g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFFromUpLocalDefViaMdoms == mDF for " ++ exampleName)
            $          PDF.mDFFromUpLocalDefViaMdoms g ==
                       PDF.mDF                       g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFUpGivenXViaMdoms == mDFUpGivenX for " ++ exampleName)
            $          PDF.mDFUpGivenXViaMdoms     g ==
                       PDF.mDFUpGivenX             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    (  "mDFUpDefViaMdoms == mDFUpDef for " ++ exampleName)
            $            PDF.mDFUpDefViaMdoms     g ==
                         PDF.mDFUpDef             g
                       @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ imdom == idomToDF _ imdom for " ++ exampleName)
            $       let imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g              imdom ==
                         PDF.idomToDF     g (fromSuccMap imdom :: Gr () ())
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "idomToDFFast _ imdom == mDF _ for " ++ exampleName)
            $       let imdom6 = PDOM.imdomOfTwoFinger6 g
                        imdom7 = PDOM.imdomOfTwoFinger7 g
                    in (∀) [imdom6, imdom7] (\imdom ->
                         PDF.idomToDFFast g imdom ==
                         PDF.mDF          g
                       ) @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "DF of imdom Cycles are all the same for " ++ exampleName)
            $       let imdom6 = fromSuccMap $ PDOM.imdomOfTwoFinger6 g :: Gr () ()
                        imdom7 = fromSuccMap $ PDOM.imdomOfTwoFinger7 g :: Gr () ()
                    in (∀) [imdom6, imdom7] (\imdom ->
                         let df    = PDF.idomToDF g imdom
                             idomSccs = scc imdom
                             cycles = [ cycle | cycle <- idomSccs, length cycle > 1 ]
                         in (∀) cycles (\cycle ->  (∀) cycle (\n -> (∀) cycle (\m -> df ! n == df ! m)))
                       )  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "imdomOfTwoFinger7^*   == imdomOfTwoFinger6^* for " ++ exampleName)
                  $ (trc $ fromSuccMap $
                           PDOM.imdomOfTwoFinger7            g :: Gr () ()) ==
                    (trc $ fromSuccMap $
                           PDOM.imdomOfTwoFinger6            g)  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  [  testCase    ( "imdomOfLfp^*          == imdomOfTwoFinger6^* for " ++ exampleName)
                  $ (trc $ PDOM.imdomOfLfp             g :: Gr () ()) ==
                    (trc $ fromSuccMap $
                           PDOM.imdomOfTwoFinger6            g)  @? ""
  | (exampleName, g) <- interestingDodWod
  ] ++
  []

