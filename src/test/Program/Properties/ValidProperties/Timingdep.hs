{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Timingdep where


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
import Util(sampleFrom, invert'', moreSeeds, restrict, reachableFromIn, findCyclesM, fromSet, pathsUpToLength, minimalPath)

import Program (Program, tcfg, entryOf, procedureOf, mainThread, observability)
import Program.Properties.Util
import Program.Defaults (defaultInput)
import Program.For (compileAllToProgram)
import Program.Generator (toProgram, toProgramIntra, toCodeSimple, toCodeSimpleWithArrays, GeneratedProgram, SimpleCFG(..))

import Program.Examples (testsuite, interestingDodWod, interestingTimingDep, interestingIsinkdomTwoFinger, code2ResumptionForProgram, code2Program)

import Data.Graph.Inductive.Util (withUniqueEndNode, fromSuccMap, delSuccessorEdges, delPredecessorEdges, isTransitive, controlSinks, ladder, fullLadder, withoutSelfEdges, costFor, prevCondsWithSuccNode, prevCondsWithSuccNode', toSuccMap, withNodes, fromSuccMapWithEdgeAnnotation, removeDuplicateEdges)


import Data.Graph.Inductive.Dot (showDot, fglToDotGeneric)

import System.IO.Unsafe(unsafePerformIO)

import IRLSOD(CFGEdge(..))

import Data.Graph.Inductive.Arbitrary.Reducible
import Data.Graph.Inductive.Query.TimingDependence (timingDependence, timingDependenceOld)
import qualified Data.Graph.Inductive.Query.PostDominance as PDOM (isinkdomOf, isinkdomOfGfp2, joinUpperBound, sinkdomOfJoinUpperBound, sinkdomOf, sinkdomOfGfp, sinkdomOfLfp, sinkdomNaiveGfp, sinkdomNaiveGfpFullTop, sinkdomOfisinkdomProperty, imdomOf, imdomOfLfp, mdomOf, mdomOfLfp, mdomNaiveLfp, mdomOfimdomProperty, onedomOf, mdomsOf, sinkdomsOf, isinkdomOfTwoFinger8, isinkdomOftwoFinger8Up,  imdomOfTwoFinger6, imdomOfTwoFinger7)
import qualified Data.Graph.Inductive.Query.PostDominanceFrontiers as PDF (stepsCL, noJoins)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (delayedInfinitely, sampleLoopPathsFor, isTracePrefixOf, sampleChoicesFor, Input(..), infinitelyDelays, runInput, observable, allChoices, isAscending, isLowEquivalentFor, isLowTimingEquivalent, isLowEquivalentTimed)
import qualified Data.Graph.Inductive.Query.Util.GraphTransformations as TRANS (sinkShrinkedGraphNoNewExitForSinks)
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (ntscdNTSODSliceViaNtscd, ntscdSlice)
import qualified Data.Graph.Inductive.Query.PathsBetween as PBETWEEN (
    pathsBetweenBFS, pathsBetweenUpToBFS,
    pathsBetween,    pathsBetweenUpTo,
  )
import qualified Data.Graph.Inductive.Query.OrderDependence as ODEP (ntsodFastPDom)
import qualified Data.Graph.Inductive.Query.TSCD         as TSCD (timdomsOf, timingCorrection, timingLeaksTransformation, tscdCostSlice, timDFCostFromUpLocalDefViaTimdoms, timDFCost, tscdOfLfp, timDF, timDFFromUpLocalDefViaTimdoms, timDFUpGivenXViaTimdomsDef, timDFUpGivenXViaTimdoms, timDFLocalDef, timDFLocalViaTimdoms, tscdOfNaiveCostfLfp, timdomOfLfp, tscdSlice, timdomsFromItimdomMultipleOf, validTimdomFor, validTimdomLfp,
    itimdomMultipleOfTwoFingerCost, cost1, cost1F,
    itimdomMultipleTwoFingercd, timDFFromFromItimdomMultipleOf,
    timdomOfNaiveLfp, timdomMultipleOfNaiveLfp,
    timDFFromFromItimdomMultipleOfFast, timDFFromFromItimdomMultipleOfFastCost, itimdomMultipleOfTwoFinger, timdomOfTwoFinger, tscdSliceFast, tscdSliceViaTimDF, timMultipleDFTwoFinger)
import qualified Data.Graph.Inductive.Query.PureTimingDependence as PTDEP (alternativeTimingSolvedF3dependence, timingSolvedF3dependence, timingF3dependence, timingF3EquationSystem', timingF3EquationSystem, snmTimingEquationSystem, timingSolvedF3sparseDependence, timingSnSolvedDependence, timingSnSolvedDependenceWorklist, timingSnSolvedDependenceWorklist2, enumerateTimingDependence, solveTimingEquationSystem, Reachability(..), timmaydomOfLfp, timingDependenceViaTwoFinger, nticdTimingSlice, ntscdTimingSlice, ptd, timingDependenceFromTimdom)

timingdep  = defaultMain                               $ testGroup "timingDep" [ mkTest [timingDepTests], mkProp [timingDepProps] ]
timingdepX = defaultMainWithIngredients [antXMLRunner] $ testGroup "timingDep" [ mkTest [timingDepTests], mkProp [timingDepProps] ]


timingDepProps = testGroup "(concerning timingDependence)" [
    testProperty "generate testCases in .dot file format"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    itimdomMultiple = TSCD.itimdomMultipleOfTwoFinger g
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    writeDot = do
                          let valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdomMultiple (Set.fromList $ nodes g)
                          
                          let dotG       = showDot (fglToDotGeneric (withNodes        g) show show id)
                          let dotItimdom = showDot (fglToDotGeneric (withNodes itimdomG) show show id)
                                where itimdomG = fromSuccMapWithEdgeAnnotation itimdomMultiple :: Gr () Integer
                          let dotValid   = showDot (fglToDotGeneric (withNodes   validG) show show id)
                                where validG   = mkGraph (labNodes g) [ (n,n, valid ! n) | n <- nodes g] :: Gr () Integer
                          let dotTSCD    = showDot (fglToDotGeneric (withNodes    tscdG) show show id)
                                where tscdG    = fromSuccMap $ (Map.fromList [(n, Set.empty) | n <- nodes g ]) ⊔ (invert'' $ TSCD.timDFFromFromItimdomMultipleOfFast g) :: Gr () ()
                          let dotTDEP    = showDot (fglToDotGeneric (withNodes    tdepG) show show id)
                                where tdepG    = fromSuccMap $ PTDEP.timingDependenceViaTwoFinger g :: Gr () ()
                          randomInt <- getStdRandom (randomR (1,65536)) :: IO Int
                          let fileG       = (show randomInt) ++ "-cfg.dot"
                          let fileItimdom = (show randomInt) ++ "-itimdom.dot"
                          let fileValid   = (show randomInt) ++ "-valid.dot"
                          let fileTSCD    = (show randomInt) ++ "-tscd.dot"
                          let fileTDEP    = (show randomInt) ++ "-tdep.dot"
                          writeFile fileG       dotG
                          writeFile fileItimdom dotItimdom
                          writeFile fileValid   dotValid
                          writeFile fileTSCD    dotTSCD
                          writeFile fileTDEP    dotTDEP
                in seq (unsafePerformIO writeDot) $ True,
    testProperty  "timingDependenceFromTimdom  == timingDependenceViaTwoFinger"
                $ \(ARBITRARY(g)) ->
                       -- let tdep           = PTDEP.timingSolvedF3dependence g
                       let tdepfromTwoFinger = Map.mapWithKey Set.delete $ PTDEP.timingDependenceViaTwoFinger g
                           tdepfromTimdom    = Map.mapWithKey Set.delete $ PTDEP.timingDependenceFromTimdom g
                       in  tdepfromTimdom == tdepfromTwoFinger,
    testProperty  "timingDependenceFromTimdom  == timingSolvedF3dependence for n /= m"
                $ \(ARBITRARY(g)) ->
                       -- let tdep           = PTDEP.timingSolvedF3dependence g
                       let tdep           = Map.mapWithKey Set.delete $ PTDEP.timingSolvedF3dependence g
                           tdepfromTimdom = Map.mapWithKey Set.delete $ PTDEP.timingDependenceFromTimdom g
                       in  tdepfromTimdom == tdep,
    testProperty "some prop"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom = TSCD.timdomOfLfp g
                    timdomnok = fmap (Set.map fst) $ timdom
                in (∀) (Map.assocs timdom) (\(n, m's) -> (∀) m's (\(m', steps) -> (∀) (timdom ! m') (\(m, steps') ->
                       if (m ∈ timdomnok ! n)   ∨  (n == m  ∨  m == m'  ∨  m' == n)  then True else (
                          True
                        ∧ (let dombefore' = PDOM.mdomOfLfp (delSuccessorEdges g m') in  not $ m  ∈ dombefore' ! n)
                        ∧ (let dombefore  = PDOM.mdomOfLfp (delSuccessorEdges g m ) in  not $ m' ∈ dombefore  ! n)
                        ∧ (∀) (suc g n) (\nr -> if       m ∈ timdomnok ! nr then True else traceShow ("nr", nr) (
                              (let dombefore' = PDOM.mdomOfLfp (delSuccessorEdges g m') in  not $ m  ∈ dombefore' ! nr)
                            ∧ (let dombefore  = PDOM.mdomOfLfp (delSuccessorEdges g m ) in  not $ m' ∈ dombefore  ! nr)
                          ))
                        ∧ (∀) (suc g n) (\nl -> if not $ m ∈ timdomnok ! nl then True else traceShow ("nl", nl) (
                              (let dombefore' = PDOM.mdomOfLfp (delSuccessorEdges g m') in        m  ∈ dombefore' ! nl)
                            ∨ (let dombefore  = PDOM.mdomOfLfp (delSuccessorEdges g m ) in        m' ∈ dombefore  ! nl)
                          ))
                       )
                ))),
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in reducible CFG"
    $ \(REDUCIBLE(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s) ok,
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in CFG with unique exit node"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let (_, g) = withUniqueEndNode () () generatedGraph
                    
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s) ok,
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in CFG with empty ntsod"
    $ \(REDUCIBLE(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    ntsod = ODEP.ntsodFastPDom   g
                    
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in ((∀) (Map.assocs ntsod) (\(_,ns) -> Set.null ns)) ==>
                   let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s, ntsod) ok,
    testProperty "timingCorrection tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size in CFG with unique exit node, but fixed examples"
    $ \seed1 seed2 seed3 -> (∀) interestingTimingDep (\(exampleName, example) ->
                let (_, g) = withUniqueEndNode () () example
                    (cost, _) = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms
                in let ok = s == s'
                   in if ok then ok else traceShow (g,ms,s',s) ok
                ),
    testProperty "timingLeaksTransformation tscdCostSlice == ntscdNTSODSlice for random slice criteria of random size, but fixed examples"
    $ \seed1 seed2 seed3 -> (∀) interestingTimingDep (\(exampleName, example) ->
                let g = example :: Gr () ()
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    
                    (cost, _) = TSCD.timingLeaksTransformation g cost0 ms
                      where cost0 = costFor g seed3
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g costF
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g
                    
                    s  = tscdcostslicer   ms
                    s' = ntscdntsodslicer ms


                in let ok = (s == s')
                   in if ok then ok else traceShow (g,ms,s',s) ok
                ),
    testProperty "timingCorrection tscdCostSlice g[ms -/> ] ms == ntscdNTSODSlice ms for random slice criteria of random size"
    $ \(ARBITRARY(generatedGraph)) seed1 seed2 seed3 ->
                let g = generatedGraph
                    n = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

                    cost0 = costFor g seed3
                    
                    (cost,   _) = TSCD.timingLeaksTransformation g   cost0 ms
                    costF n m = cost ! (n,m)
                    tscdcostslicer    = TSCD.tscdCostSlice           g   costF  
                    ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd g

                    g'' = foldr (flip delSuccessorEdges) g ms
                    (cost'', _) = TSCD.timingCorrection          g'' cost0
                    costF'' n m = cost'' ! (n,m)
                    tscdcostslicer''  = TSCD.tscdCostSlice           g'' costF''
                    ntscdslicer = SLICE.NTICD.ntscdSlice                g''
    
                    s    = tscdcostslicer    ms
                    s'   = ntscdntsodslicer  ms
                    s''  = tscdcostslicer''  ms
                    s''' = ntscdslicer       ms
                in let ok = (s == s') ∧ (s == s'') ∧ (s == s''') ∧ ((Map.keysSet cost ⊇ Map.keysSet cost'') ∧ (∀) (Map.assocs cost'') (\((n,m),k) -> cost ! (n,m) <= k))
                   in if ok then ok else traceShow (g,ms,cost0, s,s', s'') $ traceShow ("cost:",cost, cost'') $ ok,
    testProperty "timingCorrection itimdomMultiple"
    $ \(ARBITRARY(generatedGraph)) seed3 ->
                let g = generatedGraph
                    (cost, itimdomMultiple') = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    itimdomMultiple'' = TSCD.itimdomMultipleOfTwoFingerCost g (\n m -> cost ! (n,m))
                    noselfloops = Map.mapWithKey (\n ms -> Set.filter (\(m, k) -> m /= n) ms)
                in noselfloops itimdomMultiple'' == noselfloops itimdomMultiple',
    testProperty "timingCorrection imdom"
    $ \(ARBITRARY(generatedGraph)) seed3 ->
                let g = generatedGraph
                    (cost, itimdomMultiple') = TSCD.timingCorrection g cost0
                      where cost0 = costFor g seed3
                    itimdomMutliple'NoK = fmap (Set.map fst) itimdomMultiple'
                    imdom = PDOM.imdomOfTwoFinger6 g
                    -- noselfloops = Map.mapWithKey (\n ms -> Set.filter (/= n) ms)
                in (trc $ fromSuccMap $ itimdomMutliple'NoK :: Gr () ()) == (trc $ fromSuccMap $ imdom :: Gr () ()),
    testProperty "timdom implies mdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    mdom   = PDOM.mdomOfLfp g
                in timdom ⊑ mdom,
    testProperty "tscd implies dom"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    tscd = TSCD.tscdOfLfp g
                in (∀) (Map.assocs $  tscd) (\(n, ms) -> (∀) ms (\m -> (m == n) ∨ (not $ m ∈ timdom ! n))),
    testProperty "tscd implies onedome"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    onedom = PDOM.onedomOf timdom
                    tscd = TSCD.tscdOfLfp g
                in (∀) (Map.assocs $  tscd) (\(n, ms) -> (∀) ms (\m -> not $ m ∈ onedom n)),
    testProperty "fmap (Set.map fst) $ timdomOfLfp is transitive in reducible CFG"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                in (∀) (Map.assocs $  timdom) (\(x, ys) -> (∀) ys (\y -> (∀) (timdom ! y) (\z -> z ∈ timdom ! x ))),
    testProperty "fmap (Set.map fst) $ timdomOfLfp is transitive in unique exit node cfg"
    $ \(ARBITRARY(generatedGraph)) ->
                let (_, g) = withUniqueEndNode () () generatedGraph
                    timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                in (∀) (Map.assocs $  timdom) (\(x, ys) -> (∀) ys (\y -> (∀) (timdom ! y) (\z -> z ∈ timdom ! x ))),
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp via validTimdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g
                    valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdom (Set.fromList $ nodes g)
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                     let fuel = valid ! x in
                           (∀) ys (\(y, steps) -> (∀) (timdomMultipleNaive ! y) (\(z, steps') ->
                             -- (if (fuel > 1) then traceShow (steps + steps', fuel, steps + steps'  <= fuel) else id) $
                             ((z, (steps + steps'          )          ) ∈ timdom ! x)    ↔  (steps + steps'  <= fuel )
                           ))
                       ∧ (∀) [0..fuel-1] (\fuel' ->
                           not $
                           (∀) ys (\(y, steps) -> (∀) (timdomMultipleNaive ! y) (\(z, steps') ->
                             ((z, (steps + steps'          )          ) ∈ timdom ! x)    ↔  (steps + steps'  <= fuel')
                           ))
                         )
                   ),
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                         (∃) [0..n] (\fuel ->
                           (∀) ys (\(y, steps) -> (∀) (timdomMultipleNaive ! y) (\(z, steps') ->
                             ((z, (steps + steps'          )          ) ∈ timdom ! x)    ↔  (steps + steps'  <= fuel)
                           ))
                         )
                   ),
    testProperty "itimdom cycles vs timdom"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g

                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdom ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdom
                    cycleNodes = (∐) cycles
                in (∀) cycles (\cycle ->
                     let circumference = sum [ steps | m <- Set.toList cycle, (_,steps) <- Set.toList $  itimdom ! m]
                     in (∀) cycle (\m -> (∀) cycle (\m' -> 
                            False
                          ∨ (m == m')
                          ∨ (   (m' ∈ (Set.map fst $ timdom ! m ))
                              ∧ (m  ∈ (Set.map fst $ timdom ! m'))
                              ∧ (∀) (Set.filter ((==m') . fst) $ timdom ! m ) (\(_,k)  ->
                                (∀) (Set.filter ((==m ) . fst) $ timdom ! m') (\(_,k') ->
                                  (k + k' == circumference)
                                ))
                            )
                       ))
                    ),
    testProperty "timdomMultipleOfNaiveLfp step vs fuel"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g
                    valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdom (Set.fromList $ nodes g)

                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdom ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (cycleOf, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdom
                    cycleNodes = (∐) cycles
                in (∀) (Map.assocs itimdom) (\(m, m's) -> (∀) (m's) (\(m', steps) ->
                          False
                        ∨ (m == m')
                        ∨ (   (m' ∈ (Set.map fst $ timdom ! m ))
                            ∧ (m  ∈ (Set.map fst $ timdom ! m'))
                            ∧ (∀) (Set.filter ((==m') . fst) $ timdom ! m ) (\(_,k)  ->
                              (∀) (Set.filter ((==m ) . fst) $ timdom ! m') (\(_,k') ->
                                  True
                                ∧ (k == steps)
                                ∧ (k + k' == (valid ! m') + k)
                              ))
                          )
                        ∨ (m ∈ entries)
                        ∨ (valid ! m == valid ! m' + steps)
                   )),
    testProperty "validTimdomFor entries == validTimdomFor (nodes g) | entries "
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    itimdommultiple = TSCD.itimdomMultipleOfTwoFinger g
                    valid        = TSCD.validTimdomFor g (TSCD.cost1F g) itimdommultiple (Set.fromList $ nodes g)
                    validEntries = TSCD.validTimdomFor g (TSCD.cost1F g) itimdommultiple entries

                    entries = Set.fromList [ n | n <- nodes g, not $ n ∈ cycleNodes, (∃) (itimdommultiple ! n) (\(m,_) -> m ∈ cycleNodes) ]
                    (_, cycles) = findCyclesM $ fmap fromSet $ fmap (Set.map fst) $ itimdommultiple
                    cycleNodes = (∐) cycles
                in restrict valid entries == validEntries,
    testProperty "validTimdomFor == validTimdomLfp "
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    itimmultiple = TSCD.itimdomMultipleOfTwoFinger g
                    valid    = TSCD.validTimdomFor g (TSCD.cost1F g) itimmultiple (Set.fromList $ nodes g)
                    validlfp = TSCD.validTimdomLfp g 
                in valid == validlfp,
    testProperty "timdomMultipleOfNaiveLfp vs timdomOfLfp via validTimdom one step"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    n  = toInteger $     (length $ nodes g)
                    nr = toInteger $ 2 * (length $ nodes g)
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdom              = TSCD.timdomOfLfp              g

                    itimdom    = TSCD.itimdomMultipleOfTwoFinger g
                    valid = TSCD.validTimdomFor g (TSCD.cost1F g) itimdom (Set.fromList $ nodes g)
                in (∀) (Map.assocs timdomMultipleNaive) (\(x, ys) ->
                     let fuel = valid ! x in
                           (∀) ys (\(y, steps) ->
                             -- (if (fuel > 1) then traceShow (steps + steps', fuel, steps + steps'  <= fuel) else id) $
                             ((y, steps) ∈ timdom ! x)    ↔  (steps <= fuel )
                           )
                       ∧ (∀) [0..fuel-1] (\fuel' ->
                           not $
                           (∀) ys (\(y, steps) -> 
                             ((y, steps) ∈ timdom ! x)    ↔  (steps <= fuel')
                           )
                         )
                   ),
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
                   ),
    testProperty   "ntscdNTSODSlice ⊆ tscdSlice for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                          | n == 0 = Set.empty
                          | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        ntscdntsodslicer  = SLICE.NTICD.ntscdNTSODSliceViaNtscd   g
                        tscdslicer        = TSCD.tscdSliceFast g
                        subseteq = ntscdntsodslicer ms ⊆ tscdslicer ms
                    in  (if subseteq then id  else traceShow (ms, g)) subseteq,
    testPropertySized 40 "tscdSlice  == tscdSliceFast for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2->
                    let g = generatedGraph
                        n    = length $ nodes g
                        ms
                          | n == 0 = Set.empty
                          | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                        tscdslicer        = TSCD.tscdSlice     g
                        tscdslicerfast    = TSCD.tscdSliceFast g
                        same = tscdslicer ms == tscdslicerfast ms
                    in  (if same then id  else traceShow (ms, g)) same,
    testPropertySized 40 "tscdSlice  == tscdSliceViaTimDF for random slice-criteria of random size"
                $ \(ARBITRARY(generatedGraph)) seed1 seed2 ->
                    let g = generatedGraph
                        n    = length $ nodes g
                        tscdslicer        = TSCD.tscdSlice         g
                        tscdslicertimdf   = TSCD.tscdSliceViaTimDF g
                        seeds = zip (moreSeeds seed1 30) (moreSeeds seed2 30)
                    in (∀) seeds (\(seed1, seed2) ->
                         let ms
                               | n == 0 = Set.empty
                               | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                             same = tscdslicer ms == tscdslicertimdf ms
                         in  (if same then id  else traceShow (ms, g)) same
                       ),
    testProperty   "timDFFromFromItimdomMultipleOfFast == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromFromItimdomMultipleOfFast  g ==
                       TSCD.timDF                               g,
    testProperty   "timDFFromFromItimdomMultipleOf   == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromFromItimdomMultipleOf  g ==
                       TSCD.timDF                           g,
    testProperty   "timdomsFromItimdomMultipleOf     == timdomsOf"
                $ \(ARBITRARY(g)) ->
                       TSCD.timdomsFromItimdomMultipleOf  g ==
                       TSCD.timdomsOf                     g,
    testProperty   "timDFLocalViaTimdoms    == timDFLocalDef"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFLocalViaTimdoms  g ==
                       TSCD.timDFLocalDef         g,
    testProperty   "timDFUpGivenXViaTimdoms == timDFUpGivenXViaTimdomsDef"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFUpGivenXViaTimdoms    g ==
                       TSCD.timDFUpGivenXViaTimdomsDef g,
    testProperty   "timDFFromUpLocalDefViaTimdoms == timDF"
                $ \(ARBITRARY(g)) ->
                       TSCD.timDFFromUpLocalDefViaTimdoms g ==
                       TSCD.timDF                          g,
    testProperty   "timDFCostFromUpLocalDefViaTimdoms == timDFCost"
                $ \(ARBITRARY(g)) seed -> 
                       let cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in TSCD.timDFCostFromUpLocalDefViaTimdoms g costF ==
                          TSCD.timDFCost                         g costF,
    testPropertySized 40   "tscdOfLfp  == timDF"
                $ \(ARBITRARY(g)) ->
                       (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfLfp g) ==
                       (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDF    g)),
    testProperty "timdomMultipleOfNaiveLfp == timdom in unique exit node cfg"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                        timdom     = fmap (Set.map fst) $ TSCD.timdomOfLfp              g
                        timdomMult = fmap (Set.map fst) $ TSCD.timdomMultipleOfNaiveLfp g
                    in timdom == timdomMult,
    testProperty "timdom is cycle free in unique exit node cfg"
                $ \(ARBITRARY(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                        timdom     = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    in (∀) (Map.assocs timdom) (\(n,ms) -> (∀) ms (\m -> (n ∈ timdom ! m) → (n == m))),
    testProperty   "timMultipleDFTwoFinger == timDF in unique exit node cfg"
                $ \(ARBITRARY(generatedGraph)) ->
                       let (_, g) = withUniqueEndNode () () generatedGraph
                       in TSCD.timMultipleDFTwoFinger g == TSCD.timDF g,
    testPropertySized 40   "tscdOfNaiveCostLfp  == timDFFromFromItimdomMultipleOfFastCost"
                $ \(ARBITRARY(g)) seed ->
                       let cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfNaiveCostfLfp g costF) ==
                          (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDFFromFromItimdomMultipleOfFastCost g costF)),
    testProperty   "tscdOfNaiveCostLfp  == timDFFromFromItimdomMultipleOfFastCost for fixed examples"
                $ \seed -> (∀) interestingTimingDep (\(exampleName, example) ->
                       let g = example :: Gr () ()
                           cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfNaiveCostfLfp g costF) ==
                          (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDFFromFromItimdomMultipleOfFastCost g costF))),
    testPropertySized 40   "tscdOfNaiveCostLfp  == timDFCost"
                $ \(ARBITRARY(g)) seed ->
                       let cost = costFor g seed
                           costF n m = cost ! (n,m)
                       in (Map.mapWithKey (\n s -> Set.delete n s) $ TSCD.tscdOfNaiveCostfLfp g costF) ==
                          (Map.mapWithKey (\n s -> Set.delete n s) $ (Map.fromList [ (n, Set.empty) | n <- nodes g]) ⊔ (invert'' $ TSCD.timDFCost g costF)),
    testPropertySized 40 "timdoms* == timdom in reducible cfg"
    $ \(REDUCIBLE(generatedGraph)) ->
                    let g = generatedGraph
                        timdom     = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                        timdoms    =                      TSCD.timdomsOf   g
                        timdomsTrc = toSuccMap $ trc $ (fromSuccMap timdoms :: Gr () ())
                    in timdom == timdomsTrc,
    testPropertySized 40 "timdoms* == timdom in unique exit node cfg"
    $ \(ARBITRARY(generatedGraph)) ->
                    let (_, g) = withUniqueEndNode () () generatedGraph
                        timdom     = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                        timdoms    =                      TSCD.timdomsOf   g
                        timdomsTrc = toSuccMap $ trc $ (fromSuccMap timdoms :: Gr () ())
                    in timdom == timdomsTrc,
    testPropertySized 40 "stepsCL timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    in PDF.stepsCL g timdom,
    testPropertySized 40 "noJoins timdomOfLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                    let g = generatedGraph
                        timdom = fmap (Set.map fst) $ TSCD.timdomOfLfp g
                    in PDF.noJoins g timdom,
    testProperty "timdomOfLfp is unique"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom  = TSCD.timdomOfLfp      g
                in (∀) (Map.assocs timdom) (\(n, ms) -> (∀) ms (\(m, steps) -> (∀) ms (\(m', steps') ->  (m == m')  →  (steps == steps')))),
    testProperty "timdomOfLfp == timdomOfNaiveLfp"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom  = TSCD.timdomOfLfp      g
                    timdom' = TSCD.timdomOfNaiveLfp g
                in timdom == timdom',
    testProperty "itimdomMultipleTwoFingercd == tscdOfLfp in graphs without non-trivial sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = TRANS.sinkShrinkedGraphNoNewExitForSinks generatedGraph (controlSinks generatedGraph)
                in TSCD.itimdomMultipleTwoFingercd g == Map.mapWithKey Set.delete (TSCD.tscdOfLfp g),
    testProperty "timdomOfLfp is transitive up to cycles for reducible cfg"
    $ \(REDUCIBLE(generatedGraph)) ->
                let g = generatedGraph
                    timdom = TSCD.timdomOfLfp g
                in (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                                                                      (z, (steps + steps'          )          ) ∈ timdom ! x
                     ∨ (∃) (timdom ! z) (\(y',steps'') -> y' == y  ∧  (z, (steps          - steps'')          ) ∈ timdom ! x)
                ))),
    testProperty "timdomOfLfp is transitive up to cycles"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom = TSCD.timdomOfLfp g
                in (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                                                                      (z, (steps + steps'          )          ) ∈ timdom ! x
                     ∨ (∃) (timdom ! z) (\(y',steps'') -> y' == y  ∧  (z, (steps          - steps'')          ) ∈ timdom ! x)
                     ∨ (∃) (timdom ! z) (\(y',steps'') -> y' == y) ∧  (not $ ((∃) (timdom ! z) (\(x', _) -> x' == x)))
                ))),
    testProperty "timdomMultipleOfNaiveLfp == itimdomMultipleOfTwoFinger^*"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    nr = toInteger $ 2 * (length $ nodes g)
                    itimdomMultiple = TSCD.itimdomMultipleOfTwoFinger g
                    timdomMultipleNaive = TSCD.timdomMultipleOfNaiveLfp g
                    timdomMultipleFinger = Map.fromList [ (n, Set.fromList [ (m, steps) | m <- nodes g, path <- pathsUpToLength itimdomMultiple nr n m, let steps = sum $ fmap snd path ]) | n <- nodes g]
                in timdomMultipleNaive == timdomMultipleFinger,
    testProperty "timdomOfLfp == timdomOfTwoFinger"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    timdom  = TSCD.timdomOfLfp g
                    timdom' = TSCD.timdomOfTwoFinger g
                in timdom == timdom',
    testProperty "timdomOfLfp is transitive in graphs without non-trivial sinks"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = TRANS.sinkShrinkedGraphNoNewExitForSinks generatedGraph (controlSinks generatedGraph)
                    timdom = TSCD.timdomOfLfp g
                in (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                       (z, steps+steps') ∈ timdom ! x
                ))),
    testProperty "timdomOfLfp is transitive in graphs without imdom cycles"
    $ \(ARBITRARY(generatedGraph)) ->
                let g = generatedGraph
                    imdom = PDOM.imdomOfTwoFinger6 g
                    cycles = snd $ findCyclesM $ fmap fromSet $ imdom
                    timdom = TSCD.timdomOfLfp g
                in  List.null cycles ==>
                    (∀) (Map.assocs timdom) (\(x, ys) -> (∀) ys (\(y, steps) -> (∀) (timdom ! y) (\(z, steps') ->
                       (z, steps+steps') ∈ timdom ! x
                ))),
    testProperty "nticdTimingSlice == ntscdTimingSlice == tscdSlice == tscdSliceFast "
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
                   ),
    testProperty "nticdTimingSlice == ntscdTimingSlice == tscdSlice == tscdSliceFast for random slice-criteria of random size"
    $ \(ARBITRARY(generatedGraph))  seed1 seed2 ->
                let g    = generatedGraph
                    n    = length $ nodes g
                    ms
                      | n == 0 = Set.empty
                      | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]
                    ntscdtimingslicer  = PTDEP.ntscdTimingSlice g
                    nticdtimingslicer  = PTDEP.nticdTimingSlice g
                    tscdslicer         = TSCD.tscdSlice        g
                    tscdslicerfast     = TSCD.tscdSliceFast    g
                    s1 = nticdtimingslicer ms
                    s2 = ntscdtimingslicer ms
                    s3 = tscdslicer        ms
                    s4 = tscdslicerfast    ms
                in s1 == s2  ∧  s2 == s3  ∧  s3 == s4,
    testPropertySized 35 "tscdSlice is minimal wrt. timed traces and termination"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        ms = Set.fromList $ sampleFrom seed (max 1 $ abs $ seed2 `mod` (max 1 $ n `div` 2)) (nodes g)
                        s = TSCD.tscdSlice g ms
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (∀) s (\n -> n ∈ ms ∨
                         let s' = Set.delete n s
                             differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s') (condNodes ∖ s') in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentTimed g s input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in different
                                  )
                               ))
                         in (if differentobservation then id else traceShow (ms, n, differentobservation)) $
                            differentobservation
                       ),
    testPropertySized 25 "tscdSlice  is sound wrt. timed traces and termination"
                $ \(ARBITRARY(generatedGraph)) seed seed2 ->
                    let g = withoutSelfEdges $ removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        ms = Set.fromList $ sampleFrom seed (max 1 $ abs $ seed2 `mod` (max 1 $ n `div` 2)) (nodes g)
                        s = TSCD.tscdSlice g ms
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowEquivalentTimed g s input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in (if not $ different then id else traceShow (ms, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in -- traceShow (length $ nodes g, Set.size s, Set.size ms, Set.size condNodes, Set.size $ (condNodes ∩ (Set.fromList $ rdfs (Set.toList ms) g)) ∖ s) $
                       (if not $ differentobservation then id else traceShow (ms, differentobservation)) $
                       not differentobservation,
    testPropertySized 20 "timingSolvedF3dependence  is sound wrt. timed traces"
                $ \(ARBITRARY(generatedGraph)) seed->
                    let g = removeDuplicateEdges generatedGraph -- removal is only a runtime optimization
                        n = toInteger $ length $ nodes g
                        condNodes  = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
                        choices    = InfiniteDelay.allChoices g Map.empty condNodes
                        [m1,m2]    = sampleFrom seed 2 (nodes g)
                        ms = Set.fromList [m1,m2]
                        s = ms ⊔ Set.fromList [n | (n, ms') <- Map.assocs $ PTDEP.timingSolvedF3dependence g, (∃) ms (\m -> m ∈ ms')]
                        differentobservation = (∃) choices (\choice -> let choices' = InfiniteDelay.allChoices g (restrict choice s) (condNodes ∖ s) in (∃) (nodes g) (\startNode -> 
                               let input = InfiniteDelay.Input startNode choice
                                   isLowEquivalent = InfiniteDelay.isLowTimingEquivalent g s input
                               in (∃) choices' (\choice' ->
                                    let input' = InfiniteDelay.Input startNode choice'
                                        different = not $ isLowEquivalent input'
                                     in (if not $ different then id else traceShow (m1,m2, startNode, choice, choice', g)) $
                                        different
                                  )
                               ))
                    in -- traceShow (length $ nodes g, Set.size s, Set.size condNodes) $
                       (if not $ differentobservation then id else traceShow (m1, m2, differentobservation)) $
                       not differentobservation,
    testPropertySized 30  "the  solved timingF3EquationSystem is correct"
                $ \(ARBITRARY(g)) ->
                       let timingEqSolved    = PTDEP.solveTimingEquationSystem $ PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem
                           trcG = trc g
                           pathsBetween     = PBETWEEN.pathsBetween        g trcG
                           pathsBetweenUpTo = PBETWEEN.pathsBetweenUpTo    g trcG
                       in  -- traceShow g $
                           (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in (m /= p) →
                                  let paths = pathsBetween p m in
                                  -- traceShow (m,p, rmq) $
                                  case rmq of
                                     PTDEP.FixedStepsPlusOther s y ->
                                                                      let paths = pathsBetweenUpTo p m y in
                                                                      (∀) paths (\(hasLoop,  path ) -> y `elem` path ∧ (toInteger (length $ takeWhile (/= y) path)) == s + 1)
                                     PTDEP.FixedSteps s            -> (∀) paths (\(hasLoop,  path ) -> (not hasLoop) ∧ (toInteger (length                    path)) == s + 2)
                                     PTDEP.UndeterminedSteps       -> (∃) paths (\(hasLoop,  path ) -> hasLoop)
                                                                    ∨ (∃) paths (\(hasLoop1, path1) -> (not hasLoop1) ∧
                                                                          (∃) paths (\(hasLoop2, path2) -> (not hasLoop2) ∧ length (path1) /= (length path2))
                                                                      )
                                     PTDEP.Unreachable             -> paths == []
                           ),
    testProperty  "prevCondsWithSuccNode  ==  prevCondsWithSuccNode'"
                $ \(ARBITRARY(g)) -> (∀) (nodes g) (\n -> 
                       (List.sort $ prevCondsWithSuccNode  g n) ==
                       (List.sort $ prevCondsWithSuccNode' g n)
                  ),
    testProperty  "timingSnSolvedDependence         == enumerateTimingDependence"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSnSolvedDependence  g ==
                       PTDEP.enumerateTimingDependence g,
    testProperty  "timingSnSolvedDependence         == timingSnSolvedDependenceWorklist"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSnSolvedDependence          g ==
                       PTDEP.timingSnSolvedDependenceWorklist  g,
    testProperty  "timingSnSolvedDependence         == timingSnSolvedDependenceWorklist2"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSnSolvedDependence          g ==
                       PTDEP.timingSnSolvedDependenceWorklist2 g,
    testProperty  "timingSolvedF3dependence == timingSnSolvedDependenceWorklist"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSolvedF3dependence g ==
                       PTDEP.timingSnSolvedDependenceWorklist g,
    testProperty  "timingSolvedF3dependence == timingSnSolvedDependence"
                $ \(ARBITRARY(g)) -> 
                       PTDEP.timingSolvedF3dependence g ==
                       PTDEP.timingSnSolvedDependence g,
    testProperty  "timmaydomOfLfp            relates to solved timingF3EquationSystem"
                $ \(ARBITRARY(g)) ->
                       let timingEqSolved    = PTDEP.solveTimingEquationSystem $ PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem
                           timmaydomOfLfp    = PTDEP.timmaydomOfLfp g
                       in  (∀) (Map.assocs timingEqSolved) (\((m,p), smp) ->
                             let rmq = (∐) [ r | r <- Map.elems smp ]
                             in (m /= p) →
                                  case rmq of
                                     PTDEP.FixedSteps s            -> Set.fromList [1+s] == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                                     PTDEP.FixedStepsPlusOther s y -> Set.fromList [1+s] == Set.fromList [ steps | (y', steps) <- Set.toList $ timmaydomOfLfp ! p, y == y']
                                     PTDEP.UndeterminedSteps       -> Set.fromList []    == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                                     PTDEP.Unreachable             -> smp == Map.empty ∧
                                                                      Set.fromList []    == Set.fromList [ steps | (m', steps) <- Set.toList $ timmaydomOfLfp ! p, m == m']
                           ),
    testProperty  "itimdomMultipleOfTwoFinger^* {no loop}  == timdomOfLfp for graphs without itimdomMultiple cycles"
                $ \(ARBITRARY(g)) ->
                       let itimdomMultiple   = TSCD.itimdomMultipleOfTwoFinger g
                           timdomOfLfp       = TSCD.timdomOfLfp g
                           mustReachFromIn   = reachableFromIn $ fmap (Set.map (\(x,steps) -> (x,(steps, Set.empty)))) $ itimdomMultiple

                           imdom = PDOM.imdomOfTwoFinger6 g
                           cycles = snd $ findCyclesM $ fmap (fromSet . Set.map fst ) $ itimdomMultiple
                       in  List.null cycles ==>
                           (∀) (Map.assocs timdomOfLfp) (\(n, ms) ->
                              (∀) (ms) (\(m,steps) -> Set.fromList [steps] == mustReachFromIn n m)
                           )
                         ∧ (∀) (nodes g) (\n -> (∀) (nodes g) (\m ->
                              mustReachFromIn n m == Set.fromList [ steps | (m', steps) <- Set.toList $ timdomOfLfp ! n, m == m']
                           ))
                         ∧ (timdomOfLfp  ==  Map.fromList [ (n, Set.fromList [ (m, steps) | m <- nodes g, path <- minimalPath itimdomMultiple n m, let steps = sum $ fmap snd path ]) | n <- nodes g]),
    testProperty  "timingF3EquationSystem'  == timingF3EquationSystem"
                $ \(ARBITRARY(g)) ->
                       let timingEq        = PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem
                           timingEq'       = PTDEP.snmTimingEquationSystem g PTDEP.timingF3EquationSystem'
                       in  timingEq         == timingEq',
    testProperty  "timingF3dependence is transitive"
                $ \(ARBITRARY(g)) ->
                       let tdep    = PTDEP.timingF3dependence g
                       in (∀) (nodes g) (\n ->
                            (∀) (tdep ! n) (\n' ->
                              (∀) (tdep ! n') (\n'' ->
                                  (n'' == n)
                                ∨ (n'' ∈ tdep ! n)
                              )
                            )
                          ),
    testProperty  "timingSolvedF3dependence is transitive"
                $ \(ARBITRARY(g)) ->
                       let tdep    = PTDEP.timingSolvedF3dependence g
                       in (∀) (nodes g) (\n ->
                            (∀) (tdep ! n) (\n' ->
                              (∀) (tdep ! n') (\n'' ->
                                  (n'' == n)
                                ∨ (n'' ∈ tdep ! n)
                              )
                            )
                          ),
    testProperty  "timingDependenceViaTwoFinger        == timingSolvedF3dependence ∪ {(n,n) | n ∈ nodes}"
                $ \(ARBITRARY(g)) ->
                       let tdep             = PTDEP.timingSolvedF3dependence g
                           tdepviatwofinger = PTDEP.timingDependenceViaTwoFinger g
                       in  tdepviatwofinger == tdep ⊔ Map.fromList [(n, Set.fromList [n]) | n <- nodes g ],
    testProperty  "alternativeTimingSolvedF3dependence == timingSolvedF3dependence"
                $ \(ARBITRARY(g)) ->
                       let tdep            = PTDEP.timingSolvedF3dependence g
                           alternativetdep = PTDEP.alternativeTimingSolvedF3dependence g
                       in  alternativetdep == tdep,
    testProperty  "timingSolvedF3sparseDependence^*    == timingSolvedF3dependence ∪ {(n,n) | n ∈ nodes}"
                $ \(ARBITRARY(g)) ->
                       let tdep             = PTDEP.timingSolvedF3dependence g
                           tdepsparse       = PTDEP.timingSolvedF3sparseDependence g
                       in (trc $ fromSuccMap $ tdepsparse :: Gr () ()) ==
                          (      fromSuccMap $ tdep ⊔ Map.fromList [(n, Set.fromList [n]) | n <- nodes g ]),
    testProperty  "timingSolvedF3dependence ⊑ timingF3dependence"
                $ \(ARBITRARY(g)) ->
                       PTDEP.timingSolvedF3dependence g ⊑
                       PTDEP.timingF3dependence       g,
    testProperty  "timingF3dependence       ⊑ timingDependenceOld"
                $ \(ARBITRARY(g)) ->
                       let gCfg = emap (\() -> NoOp) g in
                       PTDEP.timingF3dependence       g ⊑
                             timingDependenceOld      gCfg,
    testPropertySized 40 "timingDependence         ⊑ timingDependenceOld"
                $ \generated -> let p :: Program Gr = toProgramIntra generated
                                    g = tcfg p
                                    td    = timingDependence g
                                    tdOld = timingDependenceOld g
                                    count = Map.foldr (\s k -> Set.size s + k) 0
                                    ts ok = traceShow (count td, count tdOld) $ if ok then ok else traceShow g $ ok
                                in td ⊑ tdOld
  ]

timingDepTests = testGroup "(concerning timingDependence)" $
  [  testCase    ("timingCorrection itimdomMultiple for " ++ exampleName)
            $   let (cost, itimdomMultiple') = TSCD.timingCorrection g (TSCD.cost1 g)
                    itimdomMultiple'' = TSCD.itimdomMultipleOfTwoFingerCost g (\n m -> cost ! (n,m))
                    noselfloops = Map.mapWithKey (\n ms -> Set.filter (\(m, k) -> m /= n) ms)
                in noselfloops itimdomMultiple'' == noselfloops itimdomMultiple' @? ""
  | (exampleName, g) <- interestingTimingDep ++ interestingIsinkdomTwoFinger
  ] ++
  [  testCase    ("timingCorrection imdom for " ++ exampleName)
            $   let (cost, itimdomMultiple') = TSCD.timingCorrection g (TSCD.cost1 g)
                    itimdomMutliple'NoK = fmap (Set.map fst) itimdomMultiple'
                    imdom = PDOM.imdomOfTwoFinger6 g
                in (trc $ fromSuccMap $ itimdomMutliple'NoK :: Gr () ()) == (trc $ fromSuccMap $ imdom :: Gr () ()) @? ""
  | (exampleName, g) <- interestingTimingDep ++ interestingIsinkdomTwoFinger
  ] ++
  []
