{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Program.Tests where

import System.Process

import Data.Graph.Inductive.Dot

import Data.Array (array)
import Data.List

import Data.Maybe (fromJust)

import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)
import Data.Dequeue.SimpleDequeue (SimpleDequeue)

import qualified Data.PQueue.Prio.Max as Prio.Max

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random
import Control.Monad(forM_, when, forever, forM)
import Test.QuickCheck
import Test.QuickCheck.Random (mkQCGen)
import Test.QuickCheck.Gen (Gen(MkGen))


import Program.Typing.FlexibleSchedulerIndependentChannels
import qualified Program.Typing.ResumptionBasedSecurity as Res

import Program.For
import Program
import Program.Defaults
import Program.Examples
import Program.MultiThread
import Program.MHP
import Program.CDom
import Program.Analysis
import Program.DynamicAnalysis (isSecureEmpirically, isSecureEmpiricallyCombinedTest)
import Program.Generator (GeneratedProgram(..), toCode, toProgram,
                          IntraGeneratedProgram(..), toCodeIntra, toProgramIntra,
                          SimpleProgram(..), toCodeSimple, toProgramSimple,
                          SimpleCFG(..),
                          Generated(..))
import Program.TransitionSystem

import Program.Properties.CDom


import IRLSOD
import Execution
import ExecutionTree
import PNI
import Unicode
import Util

import Algebra.Lattice

import qualified Data.Graph.Inductive.FA as FA
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.ProgramDependence
import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.LCA
import Data.Graph.Inductive.Query.PostDominance
import Data.Graph.Inductive.Query.PostDominance.Numbered
import Data.Graph.Inductive.Query.NTICD
import Data.Graph.Inductive.Query.OrderDependence
import Data.Graph.Inductive.Query.NTIODSlice
import Data.Graph.Inductive.Query.InfiniteDelay
import qualified Data.Graph.Inductive.Query.FCACD as FCACD
import Data.Graph.Inductive.Query.TimingDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.DataConflict
import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.BalancedSCC
import Data.Graph.Inductive.Arbitrary


import Data.Tree

import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Arbitrary.Reducible

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set



main = let { p = toProgramIntra someGen3 :: Program Gr } in  do { putStrLn $ show $ isSecureTimingClassificationAtUses p ; return $ isSecureEmpiricallyCombinedTest p }

showCdomChef p = [ ((n,n'),c) | ((n,n'),c) <- Map.toList $ idomChef p, mhpFor p ! (n,n') == True]


showGraph g = do
  let dot = showDot (fglToDot g)
  randomInt <- getStdRandom (randomR (1,65536)) :: IO Int
  let file = "file" ++ (show randomInt) ++ ".dot"
  writeFile file dot
  runInteractiveCommand $ "xdot " ++ file

showPDG p = showGraph $ programDependenceGraphP p
showcPDG p = showGraph $ concurrentProgramDependenceGraphP p mhp
  where mhp = mhpSetFor p
showCFG p = showGraph $ tcfg p
-- showSDGSimp sdg = showGraph $ efilter f sdg
--   where f (_,_, SummaryDependence) = True
--         f (_,_, ParameterInDependence)   = True
--         f (_,_, ParameterOutDependence)  = True
--         f (_,_, CallDependence)          = True
--         f (_,_, ControlDependence)       = True
--         f _                              = False
showTDG p = showGraph $ timingDependenceGraphP p
showConflicts p = showGraph $ dataConflictGraphP p
showInterIDomGraph gr s = showGraph $ withNodes $ trrAcyclic $ ( fromPredMap (interDom gr s) :: Gr () ())
showInterIDomGraphGeneral gr s = showGraph $ withNodes $ trrAcyclic $ ( fromPredMap (interDomGeneral summary gr s) :: Gr () ())
  where summary = sameLevelSummaryGraph'WithBs gr

withNodes :: (Graph gr) => gr a b -> gr (Node,a) b
withNodes g =  mkGraph [(n,(n,l)) | (n,l) <- labNodes g]
                       (labEdges g)

investigate s gr = do
  showGraph $ withNodes $ gr
  showInterIDomGraph gr s
  putStrLn $ show $ chopsInterIDomAreChopsCounterExamples (InterCFG s gr)
  


showDomTree cdomComputation p = showGraph idom

  where
    cdom = cdomComputation p
    idom = insEdge (entry,entry,()) $ idomToTree cdom
    entry = entryOf p $ procedureOf p $ mainThread p

p :: Program Gr
-- p = cdomIsBroken'
-- p = figure5right'
-- p = someGeneratedProgram
-- p = timingSecureButNotCombinedTimingSecure
-- p = aSecureGeneratedProgram
-- p = anotherGeneratedProgram
-- p = rofllol
-- p = minimalClassificationVstimingClassificationDomPathsCounterExample2Essential
-- p = notReallyUnsound8
-- p = timingVsFSI3
-- p = notReallyUnsound9
-- p = notReallyUnsound21
-- p = minimalClassificationVstimingClassificationDomPathsCounterExampleMartin
p = toProgramIntra someGen6'
  
testSinkPaths = do
  (CG _ generatedGraph) <- (generate $ resize 40 arbitrary :: IO ((Connected Gr () ())))
  --(NME generatedGraph) <- (generate $ resize 30 arbitrary :: IO ((NoMultipleEdges Gr () ())))
  showGraph $ withNodes $ withoutMultipeEdges generatedGraph
  let n = head $ nodes generatedGraph
  forM ((sinkPathsFor generatedGraph) ! n) (\p -> putStrLn $ show (n,p))
mainEquiv p = do
  putStrLn $ show $ length $ allFinishedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquiv p defaultInput defaultInput'

mainEquivAnnotated p = do
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquivAnnotated p defaultInput defaultInput'

mainEquivAnnotatedSampled p = do
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquivAnnotatedSampled p defaultInput defaultInput'

mainEquivAnnotatedSome p = do
  showCounterExamplesPniForEquivAnnotatedSome 7500 p defaultInput defaultInput'


withoutMultipeEdges :: (Eq b ,DynGraph gr) => gr a b -> gr a b
withoutMultipeEdges g =
  mkGraph (labNodes g) [ (n,m,e) | (n,m,e) <- nub $ labEdges g]

mainFindMorePrecise = forever $ showMorePrecise isSecureTimingClassification isSecureTimingCombinedTimingClassification
mainFindUnsound     = forever $ showMorePrecise isSecureTimingClassification isSecureEmpirically

showMorePrecise :: (Program Gr -> Bool) -> (Program Gr -> Bool) -> IO ()
showMorePrecise a1 a2 = do
    generated <- sample' (arbitrary :: Gen GeneratedProgram)
    forM_ generated (\gen -> do
       let p :: Program Gr = toProgram gen
       let sec1 = a1  p
       let sec2 = a2 p

       putStrLn $ show $ toCode gen

       putStr "a1: "
       putStrLn $ show $ sec1

       putStr "a2: "
       putStrLn $ show $ sec2

       when (sec1 ∧ ((¬) sec2)) $ do
--       when (sec1 /= sec2) $ do
         showCFG p
         return ()

       putStrLn ""
     )



genAndShowSimpleTransitionSystem = do
    generatedSimples <- sample' (arbitrary :: Gen SimpleProgram)
--    let simple = generatedSimples !! (length generatedSimples `div` 4)
    -- let simple = SimpleProgram (Map.fromList [(1,Generated (Seq Skip (ForC 2 (Seq (Seq (Seq (Ass "h" (Times (Var "x") (Var "h"))) (Ass "x" (Times (Var "x") (Var "z")))) (Seq Skip (Ass "z" (Times (Var "x") (Var "z"))))) (Seq (If (Leq (Val 0) (Times (Var "y") (Var "z"))) Skip Skip) (Seq Skip (Ass "h" (Times (Var "x") (Var "h")))))))) (Set.fromList ["h","x","y","z"]) (Map.fromList []))])
    -- let simple = SimpleProgram (Map.fromList [(1,Generated (Seq Skip (Seq (ForC 1 (Seq (ForC 2 (Ass "z" (Times (Var "x") (Var "x")))) (ForV (Global "z") (Ass "h" (Times (Var "x") (Var "y")))))) (Seq (Seq (Seq (Ass "z" (Times (Var "y") (Var "h"))) (Ass "z" (Times (Var "x") (Var "z")))) (If (Leq (Val 0) (Times (Var "z") (Var "z"))) (Ass "h" (Times (Var "z") (Var "z"))) Skip)) (If (Leq (Val 0) (Times (Var "x") (Var "y"))) (Seq Skip Skip) (ForV (Global "y") (Ass "h" (Times (Var "y") (Var "x")))))))) (Set.fromList ["h","x","y","z"]) (Map.fromList []))])
    let simple = SimpleProgram (Map.fromList [(1, "1")]) (Map.fromList [("1", Generated (Seq Skip (ForC 1 (Seq (Seq (ForC 2 (Ass (Global "h") (Times (Var (Global "h")) (Var (Global "h"))))) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "h")))) (Ass (Global "y") (Times (Var (Global "z")) (Var (Global "y")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "h")) (Var (Global "z")))) (Ass (Global "h") (Times (Var (Global "x")) (Var (Global "y")))) (Ass (Global "x") (Times (Var (Global "z")) (Var (Global "h"))))) (ForC 2 Skip))))) (Set.map Global $ Set.fromList ["h","x","y","z"]) (Map.fromList []) (Map.empty) )])

    let p :: Program Gr = toProgramSimple $ simple
    let low  = Set.map Global (Set.fromList ["x", "y", "z"]) ∩ vars p
    let high = Set.map Global (Set.fromList ["a", "b", "c"]) ∩ vars p
    showCFG   $ p
    showGraph $ fromSimpleProgram p
    putStrLn  $ "secureSymbolic: " ++ (show $ secureSymbolic low high p)
    putStrLn  $ "securePDG:      " ++ (show $ securePDG (vars p) low high simple)



showSimpleTransitionSystem = do
    let p :: Program Gr = simple2
    let low  = Set.map Global (Set.fromList ["z"]) ∩ vars p
    let high = Set.map Global (Set.fromList ["a", "b", "c"]) ∩ vars p
    showCFG   $ p
    showGraph $ fromSimpleProgram p
    putStrLn  $ "secureSymbolic: " ++ (show $ secureSymbolic low high p)


showConcreteTransitionSystem = do
    let p :: Program Gr = simple
    let low  = Set.map Global (Set.fromList ["z"]) ∩ vars p
    let high = Set.map Global (Set.fromList ["a", "b", "c"]) ∩ vars p
    let system = concreteFromSimpleProgram p
    let obs = observablePartOfConcrete (vars p)
                                       (entryOf p $ procedureOf p $ mainThread p)
                                       (exitOf  p $ procedureOf p $ mainThread p)
                                       low
                                       system
    showCFG   $ p
    showGraph $ system
--  showGraph $ trc system
    showGraph $ obs

--    putStrLn  $ "secureSymbolic: " ++ (show $ secureSymbolic low high p)


genAndShowSimpleTwoValuTransitionSystem = do
    generatedSimples <- sample' (arbitrary :: Gen SimpleProgram)
    let simple = generatedSimples !! (length generatedSimples `div` 4)
    let p :: Program Gr = toProgramSimple $ simple
    let system = twoValueFromSimpleProgram p
    let obs = observablePartOfTwoValueDefUseSimple (vars p)
                                                   (entryOf p $ procedureOf p $ mainThread p)
                                                   (exitOf  p $ procedureOf p $ mainThread p)
                                                   (Set.map Global (Set.fromList ["x", "y", "z"]) ∩ vars p)
                                                   system
    showCFG   $ p
    showGraph $ system
    showGraph $ obs


showSimpleTwoValueTransitionSystem = do
    -- let p = simple2
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (ForC 2 Skip) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (Ass (Global "z") (Times (Var (Global "b")) (Var (Global "z")))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    -- let p = (toProgramSimple $  SimpleProgram (Map.fromList [(1,Generated (Seq (ForV (Global "b") (Seq (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "a"))))) (ForC 1 Skip))) (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "z")))) (Seq (Ass (Global "y") (Times (Var (Global "z")) (Var (Global "c")))) (Ass (Global "x") (Times (Var (Global "a")) (Var (Global "x"))))) (ForV (Global "b") (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "x")))))) (Seq (ForV (Global "c") (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "a"))))) (Seq Skip (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "z")))))))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1, "1")])  (Map.fromList [("1",Generated (Seq Skip (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "z")) (Var (Global "x")))) (Ass (Global "h") (Times (Var (Global "h")) (Var (Global "x")))))) (Set.map Global $ Set.fromList ["h","x","y","z"]) (Map.fromList []) (Map.empty))])) :: Program Gr

    let system = twoValueFromSimpleProgram p
    -- let low = (Set.fromList ["z"])
    let low =  Set.map Global (Set.fromList ["x", "y", "z"]) ∩ vars p
    let obs = observablePartOfTwoValueDefUseSimple (vars p)
                                                   (entryOf p $ procedureOf p $ mainThread p)
                                                   (exitOf  p $ procedureOf p $ mainThread p)
                                                   low
                                                   system
    showCFG   $ p
    showGraph $ system
    showGraph $ obs
    putStrLn  $ "secure: " ++ (show $ secureTwoValueDefUse low p)

showSimpleOneValueTransitionSystem = do
    -- let p = simple2
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (ForC 2 Skip) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (Ass (Global "z") (Times (Var (Global "b")) (Var (Global "z")))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    --let p = (toProgramSimple $  SimpleProgram (Map.fromList [(1,Generated (Seq (ForV (Global "b") (Seq (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "a"))))) (ForC 1 Skip))) (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "z")))) (Seq (Ass (Global "y") (Times (Var (Global "z")) (Var (Global "c")))) (Ass (Global "x") (Times (Var (Global "a")) (Var (Global "x"))))) (ForV (Global "b") (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "x")))))) (Seq (ForV (Global "c") (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "a"))))) (Seq Skip (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "z")))))))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1, "1")])  (Map.fromList [("1",Generated (Seq Skip (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "z")) (Var (Global "x")))) (Ass (Global "h") (Times (Var (Global "h")) (Var (Global "x")))))) (Set.map Global $ Set.fromList ["h","x","y","z"]) (Map.fromList []) (Map.empty))])) :: Program Gr
    let system = oneValueFromSimpleProgram p
    -- let low = (Set.fromList ["z"])
    let low = Set.map Global (Set.fromList ["x", "y", "z"]) ∩ vars p
    let obs = observablePartOfOneValueDefUseSimple (vars p)
                                                   (entryOf p $ procedureOf p $ mainThread p)
                                                   (exitOf  p $ procedureOf p $ mainThread p)
                                                   low
                                                   system
    showCFG   $ p
    showGraph $ system
    showGraph $ obs
    putStrLn  $ "secure: " ++ (show $ secureOneValueDefUse low p)


timingVsFSI :: GeneratedProgram
timingVsFSI = GeneratedProgram (Map.fromList [(1, "1"), (2, "2")]) (Map.fromList [
    ("1",Generated (Seq (Seq (Seq (Seq
            (Ass (Global "y") (Val 0))
            (Ass (Global "a") (Times (Var (Global "y")) (Var (Global "y")))))
       (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "y"))) "stdOut")
            (SpawnThread 2)))
  (Seq (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut")
            (ReadFromChannel (Global "x") "stdIn"))
            (ForV (Global "x") Skip)))
            (ForV (Global "y")
               (ForV (Global "x")
                  (Seq (ReadFromChannel (Global "z") "stdIn")
                        Skip))))
       (Set.map Global $ Set.fromList ["a","x","y"])
       (Map.fromList [(2,  Set.map Global $ Set.fromList ["a","y"])])
       (Map.empty)
    ),
    ("2",Generated
            (ForV (Global "a")
               (ForC 1 (
                   ForC 1
                     (ForV (Global "y")
                        (ReadFromChannel (Global "b") "stdIn")))))
       (Set.map Global $ Set.fromList ["a","y"])
       (Map.fromList [])
       (Map.empty)
    )
    ])

timingVsFSI2 :: GeneratedProgram
timingVsFSI2 = GeneratedProgram  (Map.fromList [(1, "1")]) (Map.fromList [
    ("1",Generated
          (If CTrue
               (Seq (Seq (ForC 1 (Ass (Global "a") (Val 1))) (Seq (ReadFromChannel (Global "c") "stdIn") (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "a")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "z")))) (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "z")))) (ReadFromChannel (Global "c") "stdIn")) (ForV (Global "c") (ReadFromChannel (Global "z") "lowIn1"))))
               {-else-}
               (If CTrue
                   (ForC 2 (Seq (Ass (Global "b") (Val 17)) (ReadFromChannel (Global "c") "lowIn1")))
                   {-else-}
                   (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "a"))))) (ForV (Global "a") (ReadFromChannel (Global "b") "stdIn")))))
       (Set.fromList [])
       (Map.fromList [])
       (Map.empty)
    )
  ])


someGen :: GeneratedProgram
someGen =
  GeneratedProgram
    (Map.fromList [(1,"main")])
    (Map.fromList [
        ("main",Generated (Seq (PrintToChannel (Val (-1)) "stdOut") (CallProcedure "procH")) undefined undefined undefined),
        ("procH",Generated (Seq (CallProcedure "procH") Skip) undefined undefined undefined)
    ])

someGen2 = GeneratedProgram
    (Map.fromList [(1,"main"),(3,"thread3")])
    (Map.fromList [
        ("main", Generated (ForC 1 (CallProcedure "procF")) undefined undefined undefined),
        ("procF",Generated (Seq (CallProcedure "procF") (SpawnThread 3)) undefined undefined undefined),
        ("thread3",Generated (If CTrue (Ass (Global "z") (Val 17)) Skip) undefined undefined undefined)
    ])

someGen3 = IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (Seq (ForC 2 (ForC 1 (SpawnThread 2))) (Seq (SpawnThread 3) (ReadFromChannel (Global "c") "lowIn1"))) undefined undefined undefined),
        ("thread2",Generated (ForC 2 (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 17) "stdOut")) (If CFalse (Ass (Global "c") (Val 0)) (ReadFromChannel (Global "a") "lowIn1")))) undefined undefined undefined),
        ("thread3",Generated (If CTrue (PrintToChannel (Val 1) "stdOut") Skip) undefined undefined undefined)
    ])


someGen4 = IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (ForC 2 (ForC 2 (Seq (Seq (SpawnThread 3) (SpawnThread 2)) (Seq (PrintToChannel (Val 0) "stdOut") (PrintToChannel (Val 17) "stdOut"))))) undefined undefined undefined),
        ("thread2",Generated (Seq (ForC 1 (Seq (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val 0) "stdOut"))) (Seq (Ass (Global "a") (Val 42)) (ReadFromChannel (Global "b") "stdIn"))) undefined undefined undefined),
        ("thread3",Generated (Seq (PrintToChannel (Val 1) "stdOut") Skip) undefined undefined undefined)
    ])


someGen5 = IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [("main",Generated (ForC 2 (ForC 1 (Seq (Seq (SpawnThread 2) (SpawnThread 3)) (If CTrue (PrintToChannel (Val 0) "stdOut") (Ass (Global "y") (Val 4)))))) undefined undefined undefined),
                   ("thread2",Generated (Seq (Seq (ReadFromChannel (Global "z") "lowIn1") (PrintToChannel (Plus (Var (Global "z")) (Var (Global "z"))) "stdOut")) (ForC 1 (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut") (ReadFromChannel (Global "c") "lowIn1")))) undefined undefined undefined),
                   ("thread3",Generated (If CFalse (PrintToChannel (Val 0) "stdOut") (PrintToChannel (Val 1) "stdOut")) undefined undefined undefined)
    ])


someGen6 = IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (Seq (ForC 1 (ReadFromChannel (Global "c") "lowIn1")) (Seq (SpawnThread 3) (SpawnThread 2))) undefined undefined undefined),
        ("thread2",Generated (ForC 1 (If (Leq (Val 0) (Var (Global "c")))
                                       (If (Leq (Val 0) (Neg (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (PrintToChannel (Val 9) "stdOut"))
                                       (ForC 1 (PrintToChannel (Val 1) "stdOut")))) undefined undefined undefined),
        ("thread3",Generated (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "c") "stdIn")) undefined undefined undefined)
    ])


someGen6' = IntraGeneratedProgram
    (Map.fromList [(1,"main"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (
                    (ReadFromChannel (Global "c") "lowIn1")  `Seq`
                    (SpawnThread 3) `Seq`
                    (ForC 1 (If (Leq (Val 0) (Var (Global "c")))
                                       (If (Leq (Val 0) (Neg (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (PrintToChannel (Val 9) "stdOut"))
                                       (ForC 1 (PrintToChannel (Val 1) "stdOut"))))
                ) undefined undefined undefined),
        ("thread3",Generated (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "c") "stdIn")) undefined undefined undefined)
    ])

someGen6'' = IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (Seq (ReadFromChannel (Global "c") "lowIn1") (Seq (SpawnThread 3) (Seq Skip (SpawnThread 2)))) undefined undefined undefined),
        ("thread2",Generated (If (Leq (Val 0) (Var (Global "c")))
                                       (If (Leq (Val 0) (Neg (Var (Global "c"))))
                                           (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut")
                                           (PrintToChannel (Val 9) "stdOut"))
                                       (PrintToChannel (Val 1) "stdOut")) undefined undefined undefined),
        ("thread3",Generated (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "c") "stdIn")) undefined undefined undefined)
    ])
