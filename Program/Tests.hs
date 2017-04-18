{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Program.Tests where

import System.Process
import Data.Graph.Inductive.Dot

import Data.List

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random
import Control.Monad(forM_, when, forever, forM)
import Test.QuickCheck

import Program.Typing.FlexibleSchedulerIndependentChannels
import Program.For
import Program
import Program.Defaults
import Program.Examples
import Program.MultiThread
import Program.MHP
import Program.CDom
import Program.Analysis
import Program.Generator (GeneratedProgram(..), toCode, toProgram,
                          SimpleProgram(..), toCodeSimple, toProgramSimple,
                          Generated(..))
import Program.TransitionSystem

import Program.Properties.CDom


import IRLSOD
import Execution
import ExecutionTree
import PNI
import Unicode

import Algebra.Lattice

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.ProgramDependence
import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.NTICD
import Data.Graph.Inductive.Query.TimingDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.DataConflict
import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.BalancedSCC
import Data.Graph.Inductive.Arbitrary


import Data.Tree

import Data.Graph.Inductive.Query.Dominators


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


showCdomChef p = [ ((n,n'),c) | ((n,n'),c) <- Map.toList $ idomChef p, mhpFor p ! (n,n') == True]


showGraph g = do
  let dot = showDot (fglToDot g)
  randomInt <- getStdRandom (randomR (1,65536)) :: IO Int
  let file = "file" ++ (show randomInt) ++ ".dot"
  writeFile file dot
  runInteractiveCommand $ "xdot " ++ file

showPDG p = showGraph $ programDependenceGraphP p
showcPDG p = showGraph $ concurrentProgramDependenceGraphP p
showCFG p = showGraph $ tcfg p
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
    entry = entryOf p $ mainThread p

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
p = notReallyUnsound15
--p = minimalClassificationVstimingClassificationDomPathsCounterExampleMartin

testSinkPaths = do
  (CG _ generatedGraph) <- (generate $ resize 40 arbitrary :: IO ((Connected Gr () ())))
  --(NME generatedGraph) <- (generate $ resize 30 arbitrary :: IO ((NoMultipleEdges Gr () ())))
  showGraph $ withNodes $ withoutMultipeEdges generatedGraph
  let n = head $ nodes generatedGraph
  forM ((sinkPathsFor generatedGraph) ! n) (\p -> putStrLn $ show (n,p))
mainEquiv = do
  putStrLn $ show $ length $ allFinishedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquiv p defaultInput defaultInput'

mainEquivAnnotated = do
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquivAnnotated p defaultInput defaultInput'

mainEquivAnnotatedSampled = do
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquivAnnotatedSampled p defaultInput defaultInput'

mainEquivAnnotatedSome = do
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



isSecureEmpirically program@(Program { tcfg, observability }) = unsafePerformIO $ do
  θ  <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program defaultInput
  θ' <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program defaultInput'
  let counterExamples =  fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotatedIf areDifferent tcfg observability θ θ'
  return $ length counterExamples == 0
 where areDifferent p p' =   abs(p-p') > 2/100
       n = 7500


rofllol :: Program Gr
rofllol = toProgram $  GeneratedProgram (Map.fromList [(1,Generated (Seq (ForC 1 (If CFalse (PrintToChannel (Val 1) "stdOut") (ReadFromChannel "c" "stdIn"))) (ForC 2 (Seq (SpawnThread 2) (PrintToChannel (Val 42) "stdOut")))) (Set.fromList []) (Map.fromList [(2,Set.fromList [])])),(2,Generated (Seq (Seq (Seq (SpawnThread 3) (Ass "a" (Val 1))) (Seq (Ass "b" (Times (Var "a") (Var "a"))) (Ass "y" (Times (Var "a") (Var "b"))))) (ForC 1 (Seq Skip (Ass "a" (Times (Var "y") (Var "a")))))) (Set.fromList ["a","b","y"]) (Map.fromList [(3,Set.fromList [])])),(3,Generated (ForC 1 (Seq (Seq (PrintToChannel (Val 0) "stdOut") Skip) (Seq (PrintToChannel (Val 17) "stdOut") (ReadFromChannel "x" "stdIn")))) (Set.fromList ["x"]) (Map.fromList []))])


genAndShowSimpleTransitionSystem = do
    generatedSimples <- sample' (arbitrary :: Gen SimpleProgram)
--    let simple = generatedSimples !! (length generatedSimples `div` 4)
    -- let simple = SimpleProgram (Map.fromList [(1,Generated (Seq Skip (ForC 2 (Seq (Seq (Seq (Ass "h" (Times (Var "x") (Var "h"))) (Ass "x" (Times (Var "x") (Var "z")))) (Seq Skip (Ass "z" (Times (Var "x") (Var "z"))))) (Seq (If (Leq (Val 0) (Times (Var "y") (Var "z"))) Skip Skip) (Seq Skip (Ass "h" (Times (Var "x") (Var "h")))))))) (Set.fromList ["h","x","y","z"]) (Map.fromList []))])
    -- let simple = SimpleProgram (Map.fromList [(1,Generated (Seq Skip (Seq (ForC 1 (Seq (ForC 2 (Ass "z" (Times (Var "x") (Var "x")))) (ForV "z" (Ass "h" (Times (Var "x") (Var "y")))))) (Seq (Seq (Seq (Ass "z" (Times (Var "y") (Var "h"))) (Ass "z" (Times (Var "x") (Var "z")))) (If (Leq (Val 0) (Times (Var "z") (Var "z"))) (Ass "h" (Times (Var "z") (Var "z"))) Skip)) (If (Leq (Val 0) (Times (Var "x") (Var "y"))) (Seq Skip Skip) (ForV "y" (Ass "h" (Times (Var "y") (Var "x")))))))) (Set.fromList ["h","x","y","z"]) (Map.fromList []))])
    let simple = SimpleProgram (Map.fromList [(1,Generated (Seq Skip (ForC 1 (Seq (Seq (ForC 2 (Ass "h" (Times (Var "h") (Var "h")))) (If (Leq (Val 0) (Times (Var "y") (Var "y"))) (Ass "x" (Times (Var "y") (Var "h"))) (Ass "y" (Times (Var "z") (Var "y"))))) (Seq (If (Leq (Val 0) (Times (Var "h") (Var "z"))) (Ass "h" (Times (Var "x") (Var "y"))) (Ass "x" (Times (Var "z") (Var "h")))) (ForC 2 Skip))))) (Set.fromList ["h","x","y","z"]) (Map.fromList []))])

    let p :: Program Gr = toProgramSimple $ simple
    let low  = Set.fromList ["x", "y", "z"] ∩ vars p
    let high = Set.fromList ["a", "b", "c"] ∩ vars p
    showCFG   $ p
    showGraph $ fromSimpleProgram p
    putStrLn  $ "secureSymbolic: " ++ (show $ secureSymbolic low high p)
    putStrLn  $ "securePDG:      " ++ (show $ securePDG (vars p) low high simple)



showSimpleTransitionSystem = do
    let p :: Program Gr = simple2
    let low  = Set.fromList ["z"] ∩ vars p
    let high = Set.fromList ["a", "b", "c"] ∩ vars p
    showCFG   $ p
    showGraph $ fromSimpleProgram p
    putStrLn  $ "secureSymbolic: " ++ (show $ secureSymbolic low high p)


showConcreteTransitionSystem = do
    let p :: Program Gr = simple
    let low  = Set.fromList ["z"] ∩ vars p
    let high = Set.fromList ["a", "b", "c"] ∩ vars p
    let system = concreteFromSimpleProgram p
    let obs = observablePartOfConcrete (vars p)
                                       (entryOf p $ mainThread p)
                                       (exitOf  p $ mainThread p)
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
                                                   (entryOf p $ mainThread p)
                                                   (exitOf  p $ mainThread p)
                                                   (Set.fromList ["x", "y", "z"] ∩ vars p)
                                                   system
    showCFG   $ p
    showGraph $ system
    showGraph $ obs


showSimpleTwoValueTransitionSystem = do
    -- let p = simple2
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (ForC 2 Skip) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (Ass "z" (Times (Var "b") (Var "z"))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    -- let p = (toProgramSimple $  SimpleProgram (Map.fromList [(1,Generated (Seq (ForV "b" (Seq (If (Leq (Val 0) (Times (Var "z") (Var "b"))) (Ass "c" (Times (Var "x") (Var "x"))) (Ass "x" (Times (Var "y") (Var "a")))) (ForC 1 Skip))) (Seq (If (Leq (Val 0) (Times (Var "a") (Var "z"))) (Seq (Ass "y" (Times (Var "z") (Var "c"))) (Ass "x" (Times (Var "a") (Var "x")))) (ForV "b" (Ass "a" (Times (Var "a") (Var "x"))))) (Seq (ForV "c" (Ass "y" (Times (Var "x") (Var "a")))) (Seq Skip (Ass "z" (Times (Var "x") (Var "z"))))))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (Seq Skip (If (Leq (Val 0) (Times (Var "y") (Var "x"))) (Ass "z" (Times (Var "z") (Var "x"))) (Ass "h" (Times (Var "h") (Var "x"))))) (Set.fromList ["h","x","y","z"]) (Map.fromList []))])) :: Program Gr

    let system = twoValueFromSimpleProgram p
    -- let low = (Set.fromList ["z"])
    let low = Set.fromList ["x", "y", "z"] ∩ vars p
    let obs = observablePartOfTwoValueDefUseSimple (vars p)
                                                   (entryOf p $ mainThread p)
                                                   (exitOf  p $ mainThread p)
                                                   low
                                                   system
    showCFG   $ p
    showGraph $ system
    showGraph $ obs
    putStrLn  $ "secure: " ++ (show $ secureTwoValueDefUse low p)

showSimpleOneValueTransitionSystem = do
    -- let p = simple2
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (ForC 2 Skip) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    -- let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (Ass "z" (Times (Var "b") (Var "z"))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    --let p = (toProgramSimple $  SimpleProgram (Map.fromList [(1,Generated (Seq (ForV "b" (Seq (If (Leq (Val 0) (Times (Var "z") (Var "b"))) (Ass "c" (Times (Var "x") (Var "x"))) (Ass "x" (Times (Var "y") (Var "a")))) (ForC 1 Skip))) (Seq (If (Leq (Val 0) (Times (Var "a") (Var "z"))) (Seq (Ass "y" (Times (Var "z") (Var "c"))) (Ass "x" (Times (Var "a") (Var "x")))) (ForV "b" (Ass "a" (Times (Var "a") (Var "x"))))) (Seq (ForV "c" (Ass "y" (Times (Var "x") (Var "a")))) (Seq Skip (Ass "z" (Times (Var "x") (Var "z"))))))) (Set.fromList ["a","b","c","x","y","z"]) (Map.fromList []))])) :: Program Gr
    let p = (toProgramSimple $ SimpleProgram (Map.fromList [(1,Generated (Seq Skip (If (Leq (Val 0) (Times (Var "y") (Var "x"))) (Ass "z" (Times (Var "z") (Var "x"))) (Ass "h" (Times (Var "h") (Var "x"))))) (Set.fromList ["h","x","y","z"]) (Map.fromList []))])) :: Program Gr
    let system = oneValueFromSimpleProgram p
    -- let low = (Set.fromList ["z"])
    let low = Set.fromList ["x", "y", "z"] ∩ vars p
    let obs = observablePartOfOneValueDefUseSimple (vars p)
                                                   (entryOf p $ mainThread p)
                                                   (exitOf  p $ mainThread p)
                                                   low
                                                   system
    showCFG   $ p
    showGraph $ system
    showGraph $ obs
    putStrLn  $ "secure: " ++ (show $ secureOneValueDefUse low p)


timingVsFSI :: GeneratedProgram
timingVsFSI = GeneratedProgram $ Map.fromList [
    (1,Generated (Seq (Seq (Seq (Seq
            (Ass "y" (Val 0))
            (Ass "a" (Times (Var "y") (Var "y"))))
       (Seq (PrintToChannel (Times (Var "a") (Var "y")) "stdOut")
            (SpawnThread 2)))
  (Seq (Seq (PrintToChannel (Times (Var "y") (Var "y")) "stdOut")
            (ReadFromChannel "x" "stdIn"))
            (ForV "x" Skip)))
            (ForV "y"
               (ForV "x"
                  (Seq (ReadFromChannel "z" "stdIn")
                        Skip))))
       (Set.fromList ["a","x","y"])
       (Map.fromList [(2,Set.fromList ["a","y"])])),
    (2,Generated
            (ForV "a"
               (ForC 1 (
                   ForC 1
                     (ForV "y"
                        (ReadFromChannel "b" "stdIn")))))
       (Set.fromList ["a","y"])
       (Map.fromList []))
    ]

timingVsFSI2 :: GeneratedProgram
timingVsFSI2 = GeneratedProgram $ Map.fromList [
    (1,Generated
          (If CTrue
               (Seq (Seq (ForC 1 (Ass "a" (Val 1))) (Seq (ReadFromChannel "c" "stdIn") (Ass "z" (Times (Var "a") (Var "a"))))) (Seq (If (Leq (Val 0) (Times (Var "a") (Var "z"))) (Ass "a" (Times (Var "z") (Var "z"))) (ReadFromChannel "c" "stdIn")) (ForV "c" (ReadFromChannel "z" "lowIn1"))))
               {-else-}
               (If CTrue
                   (ForC 2 (Seq (Ass "b" (Val 17)) (ReadFromChannel "c" "lowIn1")))
                   {-else-}
                   (Seq (Seq (ReadFromChannel "a" "stdIn") (Ass "y" (Times (Var "a") (Var "a")))) (ForV "a" (ReadFromChannel "b" "stdIn")))))
       (Set.fromList [])
       (Map.fromList []))
  ]
