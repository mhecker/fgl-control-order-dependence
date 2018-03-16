{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Program.Tests where

import System.Process

import Data.Graph.Inductive.Dot

import Data.List

import Data.Maybe (fromJust)

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
import Data.Graph.Inductive.Arbitrary.Reducible

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set



main = let {  pr = timingAtUsesVsResumptionBasedBugInTranslationExample2 } in showCounterExamplesPniForEquivAnnotatedSome 7500 pr defaultInput defaultInput'

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
p = notReallyUnsound19
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


indepsCounterExample :: GeneratedProgram
indepsCounterExample = GeneratedProgram
 (Map.fromList [(1,"main"),(3,"thread3")])
 (Map.fromList [("bar",Generated (ForV (Global "b") (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (Seq (ReadFromChannel (Global "c") "lowIn1") (ReadFromChannel (Global "y") "lowIn1")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) Skip (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))))
                 undefined undefined undefined
                ),
                ("baz",Generated (Seq (ForC 1 (If CTrue (SpawnThread 3) (Ass (Global "c") (Val 17)))) (ForC 2 (Seq (ReadFromChannel (Global "b") "stdIn") (CallProcedure "bar"))))
                 -- (fromList [Global "b"]) (fromList [(3,fromList [])]) (Map.fromList [("bar",fromList [Global "b"])])
                 undefined undefined undefined
                ),
                ("main",Generated (Seq (Seq (ForC 2 Skip) (If CTrue (CallProcedure "baz") (ReadFromChannel (Global "y") "lowIn1"))) (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "a"))))) (Seq Skip (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "z")))))))
                 -- (fromList [Global "a",Global "z"]) (fromList []) (fromList [("baz",fromList [])])
                                  undefined undefined undefined
                ),
                ("thread3",Generated (Seq (If CTrue (Seq (PrintToChannel (Val 17) "stdOut") (PrintToChannel (Val 42) "stdOut")) (ForC 1 Skip)) (Seq (Seq (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "x") "stdIn")) (ForV (Global "x") (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))))
                 -- (fromList [Global "b",Global "x"]) (fromList []) (fromList [])
                 undefined undefined undefined
                )
  ]
 )

indepsExceptionExample :: GeneratedProgram
indepsExceptionExample = GeneratedProgram
 (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
 (Map.fromList [("bar",Generated (Seq (If CTrue (If CFalse (PrintToChannel (Val 0) "stdOut") Skip) (Seq (ReadFromChannel (Global "y") "stdIn") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "y")))))) (Seq (Seq (Ass (Global "c") (Val 0)) (CallProcedure "foo")) (Seq (CallProcedure "foo") (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut"))))
                  undefined undefined undefined),
                ("baz",Generated (Seq (If CFalse (If CFalse (ReadFromChannel (Global "y") "stdIn") (Ass (Global "y") (Val (-1)))) (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "x") "lowIn1"))) (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (Ass (Global "b") (Val (-1)))) (Seq (CallProcedure "baz") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))))))
                  undefined undefined undefined),
                ("foo",Generated (ForC 1 (Seq (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c"))))) (ForC 2 (ReadFromChannel (Global "c") "lowIn1"))))
                  undefined undefined undefined),
                ("main",Generated (Seq (Seq (Seq (SpawnThread 3) (SpawnThread 2)) (Seq (CallProcedure "bar") (PrintToChannel (Val 1) "stdOut"))) (ForC 1 (If CFalse (ReadFromChannel (Global "z") "stdIn") Skip)))                 undefined undefined undefined),
                ("thread2",Generated (If CTrue (If CFalse (ForC 1 (PrintToChannel (Val 42) "stdOut")) (Seq (ReadFromChannel (Global "x") "lowIn1") Skip)) (Seq (If CFalse (ReadFromChannel (Global "b") "stdIn") (CallProcedure "bar")) (Seq (CallProcedure "baz") (Ass (Global "z") (Val 17)))))
                 undefined undefined undefined),
                ("thread3",Generated (ForC 1 (Seq (If CTrue Skip (ReadFromChannel (Global "a") "stdIn")) (Seq (Ass (Global "a") (Val 42)) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))))
                 undefined undefined undefined)])


summaryExample :: GeneratedProgram
summaryExample = GeneratedProgram
 (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
 (Map.fromList [("bar",Generated (Seq (ForC 2 (If CTrue (Ass (Global "y") (Val 0)) (ReadFromChannel (Global "z") "stdIn"))) (If CTrue (Seq (ReadFromChannel (Global "c") "lowIn1") Skip) (Seq (CallProcedure "bar") (PrintToChannel (Val 42) "stdOut"))))
                 undefined undefined undefined),
                ("foo",Generated (ForC 2 (If CFalse (Seq (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val 0) "stdOut")) (If CTrue (PrintToChannel (Val 17) "stdOut") (Ass (Global "y") (Val 0)))))
                  undefined undefined undefined),
                ("main",Generated (Seq (If CFalse (If CTrue (ReadFromChannel (Global "c") "stdIn") Skip) (Seq (CallProcedure "bar") (SpawnThread 2))) (ForC 2 (If CTrue (PrintToChannel (Val 1) "stdOut") (PrintToChannel (Val (-1)) "stdOut"))))
                  undefined undefined undefined),
                ("thread2",Generated (If CTrue (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 0) "stdOut")) (Seq (SpawnThread 3) (ReadFromChannel (Global "c") "stdIn"))) (Seq (Seq (CallProcedure "foo") (Ass (Global "a") (Val 0))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (CallProcedure "foo"))))
                  undefined undefined undefined),
                ("thread3",Generated (Seq (Seq (Seq (Ass (Global "b") (Val 42)) (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "b"))))) (Seq Skip (Ass (Global "b") (Times (Var (Global "b")) (Var (Global "c")))))) (Seq (Seq Skip (ReadFromChannel (Global "b") "stdIn")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "c")))) Skip (PrintToChannel (Times (Var (Global "c")) (Var (Global "b"))) "stdOut"))))
                  undefined undefined undefined)
 ])


summaryExample2 :: GeneratedProgram
summaryExample2 = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (CallProcedure "foo") Skip)) (Seq (Seq (ReadFromChannel (Global "a") "lowIn1") (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "x"))))) (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (CallProcedure "foo")))) (ForV (Global "x") (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (ReadFromChannel (Global "a") "stdIn"))))) undefined undefined undefined),("baz",Generated (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (ForV (Global "x") (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (CallProcedure "bar") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (ReadFromChannel (Global "b") "lowIn1") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "x"))))))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "z"))) "stdOut"))) (Seq (Seq Skip (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))))) undefined undefined undefined),("foo",Generated (ForC 1 (Seq (Seq (If CFalse (Ass (Global "c") (Val 0)) (Ass (Global "c") (Val 17))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c")))) (CallProcedure "foo"))) (Seq (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "x") "stdIn") (CallProcedure "foo")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "x") "lowIn1"))))) undefined undefined undefined),("main",Generated (Seq (Seq (If CTrue (If CTrue (ReadFromChannel (Global "y") "lowIn1") (ReadFromChannel (Global "c") "stdIn")) (Seq (ReadFromChannel (Global "z") "stdIn") (Ass (Global "y") (Times (Var (Global "z")) (Var (Global "z")))))) (If CTrue (Seq (SpawnThread 3) (PrintToChannel (Val (-1)) "stdOut")) (Seq (PrintToChannel (Val 42) "stdOut") (ReadFromChannel (Global "b") "lowIn1")))) (Seq (Seq (Seq Skip (ReadFromChannel (Global "y") "stdIn")) (Seq (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y")))) (CallProcedure "foo"))) (ForC 2 (ForV (Global "b") (SpawnThread 2))))) undefined undefined undefined),("thread2",Generated (Seq (ForV (Global "b") (ForC 1 (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "b")))) (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "c") "lowIn1")))) (Seq (Seq (Seq (Ass (Global "x") (Times (Var (Global "b")) (Var (Global "y")))) (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "y"))))) (Seq (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "a") "stdIn"))) (ForC 2 (ForV (Global "x") (ReadFromChannel (Global "y") "stdIn"))))) undefined undefined undefined),("thread3",Generated (If CFalse (Seq (ForC 1 (If CFalse (ReadFromChannel (Global "c") "lowIn1") Skip)) (ForC 2 (ForC 2 (Ass (Global "b") (Val 1))))) (ForC 1 (If CFalse (Seq (ReadFromChannel (Global "x") "stdIn") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (ReadFromChannel (Global "x") "stdIn") (CallProcedure "baz"))))) undefined undefined undefined)])


summaryExample3 :: GeneratedProgram
summaryExample3 = GeneratedProgram (Map.fromList [(1,"main"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (ForC 1 (ForC 2 Skip)) (Seq (If CTrue Skip (ReadFromChannel (Global "b") "stdIn")) (If CTrue (Ass (Global "a") (Val 17)) (CallProcedure "bar")))) undefined undefined undefined),("baz",Generated (Seq (If CFalse (ForC 1 (Ass (Global "y") (Val (-1)))) (Seq Skip (PrintToChannel (Val 42) "stdOut"))) (If CFalse (ForC 1 (ReadFromChannel (Global "a") "lowIn1")) (Seq (PrintToChannel (Val 0) "stdOut") (CallProcedure "bar")))) undefined undefined undefined),("main",Generated (Seq (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (SpawnThread 3)) (Seq (Ass (Global "z") (Val 0)) Skip)) (ForV (Global "z") (Seq (ReadFromChannel (Global "x") "stdIn") (Ass (Global "b") (Times (Var (Global "z")) (Var (Global "x"))))))) undefined undefined undefined),("thread3",Generated (Seq (Seq (If CFalse (CallProcedure "baz") (PrintToChannel (Val 0) "stdOut")) (If CFalse (PrintToChannel (Val 0) "stdOut") (Ass (Global "b") (Val 1)))) (ForC 1 (Seq (Ass (Global "z") (Val 17)) (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")))) undefined undefined undefined)])


summaryExample4 :: GeneratedProgram
summaryExample4 = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (Seq (ForV (Global "b") (ForV (Global "z") (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "b")))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (Seq (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "b")))) (ReadFromChannel (Global "b") "lowIn1")) (Seq (CallProcedure "bar") (Ass (Global "z") (Times (Var (Global "b")) (Var (Global "b"))))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (Seq (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (ReadFromChannel (Global "z") "stdIn") (Ass (Global "c") (Times (Var (Global "z")) (Var (Global "z"))))) (Seq (Ass (Global "x") (Times (Var (Global "b")) (Var (Global "b")))) Skip)) (Seq (ForC 2 (CallProcedure "baz")) (ForV (Global "b") (CallProcedure "baz"))))) undefined undefined undefined),("baz",Generated (Seq (ForV (Global "z") (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "z")))) (ForV (Global "b") Skip) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut") Skip))) (ForC 2 (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (ForV (Global "b") (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")) (Seq (CallProcedure "baz") (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut"))))) undefined undefined undefined),("foo",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (Seq (Seq (CallProcedure "foo") (Ass (Global "z") (Times (Var (Global "b")) (Var (Global "z"))))) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "z")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut") (CallProcedure "bar"))) (Seq (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "z")))) (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "z")))) (CallProcedure "baz")) (ForV (Global "z") (ReadFromChannel (Global "a") "stdIn")))) (ForC 1 (ForC 2 (ForC 1 (CallProcedure "bar"))))) undefined undefined undefined),("main",Generated (ForC 2 (Seq (Seq (Seq Skip (Ass (Global "b") (Val (-1)))) (Seq (ReadFromChannel (Global "z") "lowIn1") (Ass (Global "z") (Times (Var (Global "z")) (Var (Global "z")))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (ForV (Global "b") (ReadFromChannel (Global "x") "stdIn")) (ForC 1 (SpawnThread 3))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (Seq (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))) (CallProcedure "foo")) (ForC 1 (Ass (Global "b") (Times (Var (Global "z")) (Var (Global "b")))))) (Seq (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "b"))) "stdOut") Skip) (ForV (Global "z") (Ass (Global "x") (Times (Var (Global "z")) (Var (Global "z"))))))) (ForV (Global "b") (ForV (Global "z") (Seq (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "z")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut"))))) undefined undefined undefined),("thread3",Generated (ForV (Global "z") (Seq (Seq (Seq (SpawnThread 2) (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut")) (ForV (Global "b") (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut"))) (ForC 1 (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "b"))) "stdOut") (Ass (Global "x") (Times (Var (Global "z")) (Var (Global "b")))))))) undefined undefined undefined)])

summaryExample5 :: GeneratedProgram
summaryExample5 = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (ForC 2 (Seq (Seq (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "y")))) (ReadFromChannel (Global "y") "stdIn") (CallProcedure "bar")))) (Seq (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (PrintToChannel (Times (Var (Global "a")) (Var (Global "b"))) "stdOut")) (ForV (Global "b") (ReadFromChannel (Global "y") "stdIn"))) (Seq (ForV (Global "y") (CallProcedure "foo")) (ForV (Global "a") (ReadFromChannel (Global "z") "stdIn"))))) undefined undefined undefined),("baz",Generated (Seq (Seq (ForC 1 (Seq (PrintToChannel (Val 0) "stdOut") (Ass (Global "y") (Val 42)))) (ForV (Global "y") (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (CallProcedure "bar") (ReadFromChannel (Global "b") "stdIn")))) (Seq (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (ForV (Global "y") (CallProcedure "bar")) (ForC 2 (Ass (Global "z") (Times (Var (Global "y")) (Var (Global "y")))))) (ForV (Global "y") (Seq Skip (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "y")))))))) undefined undefined undefined),("foo",Generated (Seq (If CTrue (If CFalse (Seq (PrintToChannel (Val 1) "stdOut") (PrintToChannel (Val 17) "stdOut")) (If CTrue (PrintToChannel (Val 42) "stdOut") (ReadFromChannel (Global "x") "lowIn1"))) (Seq (Seq (ReadFromChannel (Global "c") "lowIn1") (ReadFromChannel (Global "x") "lowIn1")) (Seq (ReadFromChannel (Global "y") "stdIn") (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))))) (Seq (Seq (Seq (Ass (Global "y") (Val 1)) (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))) (Seq Skip (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "b")))))) (Seq (Seq (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "b")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "y"))) "stdOut")) (ForV (Global "c") (CallProcedure "foo"))))) undefined undefined undefined),("main",Generated (Seq (If CTrue (Seq (If CTrue (PrintToChannel (Val 0) "stdOut") (ReadFromChannel (Global "a") "lowIn1")) (ForC 1 (ReadFromChannel (Global "x") "stdIn"))) (ForC 2 (ForC 1 (CallProcedure "baz")))) (Seq (If CFalse (Seq (Ass (Global "x") (Val 0)) Skip) (Seq (SpawnThread 2) (PrintToChannel (Val (-1)) "stdOut"))) (Seq (ForC 2 (CallProcedure "baz")) (Seq (PrintToChannel (Val 17) "stdOut") (ReadFromChannel (Global "a") "stdIn"))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (Seq (Seq Skip (ReadFromChannel (Global "c") "stdIn")) (Seq (ReadFromChannel (Global "c") "stdIn") (SpawnThread 3))) (Seq (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (ReadFromChannel (Global "y") "stdIn")) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") Skip))) (ForV (Global "c") (Seq (ForC 2 (Ass (Global "z") (Times (Var (Global "c")) (Var (Global "c"))))) (Seq (ReadFromChannel (Global "a") "lowIn1") (PrintToChannel (Times (Var (Global "z")) (Var (Global "c"))) "stdOut"))))) undefined undefined undefined),("thread3",Generated (Seq (ForC 1 (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))) (CallProcedure "foo")) (ForC 2 (Ass (Global "c") (Times (Var (Global "c")) (Var (Global "c"))))))) (Seq (ForC 2 (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "a") "lowIn1") (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))))) (Seq (Seq (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "b"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) Skip (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))))) undefined undefined undefined)])

summaryExample6 :: GeneratedProgram
summaryExample6 = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2")]) (Map.fromList [("baz",Generated (Seq (ReadFromChannel (Global "a") "lowIn1") (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a"))))) undefined undefined undefined),("main",Generated (Seq (PrintToChannel (Val 17) "stdOut") (SpawnThread 2)) undefined undefined undefined),("thread2",Generated (Seq (CallProcedure "baz") (ReadFromChannel (Global "y") "stdIn")) undefined undefined undefined)])

summaryExample7 :: GeneratedProgram
summaryExample7 = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("baz",Generated (Seq (Seq (ForC 2 (Seq (CallProcedure "baz") (Ass (Global "c") (Val 42)))) (Seq (ForC 1 (SpawnThread 2)) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") Skip))) (ForV (Global "c") (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (ReadFromChannel (Global "z") "stdIn") (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "z"))))) (ForC 1 (ReadFromChannel (Global "y") "stdIn"))))) undefined undefined undefined),("foo",Generated (Seq (ForC 1 (ForC 2 (Seq (PrintToChannel (Val 42) "stdOut") (CallProcedure "baz")))) (Seq (Seq (Seq (Ass (Global "y") (Val 0)) (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut")) (Seq (CallProcedure "foo") (CallProcedure "baz"))) (Seq (ForV (Global "y") (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut")) (ForC 2 (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "y")))))))) undefined undefined undefined),("main",Generated (Seq (Seq (ForC 1 (Seq (SpawnThread 3) (Ass (Global "b") (Val (-1))))) (ForV (Global "b") (ForC 2 (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "b"))))))) (Seq (ForC 2 (ForV (Global "b") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))))) (ForC 1 (Seq (Ass (Global "a") (Times (Var (Global "b")) (Var (Global "b")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (ForV (Global "c") (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c")))))) (Seq (Seq (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c")))) Skip) (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "c"))))))) (ForV (Global "y") (ForC 1 (ForC 1 (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "c")))))))) undefined undefined undefined),("thread3",Generated (ForC 1 (Seq (Seq (Seq Skip (CallProcedure "foo")) (Seq (ReadFromChannel (Global "x") "lowIn1") (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x")))))) (ForV (Global "y") (Seq (ReadFromChannel (Global "x") "stdIn") Skip)))) undefined undefined undefined)])

summaryExample7' :: GeneratedProgram
summaryExample7' = GeneratedProgram (
  Map.fromList [(1,"main")])
 (Map.fromList [
     ("baz",Generated (Seq (Seq (ForC 2 (Seq (CallProcedure "baz") Skip)) Skip) Skip) undefined undefined undefined),
     ("foo",Generated (Seq (Seq Skip (CallProcedure "baz")) (Seq (Seq Skip (Seq (CallProcedure "foo") (CallProcedure "baz"))) Skip)) undefined undefined undefined),
     ("main",Generated (ForC 1 (CallProcedure "foo")) undefined undefined undefined)
 ])


summaryExample8 :: GeneratedProgram
summaryExample8 =GeneratedProgram (Map.fromList [(1,"main"),(3,"thread3")]) (Map.fromList [("bar",Generated (ForV (Global "b") (Seq (Seq (ForC 2 (PrintToChannel (Times (Var (Global "b")) (Var (Global "y"))) "stdOut")) (ForC 2 (CallProcedure "foo"))) (Seq (Seq Skip (ReadFromChannel (Global "y") "stdIn")) (Seq Skip (ReadFromChannel (Global "z") "stdIn"))))) undefined undefined undefined),("foo",Generated (Seq (ForV (Global "x") (Seq (ForC 2 (PrintToChannel (Times (Var (Global "x")) (Var (Global "y"))) "stdOut")) (ForV (Global "b") (ReadFromChannel (Global "y") "stdIn")))) (Seq (ForV (Global "x") (ForV (Global "y") (ReadFromChannel (Global "b") "lowIn1"))) (Seq (ForV (Global "b") (PrintToChannel (Times (Var (Global "b")) (Var (Global "y"))) "stdOut")) (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "x"))) "stdOut") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "x")))))))) undefined undefined undefined),("main",Generated (ForC 1 (Seq (Seq (Seq (PrintToChannel (Val 0) "stdOut") (Ass (Global "y") (Val 0))) (Seq (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "y")))) (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))) (Seq (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "y"))) "stdOut") (ReadFromChannel (Global "x") "stdIn")) (Seq Skip (SpawnThread 3))))) undefined undefined undefined),("thread3",Generated (ForV (Global "b") (ForC 1 (ForC 2 (ForC 1 (CallProcedure "bar"))))) undefined undefined undefined)])

summaryExample9 :: GeneratedProgram
summaryExample9 = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (ForC 2 (If CFalse (Seq (ReadFromChannel (Global "z") "lowIn1") (Ass (Global "z") (Times (Var (Global "z")) (Var (Global "z"))))) (Seq (ReadFromChannel (Global "a") "stdIn") (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "a"))))))) (Seq (Seq (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "x") "stdIn")) (ForC 1 (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "a")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "b")))) (CallProcedure "foo") (ReadFromChannel (Global "x") "lowIn1")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "a")))) (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "b")))) (CallProcedure "foo"))))) undefined undefined undefined),("baz",Generated (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "x")))) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "a")))) (ForV (Global "a") (ForV (Global "c") (ReadFromChannel (Global "y") "stdIn"))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "a")))) (ForV (Global "x") (PrintToChannel (Times (Var (Global "b")) (Var (Global "x"))) "stdOut")) (ForC 1 (CallProcedure "baz")))) (Seq (Seq (Seq Skip (CallProcedure "baz")) (ForC 1 (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (Seq (ForV (Global "x") (PrintToChannel (Times (Var (Global "b")) (Var (Global "x"))) "stdOut")) (Seq (ReadFromChannel (Global "a") "stdIn") (CallProcedure "baz"))))) undefined undefined undefined),("foo",Generated (Seq (Seq (ForC 1 (Seq (ReadFromChannel (Global "c") "lowIn1") (PrintToChannel (Times (Var (Global "c")) (Var (Global "a"))) "stdOut"))) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "a")))) (Seq (ReadFromChannel (Global "b") "stdIn") (CallProcedure "baz")) (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "c"))) "stdOut") (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "x"))))))) (ForV (Global "b") (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (ReadFromChannel (Global "x") "stdIn") (PrintToChannel (Times (Var (Global "x")) (Var (Global "a"))) "stdOut")) (ForC 2 (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "c")))))))) undefined undefined undefined),("main",Generated (Seq (If CFalse (If CFalse (ForC 1 (Ass (Global "x") (Val 0))) (Seq (PrintToChannel (Val (-1)) "stdOut") (ReadFromChannel (Global "z") "stdIn"))) (Seq (Seq (CallProcedure "bar") (PrintToChannel (Val 1) "stdOut")) (ForC 2 Skip))) (Seq (ForC 1 (Seq (Ass (Global "x") (Val (-1))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (Seq (Seq (SpawnThread 2) (SpawnThread 3)) (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") Skip)))) undefined undefined undefined),("thread2",Generated (Seq (Seq (ForV (Global "x") (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (ForC 2 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ReadFromChannel (Global "a") "lowIn1") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")))) (ForV (Global "x") (Seq (Seq (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x")))) Skip) (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "a") "lowIn1"))))) undefined undefined undefined),("thread3",Generated (Seq (ForC 1 (ForV (Global "x") (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")))) (ForC 2 (Seq (Seq (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "y")))) (Ass (Global "c") (Times (Var (Global "z")) (Var (Global "y")))) (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut"))))) undefined undefined undefined)])

summaryExample10 :: GeneratedProgram
summaryExample10 = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (If CTrue (ForC 2 (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 17) "stdOut")) (ForC 1 (SpawnThread 2)))) (Seq (Seq (ForC 2 (PrintToChannel (Val 1) "stdOut")) (Seq (CallProcedure "bar") (PrintToChannel (Val 1) "stdOut"))) (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 1) "stdOut")) (Seq (ReadFromChannel (Global "b") "stdIn") (Ass (Global "b") (Times (Var (Global "b")) (Var (Global "b")))))))) undefined undefined undefined),("baz",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (Seq (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x")))) Skip) (Seq (CallProcedure "foo") (ReadFromChannel (Global "z") "lowIn1"))) (Seq (ForC 2 (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x"))))) (ForV (Global "x") (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x"))))))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForC 1 (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x"))))) (Seq (ReadFromChannel (Global "c") "lowIn1") (CallProcedure "baz"))) (Seq (Seq (CallProcedure "baz") (CallProcedure "foo")) (Seq (CallProcedure "foo") (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))))) undefined undefined undefined),("foo",Generated (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForC 1 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForC 2 (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (CallProcedure "foo") (ReadFromChannel (Global "b") "lowIn1")))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (CallProcedure "foo") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (ForC 1 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) Skip (CallProcedure "foo"))))) undefined undefined undefined),("main",Generated (Seq (Seq (Seq (If CFalse (CallProcedure "bar") (ReadFromChannel (Global "b") "stdIn")) (ForC 2 (ReadFromChannel (Global "x") "stdIn"))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (ReadFromChannel (Global "c") "lowIn1")) (Seq (CallProcedure "baz") (CallProcedure "baz")))) (ForC 2 (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (CallProcedure "baz") (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (Seq (Seq (SpawnThread 3) (Ass (Global "c") (Val 0))) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "c")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ReadFromChannel (Global "x") "stdIn") (ReadFromChannel (Global "y") "stdIn")) (Seq Skip (ReadFromChannel (Global "b") "lowIn1")))) (ForV (Global "x") (ForV (Global "c") (Seq (ReadFromChannel (Global "z") "lowIn1") (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut"))))) undefined undefined undefined),("thread3",Generated (Seq (Seq (ForC 2 (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "c") "stdIn"))) (ForV (Global "c") (Seq Skip (PrintToChannel (Times (Var (Global "c")) (Var (Global "x"))) "stdOut")))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (ReadFromChannel (Global "y") "stdIn") (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "c"))))) (ForC 1 (ReadFromChannel (Global "z") "lowIn1"))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "x")))) (ForC 2 (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "z")))) (ReadFromChannel (Global "x") "lowIn1") (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "x")))))))) undefined undefined undefined)])

summaryExample11 :: GeneratedProgram
summaryExample11 = GeneratedProgram (Map.fromList [(1,"main")]) (Map.fromList [("baz",Generated (ForC 1 (Seq (Seq (Seq (ReadFromChannel (Global "x") "stdIn") (PrintToChannel (Times (Var (Global "c")) (Var (Global "x"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "c")))) Skip)) (Seq (ForC 1 (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (CallProcedure "baz") (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))))) undefined undefined undefined),("main",Generated (Seq (If CTrue (Seq (Seq (ReadFromChannel (Global "y") "lowIn1") (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))) (ForV (Global "y") (Ass (Global "a") (Times (Var (Global "y")) (Var (Global "y")))))) (ForC 1 (ForC 2 Skip))) (Seq (Seq (Seq (ReadFromChannel (Global "c") "lowIn1") (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c"))))) (ForV (Global "c") Skip)) (Seq (ForV (Global "c") (CallProcedure "baz")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "b")))) Skip (ReadFromChannel (Global "z") "stdIn"))))) undefined undefined undefined)])
