{-# LANGUAGE ScopedTypeVariables #-}
module Program.Tests where

import System.Process
import Data.Graph.Inductive.Dot

import Data.List

import Control.Monad(forM_, when)
import Test.QuickCheck

import Program
import Program.Examples
import Program.MultiThread
import Program.MHP
import Program.CDom
import Program.Analysis
import Program.Generator (GeneratedProgram(..), toCode, toProgram)


import IRLSOD
import Execution
import ExecutionTree
import PNI
import Unicode

import Algebra.Lattice

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.ProgramDependence
import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.TimingDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.DataConflict
import Data.Graph.Inductive.Query.TransClos

import Data.Graph.Inductive.Query.Dominators


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
-- import Data.Set.Unicode


showCdomChef p = [ ((n,n'),c) | ((n,n'),c) <- Map.toList $ idomChef p, mhpFor p ! (n,n') == True]


showGraph g = do
  let dot = showDot (fglToDot g)
  writeFile "file.dot" dot
  system "xdot file.dot"

showPDG p = showGraph $ programDependenceGraphP p
showCFG p = showGraph $ tcfg p
showTDG p = showGraph $ timingDependenceGraphP p
showConflicts p = showGraph $ dataConflictGraphP p


-- p = cdomIsBroken'
p = figure5right'
-- p = someGeneratedProgram

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
  showCounterExamplesPniForEquivAnnotatedSome p defaultInput defaultInput'




showMorePrecise :: (Program Gr -> Bool) -> (Program Gr -> Bool) -> IO ()
showMorePrecise a1 a2 = do
    generated <- sample' (arbitrary :: Gen GeneratedProgram)
    forM_ generated (\gen -> do
       let p :: Program Gr = toProgram gen
       let sec1 = a1  p
       let sec2 = a2 p
       putStr "a1: "
       putStrLn $ show $ sec1

       putStr "a2: "
       putStrLn $ show $ sec2

--       when (sec1 ∧ ((¬) sec2)) $ do
       when (sec1 /= sec2) $ do
         putStrLn $ show $ toCode gen
         showCFG p
         return ()

       putStrLn ""
     )
