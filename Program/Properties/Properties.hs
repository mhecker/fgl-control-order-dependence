{-# LANGUAGE NamedFieldPuns #-}

module Program.Properties where

import Algebra.Lattice
import Unicode

import Program

import Program.Analysis

import Program.Examples
import Program.Generator

import Program.Properties.CDom
import Program.CDom

import Execution
import ExecutionTree

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree


import Test.QuickCheck

import Data.Map ( Map, (!) )
import qualified Data.Map as Map


instance Show (Program gr) where
  show p = "rofl"

-- p     = orderConflict
-- p     = cdomIsBroken'
p     = cdomIsBroken2
-- p     = directFlowThread
cdom  = idomChef
θ     = allFinishedExecutionTraces p defaultInput
trees = fmap fst $
        allFinalTreeStates         p defaultInput

main = do
  -- putStrLn $ show $ length $ cdomIsDomViolations     p θ     cdom
  -- putStrLn $ show $ length $ cdomIsCdomViolations    p θ     cdom
  putStrLn $ show $ length $ cdomIsCdomViolations'   p θ     cdom
  -- putStrLn $ show $ length $ cdomIsBeforeViolations  p θ     cdom
  -- putStrLn $ show $ length $ cdomIsTreeDomViolations p trees cdom




isAtLeastAsPreciseAs :: (Program Gr -> Bool) -> (Program Gr -> Bool) -> GeneratedProgram -> Bool
isAtLeastAsPreciseAs a1 a2 generated = a2 p ⊑ a1 p
  where p = toProgram generated
