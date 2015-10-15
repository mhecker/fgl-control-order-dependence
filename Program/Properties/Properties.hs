{-# LANGUAGE NamedFieldPuns #-}
module Program.Properties where


import Program.Examples

import Program.Properties.CDom
import Program.CDom

import Execution
import ExecutionTree

import Data.Map ( Map, (!) )
import qualified Data.Map as Map


-- p     = orderConflict
-- p     = cdomIsBroken'
p     = cdomIsBroken2
-- p     = directFlowThread
cdom  = idomChef
θ     = allFinishedExecutionTraces p defaultInput
trees = fmap fst $
        allFinalTreeStates         p defaultInput

main = do
--  putStrLn $ show $ length $ cdomIsDomViolations     p θ     cdom
  putStrLn $ show $ length $ cdomIsCdomViolations    p θ     cdom
  putStrLn $ show $ length $ cdomIsBeforeViolations  p θ     cdom
  putStrLn $ show $ length $ cdomIsTreeDomViolations p trees cdom

