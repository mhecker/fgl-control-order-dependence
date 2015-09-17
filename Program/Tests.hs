module Program.Tests where

import System.Process
import Data.Graph.Inductive.Dot


import Program
import Program.Examples
import Program.MultiThread
import Program.MHP
import Program.CDom
import Program.Analysis

import IRLSOD

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
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

