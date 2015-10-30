{-# LANGUAGE NamedFieldPuns #-}
module Program.Properties.TimingDependence where


import Unicode
import Data.Bool.Unicode

import Program
import Execution
import ExecutionTree


import IRLSOD

-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Graph


import Data.List (takeWhile, dropWhile)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Util
-- import Data.Set.Unicode

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Query.Dominators



delays :: DynGraph gr => Program gr -> [ExecutionTree] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
delays p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          e1 <- θ,
          [[ (i,n') | (i,(_,(n',_),_)) <- e1, n' == n]
          e2 <- θ,
          let hb = someHappensBeforeAll e,
          (not (occurencesOf e n == [] ∨  c `hb` n))
          ∨
          (not (occurencesOf e m == [] ∨  c `hb` m))
    ]
  where cdom = cd p

consecutive :: [a] -> [(a,a)]
consecutive [] = []
consecutive l= tail $ zip (undefined:l) l

