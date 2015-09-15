{-# LANGUAGE NamedFieldPuns #-}
module Program.Analysis where


import Algebra.Lattice

import Unicode

import Program
import Program.CDom
import Program.MHP
-- import IRLSOD

-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Graph


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Query.Dataflow
import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Query.TransClos

import Data.Graph.Inductive.Query.ProgramDependence




minimalClassification p@(Program { tcfg, clInit }) =
  (㎲⊒) (Map.fromList [ (n, clInit n) | n <- nodes tcfg ])
    (\cl -> cl ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre pdg n])
                               | n <- nodes tcfg])
               ⊔ (Map.fromList [ (n,(∐) [ cl ! c' | m <- Set.toList $ mhp ! n, let c = idom ! (n,m),  c' <- Set.toList $ chop c n])
                               | n <- nodes tcfg])
    )

 where pdg = programDependenceGraphP p
       idom = idomChef p
       trnsclos = trc tcfg
       mhp :: Map Node (Set Node)
       mhp = Map.fromList [ (n, Set.fromList [ m | ((n',m), True) <- Map.assocs mhpSet, n' == n])
                          | n <- nodes tcfg ]
         where mhpSet = mhpFor p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance

