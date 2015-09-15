{-# LANGUAGE NamedFieldPuns #-}
module Program.CDom where

import Algebra.Lattice

import Unicode

import Program
import Program.MultiThread
import IRLSOD

-- import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.Dominators




-- mhpFor :: DynGraph gr => Program gr -> Map (Node,Node) Bool

-- domTree ::   Map Node Node
-- domTree  = Map.fromList $ 


idomChef  :: DynGraph gr => Program gr ->  Map (Node,Node) Node
idomChef p@(Program {tcfg, entryOf, mainThread} ) = Map.fromList
    [ ((n,n'), lca n n')   | n <- nodes tcfg, n' <- nodes tcfg ]
  where dom :: Map Node Node
        dom = Map.fromList $ iDom tcfg (entryOf mainThread)

        lca :: Node -> Node -> Node
        lca n n' = c
          where (c,_) = last $ takeWhile (\(a,b) -> a==b) $ zip (pathToRoot n)
                                                                (pathToRoot n')
                pathToRoot node
                  | node `Map.member` dom = pathToRoot (dom ! node) ++ [node]
                  | otherwise             = [node]




