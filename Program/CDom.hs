{-# LANGUAGE NamedFieldPuns #-}
module Program.CDom where

import Algebra.Lattice

import Unicode
import Data.Bool.Unicode

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



idomMohrEtAl :: DynGraph gr => Program gr ->  Map (Node,Node) Node
idomMohrEtAl p@(Program {tcfg, entryOf, mainThread} ) = Map.fromList
    [ ((n,n'), leastValidFrom $ lca n n')   | n <- nodes tcfg, n' <- nodes tcfg ]
  where dom :: Map Node Node
        dom = Map.fromList $ iDom tcfg (entryOf mainThread)

        inMulti = isInMultiThread p
        inCycle = isInCycle tcfg -- TODO: ggf auf zyklen innerhalb von threads einschränken?!?!?

        leastValidFrom :: Node -> Node
        leastValidFrom c
          | (inMulti ! c) ∨ (inCycle c) = leastValidFrom (dom ! c)
          | otherwise                   = c


        lca :: Node -> Node -> Node
        lca n n' = c
          where (c,_) = last $ takeWhile (\(a,b) -> a==b) $ zip (pathToRoot n)
                                                                (pathToRoot n')
                pathToRoot node
                  | node `Map.member` dom = pathToRoot (dom ! node) ++ [node]
                  | otherwise             = [node]


domPathBetween dom dominated dominator
    | dominated  == dominator = [dominated]
    | otherwise               = domPathBetween dom dominated' dominator ++ [dominated]
  where Just dominated' = Map.lookup dominated dom
