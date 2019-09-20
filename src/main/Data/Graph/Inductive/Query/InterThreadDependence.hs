{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.InterThreadDependence where

import Unicode

import IRLSOD
import Program

import Algebra.Lattice

import Data.Char

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.Dataflow
import Data.Graph.Inductive.Query.Dependence

import Program.MHP
import IRLSOD



interThreadDependence :: DynGraph gr => Program gr -> Set (Node,Node) -> Map Node (Set Node)
interThreadDependence p@(Program {tcfg}) mhp = Map.fromList $
    [ (n, Set.fromList [ m | x <- Set.toList $ def tcfg n,
                             isGlobalName x,
                             m <- nodes tcfg,
                             (n,m) ∈ mhp,
                             x ∈ (use tcfg m)
                        ]
       )
     | n <- nodes tcfg ]

interThreadDependenceGraphP :: DynGraph gr => Program gr -> Set (Node,Node) -> gr CFGNode Dependence
interThreadDependenceGraphP p@(Program { tcfg }) mhp = mkGraph (labNodes tcfg) [ (n,n',InterThreadDependence) | (n,n's) <- Map.toList interdeps, n' <- Set.toList n's]
  where interdeps = interThreadDependence p mhp

