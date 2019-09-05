{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.DataConflict where

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



dataConflicts :: DynGraph gr => Program gr -> Map Node (Set Node)
dataConflicts p@(Program {tcfg}) = Map.fromList $
    [ (n, Set.fromList [ m | x <- Set.toList $ def tcfg n,  -- TODO: performance
                             m <- nodes tcfg,
                             (n,m) ∈ mhp,
                             x ∈ (use tcfg m) ∪ (def tcfg m)
                        ]
       )
     | n <- nodes tcfg ]
  where mhp = mhpSetFor p

dataConflictGraphP :: DynGraph gr => Program gr -> gr CFGNode ()
dataConflictGraphP p@(Program { tcfg }) = mkGraph (labNodes tcfg) [ (n,n',()) | (n,n's) <- Map.toList conflicts, n' <- Set.toList n's]
  where conflicts = dataConflicts p

