{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Program.MultiThread where


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


{- Es passt schon die default Instanziierung:
   instance BoundedJoinSemiLattice Bool
-}


-- spawnGraph :: Graph gr => Program gr -> gr StaticThread ()
-- spawnGraph p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) =
--   mkGraph [(thread,thread) | thread <- staticThreads]
--           [(t1,t2,())      | t1 <- staticThreads,
--                              t2 <- staticThreads,
--                              spawnnode <- pre tcfg (entryOf t2),
--                              staticThreadOf spawnnode == t1 ]


multiThreadAnalysis :: Graph gr => Program gr -> DataflowAnalysis Bool CFGEdge
multiThreadAnalysis p@(Program { tcfg, staticThreadOf, staticThreads, entryOf, exitOf }) = DataflowAnalysis {
    transfer = transfer,
    initial = initial
  }
 where
  initial = False
  transfer (n1,n2,Spawn) isInMultithread = isInMultithread ⊔ isInCycle (cfg p (staticThreadOf n1)) n1
                                                           ⊔ (length (pre tcfg n2) > 1)
  transfer e isInMultithread = isInMultithread


isInMultiThread :: Graph gr => Program gr -> Map Node Bool
isInMultiThread p@(Program { tcfg, entryOf, mainThread}) = analysis (multiThreadAnalysis p) tcfg (entryOf mainThread)

isMultiThread :: Graph gr => Program gr -> Map StaticThread Bool
isMultiThread p@(Program { tcfg, entryOf, staticThreads } ) =
    Map.fromList [ (thread, (isInMultiThread p) ! (entryOf thread)) | thread <- Set.toList staticThreads ]
