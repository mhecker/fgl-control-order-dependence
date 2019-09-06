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
import Data.Graph.Inductive.Util hiding (isInCycle)
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


threadsOfAnalysis :: Graph gr => Program gr -> DataflowAnalysis (Set StaticThread) CFGEdge
threadsOfAnalysis p@(Program {  mainThread, staticThreads, entryOf, procedureOf }) = DataflowAnalysis {
    transfer = transfer,
    initial = initial
  }
 where
  initial = Set.fromList [mainThread]
  transfer (n1,n2,Spawn) threads = Set.fromList [ thread | thread <- Set.toList $ staticThreads, entryOf (procedureOf thread) == n2]
  transfer (n1,n2,Return)threads = Set.empty
  transfer e             threads = threads

threadsOf :: Graph gr => Program gr -> Map Node (Set StaticThread)
threadsOf p@(Program { tcfg, entryOf, procedureOf, mainThread}) = analysis (threadsOfAnalysis p) tcfg (entryOf (procedureOf mainThread))

--              InCycle
-- FromIntraCycle     FromCall
--            NotInCycle
data CycleReason = NotInCycle | FromIntraCycle | FromCall | InCycle  deriving (Show, Eq)
instance JoinSemiLattice CycleReason where
  NotInCycle     `join` x                = x
  x              `join` NotInCycle       = x

  FromIntraCycle `join` FromIntraCycle   = FromIntraCycle
  FromIntraCycle `join` x                = InCycle
  x              `join` FromIntraCycle   = InCycle

  FromCall       `join` FromCall   = FromCall
  FromCall       `join` x          = InCycle
  x              `join` FromCall   = InCycle

  InCycle        `join` InCycle           = InCycle

instance BoundedJoinSemiLattice CycleReason  where
  bottom = NotInCycle


instance MeetSemiLattice CycleReason where
  InCycle       `meet` x                = x
  x              `meet` InCycle         = x

  FromIntraCycle `meet` FromIntraCycle   = FromIntraCycle
  FromIntraCycle `meet` x                = NotInCycle
  x              `meet` FromIntraCycle   = NotInCycle

  FromCall       `meet` FromCall   = FromCall
  FromCall       `meet` x          = NotInCycle
  x              `meet` FromCall   = NotInCycle

  NotInCycle     `meet` NotInCycle       = NotInCycle


isInCycleAnalysis:: DynGraph gr => Program gr -> DataflowAnalysis CycleReason CFGEdge
isInCycleAnalysis p@(Program {  mainThread, staticProcedureOf, staticProcedures, entryOf, procedureOf }) = DataflowAnalysis {
    transfer = transfer,
    initial = initial
  }
 where
  initial = NotInCycle
  transfer (n1, n2, Spawn)  inCycle =            (isInProcedureCycleMap ! (staticProcedureOf n2)) ! n2
  transfer (n1, n2, Call)   inCycle
    | inCycle == FromIntraCycle     = FromCall ⊔  (isInProcedureCycleMap ! (staticProcedureOf n2)) ! n2
    | otherwise                     = inCycle  ⊔  (isInProcedureCycleMap ! (staticProcedureOf n2)) ! n2
  transfer (n1, n2, Return) inCycle =            (isInProcedureCycleMap ! (staticProcedureOf n2)) ! n2
  transfer (n1, n2, e)      inCycle = (inCycle ⊓ FromCall) ⊔  (isInProcedureCycleMap ! (staticProcedureOf n2)) ! n2
  
  isInProcedureCycleMap  = Map.fromList [ (procedure, fmap toReason $ isInCycleMap (cfgOfProcedure p procedure)) | procedure <- Set.toList $ staticProcedures ]
    where toReason True  = FromIntraCycle
          toReason False = NotInCycle

isInCycle :: DynGraph gr => Program gr -> Map Node Bool
isInCycle p@(Program { tcfg, entryOf, procedureOf, mainThread}) = fmap (/= NotInCycle) $ analysis (isInCycleAnalysis p) tcfg (entryOf (procedureOf mainThread))


multiThreadAnalysis :: DynGraph gr => Program gr -> DataflowAnalysis Bool CFGEdge
multiThreadAnalysis p@(Program { tcfg, staticProcedures, entryOf, exitOf }) = DataflowAnalysis {
    transfer = transfer,
    initial = initial
  }
 where
  initial = False
  transfer (n1,n2,Spawn) isInMultithread = isInMultithread ⊔ (isInCycleMap ! n1)
                                                           ⊔ (length (pre tcfg n2) > 1)
  transfer e isInMultithread = isInMultithread
  isInCycleMap = isInCycle p

isInMultiThread :: DynGraph gr => Program gr -> Map Node Bool
isInMultiThread p@(Program { tcfg, entryOf, procedureOf, mainThread}) = analysis (multiThreadAnalysis p) tcfg (entryOf $ procedureOf $ mainThread)

isMultiThread :: DynGraph gr => Program gr -> Map StaticThread Bool
isMultiThread p@(Program { tcfg, entryOf, procedureOf, staticThreads } ) =
    Map.fromList [ (thread, (isInMultiThread p) ! (entryOf $ procedureOf $ thread)) | thread <- Set.toList staticThreads ]
