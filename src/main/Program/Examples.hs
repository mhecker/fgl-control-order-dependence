{-# LANGUAGE TemplateHaskell #-}
module Program.Examples where


import Program
import Program.Generator (Generated(..), GeneratedProgram(..), IntraGeneratedProgram(..), toProgram, toProgramIntra)
import Program.For
import Program.Defaults

import Program.Typing.FlexibleSchedulerIndependentChannels (ForProgram(..))
import qualified Program.Typing.ResumptionBasedSecurity as Res (ForProgram(..), for2ResumptionFor) 


import IRLSOD

import Unicode

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Util

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode



{-    
        1
       / \
     2     3
     ^     ^
      \---/
-}
exampleIrreducible :: Program Gr
exampleIrreducible = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticThreads  = Set.fromList [1],
    staticProcedureOf = staticProcedureOf,
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..3] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = undefined
        tcfg = mkGraph [(n,n) | n <- [1..3]] $
                       [(1,2,true), (1,3,false), (2,3,nop), (3,2,nop)]



exampleSimonReducibleWod :: Program Gr
exampleSimonReducibleWod = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..5] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 5
        tcfg = mkGraph [(n,n) | n <- [1..5]] $
                       [(1,2,true), (1,3,false), (2,4,true), (2,5,false), (3,5,nop),(4,5,nop)]



exampleSimonReducibleWod2 :: Program Gr
exampleSimonReducibleWod2 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [0..4] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 0
        exitOf "1" = 4
        tcfg = mkGraph [(n,n) | n <- [0..4]] $
                       [(0,4,nop), (4,1,nop), (4,2,nop), (1,2,nop), (1,3,nop),(2,3,nop), (3,4,nop)]



{-    
        1---------|
        |         |
        2         |
       / \        |
      /   \       |
     /     \      |
 -->3->   <-6<--  |
 |  4 |   | 7  |  |
 ---5 |   | 8---  |
      |   |       |
      \   /       |
       \ /        |
        9         |
       10<--------|
-}
exampleSimpleClassic :: Program Gr
exampleSimpleClassic = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..10] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 10
        tcfg = mkGraph [(n,n) | n <- [1..10]]  $
                       [(1,2,true), (2,3,true), (2,6,false), (1,10,false)]
                   ++  [(3,4,false),(4,5,nop),(5,3,nop),(3,9,true)]
                   ++  [(6,7,false),(7,8,nop),(8,6,nop),(6,9,true)]
                   ++  [(9,10,nop)]




{-    
        1---------|
        |         |
        2         |
       / \        |
      /   \       |
     /     \      |
 -->3->   <-6<--  |
 |  4 |   | 7  |  |
 ---5 |   | 8---  |
      |   |       |
      \   /       |
       \ /        |
        9         |
       10<--------|
-}
exampleSimpleArtificialEndNode :: Program Gr
exampleSimpleArtificialEndNode = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..10] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 10
        tcfg = mkGraph [(n,n) | n <- [1..10]]  $
                       [(1,2,true), (2,3,true), (2,6,false), (1,10,false)]
                   ++  [(3,4,false),(4,5,nop),(5,3,nop),(3,9,true)]
                   ++  [(6,7,false),(7,8,nop),(8,6,nop),(6,10,true), (7,10,true), (8,10,true)]
                   ++  [(9,10,nop)]




{-    
        1---------|
        |         |
        2         |
       / \        |
      /   \       |
     /     \      |
 -->3->     6<--  |
 |  4 |     7  |  |
 ---5 |     8---  |
      |           |
      \           |
       \          |
        9         |
       10<--------|
-}
exampleSimpleNoUniqueEndNode :: Program Gr
exampleSimpleNoUniqueEndNode = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..10] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 10
        tcfg = mkGraph [(n,n) | n <- [1..10]]  $
                       [(1,2,true), (2,3,true), (2,6,false), (1,10,false)]
                   ++  [(3,4,false),(4,5,nop),(5,3,nop),(3,9,true)]
                   ++  [(6,7,false),(7,8,nop),(8,6,nop)]
                   ++  [(9,10,nop)]



{-    
        1---------|
        |         |
        2         |
       / \        |
      /   \       |
     /     \      |
 -->3->     6<--  |
 |  4 |     7  |  |
 -5/| |     |\8-  |
 |  | |     |  |  |
 |-12 \     11-|  |
       \          |
        9         |
       10<--------|
-}
exampleSimpleNoUniqueEndNodeWithChoice :: Program Gr
exampleSimpleNoUniqueEndNodeWithChoice = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..12] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 10
        tcfg = mkGraph [(n,n) | n <- [1..12]]  $
                       [(1,2,true), (2,3,true), (2,6,false), (1,10,false)]
                   ++  [(6,7,true), (7,8,true),(8,6,true)]
                   ++  [            (7,11,false),(11,8,nop)]
                   ++  [(3,4,false),(4,5,true),(5,3,true)]
                   ++  [            (4,12,false),(12,5,nop)] ++ [(3,9,true)]
                   ++  [(9,10,nop)]


{-    
        1---------|
        |         |
        2         |
       / \        |
      /   \       |
     /     \      |
 -->3->     6<--   |
 |  4 |     7  |   |
 -5/| |     |\8-<- |
 |  | |     |  | | |
 |-12 \     11-| | |
       \    |    | |
        9   13---| |
       10<--------|
-}
exampleSimpleNoUniqueEndNodeWithChoice2 :: Program Gr
exampleSimpleNoUniqueEndNodeWithChoice2 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..14] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 10
        tcfg = mkGraph [(n,n) | n <- [1..14]] $
                       [(1,2,true), (2,3,true), (2,6,false), (1,10,false)]
                   ++  [(6,7,true), (7,8,true),(8,6,true)]
                   ++  [            (7,11,false),(11,8,true)]
                   ++  [(11,13,false), (13,8,nop) ]
                   ++  [(3,4,false),(4,14,true),(14,5,nop),(5,3,true)]
                   ++  [            (4,12,false),(12,5,nop)] ++ [(3,9,true)]
                   ++  [(9,10,nop)]
                   -- ++  [(11,10,nop)]




{-    1
      2----spawn-
      7<--       3
    8    |     4   5
    9    |       6
      10-|
      11
      12
-}
example1 :: Program Gr
example1 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,2],
    staticProcedures  = Set.fromList ["1","2"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1,2,7,8,9,10,11,12] = "1" 
         | n ∊ [3,4,5,6] = "2"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        entryOf "2" = 3
        exitOf "1" = 12
        exitOf "2" = 6
        tcfg = mkGraph (genLNodes 1 12) $
                        [(1,2,Assign (Global "x") (Val 42)),(2,3,spawn),(3,4,false),(3,5,true),(4,6,Print (Var (Global "x")) stdOut),(5,6,nop)]
                    ++  [(2,7,nop),(7,8,true),(8,9,nop),(9,10,nop),(10,11,true),(10,7,false),(11,12,Assign (Global "x") (Var (Global "x")))]


{-    1
      2
      3
    4   5
      6
   <--7<-
   |  8  |
   |  9---
   |
   ->10
     11
     12
-}
example2 :: Program Gr
example2 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..12] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 12
        tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,Assign (Global "x") (Val 42)), (2,3,Read (Global "h") stdIn),(3,4,Guard True (Leq (Var (Global "h")) (Var (Global "h")))),(3,5,Guard False (Leq (Var (Global "h")) (Var (Global "h")))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(7,8,false),(8,9,nop),(9,7,nop),(7,10,true),(10,11,Assign (Global "x") (Var (Global "x"))),(11,12,nop)]



{-    1
      2
    3   4
      5
      6
      7<--
      8  |
      9  |
      10--
      11
      12
-}
example2' :: Program Gr
example2' = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..12] = "1" 
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 12
        tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,Assign (Global "x") (Val 42)),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,Assign (Global "x") (Var (Global "x"))),(6,7,nop)]
                   ++  [(7,8,nop),(8,9,nop),(9,10,nop),(10,7,false),(10,11,true),(11,12,Assign (Global "x") (Var (Global "x")))]




--    15
--  /    \
--  |    |
--  |    v
--  |<---1 ----
--  |    ^    |
--  |    |    |
--  |<---4<----
--  |   /
--  |
--  v
-- -1
exampleNticd :: Program Gr
exampleNticd = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [3, 1, 6, 10, 15, 42] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 15
        exitOf "1" = 42
        tcfg =  mkGraph [(15,15),(3,3),(1,1),(42,42)] [(3,1,nop),(3,42,nop),(1,3,nop),(1,42,nop),(15,1,nop),(15,42,nop)]



exampleSmnF5 :: Program Gr
exampleSmnF5 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  =  Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [8, 5, 1, 12, 2] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 12
        exitOf "1" = 5
        tcfg =  mkGraph [(8,8),(5,5),(1,1),(12,12),(2,2)] [(8,5,nop),(1,8,nop),(1,5,nop),(1,2,nop),(2,1,nop),(12,8,nop),(12,5,nop),(12,1,nop)]

exampleSmnF5' :: Program Gr
exampleSmnF5' = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  =  Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [8, 5, 1, 12, 2] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 12
        exitOf "1" = 5
        tcfg =  mkGraph [(8,8),(5,5),(1,1),(12,12),(2,2)] [(8,5,nop),(1,8,nop),(1,5,nop),(1,2,nop),(2,1,nop),(12,8,nop),(12,5,nop),(12,1,nop)]


exampleSmnF4Gfp :: Program Gr
exampleSmnF4Gfp = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  =  Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [1, 3, 4, 5] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 4
        tcfg =  mkGraph [(1,1),(3,3),(4,4),(5,5)] [(1,4,nop),(1,3,nop),(3,5,nop),(3,4,nop),(5,4,nop)]



exampleSmnF4Gfp2 :: Program Gr
exampleSmnF4Gfp2 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  =  Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [1, 3, 4, 5] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "4" = 4
        tcfg =  mkGraph [(1,1),(3,3),(4,4),(5,5)] [(1,3,nop),(3,5,nop),(3,4,nop),(5,3,nop)]



exampleSmnF4WithReachGfp :: Program Gr
exampleSmnF4WithReachGfp = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  =  Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [8, 13, 6, 16, 17] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 17
        exitOf "1" = undefined
        tcfg =  mkGraph [(8,8),(13,13),(6,6),(16,16),(17,17)] [(8,13,nop),(8,16,nop),(16,6,nop),(6,16,nop), (17,8,nop),(17,13,nop)]


exampleSmnF4WithReachGfp2 :: Program Gr
exampleSmnF4WithReachGfp2 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  =  Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [8, 13, 6, 16, 17] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 17
        exitOf "1" = undefined
        tcfg =  mkGraph [(8,8),(13,13),(6,6),(16,16),(666,666), (17,17)] [(8,13,nop),(8,16,nop),(16,6,nop),(6,16,nop),(16,666,nop),(666,16,nop),(17,8,nop),(17,13,nop)]

exampleNticd2SmnF5 :: Program Gr
exampleNticd2SmnF5 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [17, 1, 2, 3, 7, 8] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 8
        exitOf "1" = 7
        tcfg = mkGraph [(17,17),(1,1),(2,2),(3,3),(7,7),(8,8)] [(1,7,nop), (17,1,nop),(17,2,nop),(17,3,nop),(2,17,nop),(3,17,nop),(3,7,nop),(8,17,nop),(8,1,nop),(8,2,nop),(8,3,nop),(8,7,nop)]


exampleNtscd :: Program Gr
exampleNtscd = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
         (1,ForC 1 (Seq (ForC 2
                            (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))
                        (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x"))))
                            (ReadFromChannel (Global "a") "stdIn")
                         {-else-}
                            (ReadFromChannel (Global "a") "stdIn"))))
         ]


exampleNtscd' :: Program Gr
exampleNtscd' = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [2,5,3,7,8,10,11,12,15] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 2
        exitOf "1" = 3
        tcfg = mkGraph [(2,2),(5,5),(3,3),(7,7),(10,10),(11,11),(12,12),(15,15)]
                       [(2,5,nop),(5,3,nop),(5,7,nop),(7,10,nop),(10,11,nop),(11,15,nop),(10,12,nop),(12,15,nop),(15,5,nop)]



exampleNtscd2 :: Program Gr
exampleNtscd2 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [-20,15,18,22,27] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 27
        exitOf "1" = 18
        tcfg = mkGraph [(-20,-20),(15,15),(18,18),(22,22),(27,27)] [(-20,15,nop),(-20,18,nop),(15,18,nop),(15,22,nop),(22,18,nop),(27,-20,nop),(27,18,nop)]


{-
     1
     2 ----   3
     5         4
     6
     7
-}
example3 :: Program Gr
example3 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,2],
    staticProcedures  = Set.fromList ["1","2"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [1,2,5,6,7] = "1"
         | n ∊ [3,4]      = "2"
         | otherwise = error "unknown node"
        entryOf "1" = 1
        entryOf "2" = 3
        exitOf "1" = 7
        exitOf "2" = 4
        tcfg = mkGraph (genLNodes 1 7)  $
                       [(1,2,nop),(2,3,spawn),(3,4,Assign (Global "x") (Val 17))]
                   ++  [(2,5,nop),(5,6,Assign (Global "x") (Val 4)),(6,7,Print (Var (Global "x")) stdOut)]




{-    1
      2 Read h
      3 if h 
    4   5
      6
      7 ----------8
      10          9
      11
-}
example4 :: Program Gr
example4 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,2],
    staticProcedures  = Set.fromList ["1","2"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ ([1..7] ++ [10,11]) = "1"
         | n ∊ ([8..9])           = "2"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        entryOf "2" = 8
        exitOf "1" = 11
        exitOf "2" = 9
        tcfg = mkGraph (genLNodes 1 11)  $
                       [(1,2,Assign (Global "x") (Val 42)), (2,3,Read (Global "h") stdIn),(3,4,Guard True (Leq (Var (Global "h")) (Var (Global "h")))),(3,5,Guard False (Leq (Var (Global "h")) (Var (Global "h")))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(7,8,Spawn),(7,10, NoOp), (10,11,Print (Var (Global "x")) stdOut),(8,9,Print (Var (Global "x")) stdOut)]


{-          1
   Read h   2 -----spawn-- 8
           11
     if h   3              9 print l 
          4   5
            6
            7 print l
           10 
-}
example5 :: Program Gr
example5 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,2],
    staticProcedures  = Set.fromList ["1","2"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ ([1..7] ++ [10,11]) = "1"
         | n ∊ ([8..9])         = "2"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        entryOf "2" = 8
        exitOf "1" = 10
        exitOf "2" = 9
        tcfg = mkGraph (genLNodes 1 11)  $
                       [(1,2,Assign (Global "x") (Val 42)), (2,11, NoOp), (11,3,Read (Global "h") stdIn),(3,4,Guard True (Leq (Var (Global "h")) (Var (Global "h")))),(3,5,Guard False (Leq (Var (Global "h")) (Var (Global "h")))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(2,8,Spawn),(7,10,Print (Var (Global "x")) stdOut),(8,9,Print (Var (Global "x")) stdOut)]






{-       1
         2 Read h
    ---  3----false --> 4
  t|     ^              5 if h
  r|     |            6   7
  u|     |              8  ----spawn--->  9 print l
  e|     | -------------                 10
   |
   |---->11  print l
         12
-}
example6 :: Program Gr
example6 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,2],
    staticProcedures  = Set.fromList ["1","2"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ ([1..8]   ++ [11,12]) = "1"
         | n ∊ ([9..10])             = "2"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        entryOf "2" = 9
        exitOf "1" = 12
        exitOf "2" = 10
        tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,Assign (Global "x") (Val 42)), (2,3,Read (Global "h") stdIn),(3,4,false),(3,11,true),(11,12,Print (Var (Global "x")) stdOut),
                        (4,5,nop), (5,6,Guard True (Leq (Var (Global "h")) (Var (Global "h")))),(5,7,Guard False (Leq (Var (Global "h")) (Var (Global "h")))),
                                   (6,8,nop),                     (7,8,nop),
                        (8,3,nop),
                        (8,9,Spawn),(9,10,Print (Var (Global "x")) stdOut)]



{-          1
            2 -----spawn--> 6
            |               | print l
            3               7
   Read h   |
            4
   print l  |
            5
-}
example7 :: Program Gr
example7 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,2],
    staticProcedures  = Set.fromList ["1","2"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ ([1..5]) = "1"
         | n ∊ ([6..7]) = "2"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        entryOf "2" = 6
        exitOf "1" = 5
        exitOf "2" = 7
        tcfg = mkGraph (genLNodes 1 7)  $
                       [(1,2,Assign (Global "x") (Val 42)), (2,3,nop), (3,4,Read (Global "h") stdIn),(4,5,Print (Var (Global "x")) stdOut)]
                   ++  [(2,6,Spawn),(6,7,Print (Var (Global "x")) stdOut)]


{-
          1
          |
         23
          |  Read h
         20
          |  zero = 0
         21
          |  one = 1
         22
          |  tmp = 1
          2
    ¬ h /   \ h
       3     4
        \   /tmp = 50
          5
          |
          6 -----spawn ------------------>   201
          |                                   |   tmp2 = 50
--------> 7 -------                          202
|         |       |
|  tmp > 0|       |
|         8       |
|  tmp--  |       |
|         |       |  ¬ (tmp > 0)
----------9       |
                  |
         10 <------
          |
         11
          | tmp2 = 1
         12 -----spawn ----------------->   301
          |                                  |   print 0
-------->13 -------                         302
|         |       |
| tmp2 > 0|       |
|        14       |
| tmp2--  |       |
|         |       |  ¬ (tmp2 > 0)
---------15       |
                  |
         16 <------
          |
          | print 1
         17
-}


example8 :: Program Gr
example8 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,2,3],
    staticProcedures  = Set.fromList ["1","2","3"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ ([1..17] ++ [20..23]) = "1"
         | n ∊ ([201..202]) = "2"
         | n ∊ ([301..302]) = "3"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        entryOf "2" = 201
        entryOf "3" = 301
        exitOf "1" = 17
        exitOf "2" = 202
        exitOf "3" = 302
        tcfg = mkGraph [(n,n) | n <- [1..17] ++ [20..23] ++ [201..202] ++ [301..302]]  $
                       [( 1,23,nop),
                        (23,20,Read (Global "h") stdIn),
                        (20,21, Assign (Global "zero") (Val 0)),
                        (21,22, Assign (Global "one") (Val 1)),
                        (22,2,Assign (Global "tmp") (Val 1)), (2,3, Guard False (Leq (Var (Global "h")) (Var (Global "h")))),
                                                     (2,4, Guard True  (Leq (Var (Global "h")) (Var (Global "h")))),
                        (4,5,Assign (Global "tmp") (Val 50)),
                        (3,5,nop),
                        (5,6,nop),
                        (6,7,nop),(6,201,Spawn),
                        (7,10, Guard False (Not $ Leq (Var (Global "tmp")) (Var (Global "zero")))),
                        (7, 8, Guard True  (Not $ Leq (Var (Global "tmp")) (Var (Global "zero")))),
                        (8, 9, Assign (Global "tmp") (Plus (Var (Global "tmp")) (Val (-1)))),
                        (9, 7, nop),
                        (10,11,nop),
                        (11,12,Assign (Global "tmp2") (Val 1)),
                        (12,301,Spawn),
                        (12,13,nop),
                        (13,16, Guard False (Not $ Leq (Var (Global "tmp2")) (Var (Global "zero")))),
                        (13,14, Guard True  (Not $ Leq (Var (Global "tmp2")) (Var (Global "zero")))),
                        (14,15, Assign (Global "tmp2") (Plus (Var (Global "tmp2")) (Val (-1)))),
                        (15,13, nop),
                        (16,17, Print (Val 1) stdOut),

                        (201,202, Assign (Global "tmp2") (Val 50)),

                        (301,302, Print (Val 0) stdOut)]


{-
          1
          | 
         23 
          |  Read h
         20
          |  zero = 0
         21
          |  one = 1
         22
          |  tmp = 1
          2
    ¬ h /   \ h
       3     4
        \   /tmp = 50
          5
          |
          6 -----spawn ------------------>   201
          |                                   |   nop
--------> 7 -------                          202
|         |       |
|  tmp > 0|       |
|         8       |
|  tmp--  |       |
|         |       |  ¬ (tmp > 0)
----------9       |
                  |
         10 <------
          |
         11
          | tmp2 = 1
         12 -----spawn ----------------->   301
          |                                  |   print 0
-------->13 -------                         302
|         |       |
| tmp2 > 0|       |
|        14       |
| tmp2--  |       |
|         |       |  ¬ (tmp2 > 0)
---------15       |
                  |
         16 <------
          |
          | print 1
         17
-}


example8' :: Program Gr
example8' = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads    = Set.fromList [1,2,3],
    staticProcedures = Set.fromList ["1","2","3"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ ([1..17] ++ [20..23]) = "1"
         | n ∊ ([201..202]) = "2"
         | n ∊ ([301..302]) = "3"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        entryOf "2" = 201
        entryOf "3" = 301
        exitOf "1" = 17
        exitOf "2" = 202
        exitOf "3" = 302
        tcfg = mkGraph [(n,n) | n <- [1..17] ++ [20..23] ++ [201..202] ++ [301..302]]  $
                       [( 1,23,nop),
                        (23,20,Read (Global "h") stdIn),
                        (20,21, Assign (Global "zero") (Val 0)), -- TODO: entfernen
                        (21,22, Assign (Global "one") (Val 1)),  -- TODO: entfernen
                        (22,2,Assign (Global "tmp") (Val 1)), (2,3, Guard False (Leq (Var (Global "h")) (Var (Global "h")))),
                                                     (2,4, Guard True  (Leq (Var (Global "h")) (Var (Global "h")))),
                        (4,5,Assign (Global "tmp") (Val 50)),
                        (3,5,nop),
                        (5,6,nop),
                        (6,7,nop),(6,201,Spawn),
                        (7,10, Guard False (Not $ Leq (Var (Global "tmp2")) (Var (Global "zero")))),
                        (7, 8, Guard True  (Not $ Leq (Var (Global "tmp2")) (Var (Global "zero")))),
                        (8, 9, Assign (Global "tmp") (Plus (Var (Global "tmp")) (Val (-1)))),
                        (9, 7, nop),
                        (10,11,nop),
                        (11,12,Assign (Global "tmp2") (Val 1)),
                        (12,301,Spawn),
                        (12,13,nop),
                        (13,16, Guard False (Not $ Leq (Var (Global "tmp2")) (Var (Global "zero")))),
                        (13,14, Guard True  (Not $ Leq (Var (Global "tmp2")) (Var (Global "zero")))),
                        (14,15, Assign (Global "tmp2") (Plus (Var (Global "tmp2")) (Val (-1)))),
                        (15,13, nop),
                        (16,17, Print (Val 1) stdOut),

                        (201,202, nop),

                        (301,302, Print (Val 0) stdOut)]

{-
1 void main ( ) :
2   fork thread_1 ( ) ;
3   fork thread_2 ( ) ;
7

4 void thread_1 ( ) :
5   fork thread_2 ( ) ;
8

6 void thread_2 ( ) :
9
-}
threadSpawn1 :: Program Gr
threadSpawn1 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1,4,6],
    staticProcedures  = Set.fromList ["1", "4", "6"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [1,2,3,7] = "1"
         | n ∊ [4,5,8]   = "4"
         | n ∊ [6,9]     = "6"
         | otherwise = error "unknown node"
        entryOf "1" = 1
        entryOf "4" = 4
        entryOf "6" = 6
        exitOf "1" = 7
        exitOf "4" = 8
        exitOf "6" = 9
        tcfg = mkGraph (genLNodes 1 9)  $
                       [(1,2,nop),(2,4,spawn),(2,3,nop),(3,6,spawn),(3,7,nop)]
                   ++  [(4,5,nop),(5,6,spawn),(5,8,nop)]
                   ++  [(6,9,nop)]


{-
1 void main ( ) :
2   while ( . . . ) :
3     fork thread_1 ( ) ;
4

5 void thread_1 ( ) :
6   fork thread_2 ( ) ;
7

8 void thread_2 ( ) :
9
-}
threadSpawn2 :: Program Gr
threadSpawn2 = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads     = Set.fromList [1,5,8],
    staticProcedures  = Set.fromList ["1","5","8"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n
         | n ∊ [1,2,3,4] = "1"
         | n ∊ [5,6,7]   = "5"
         | n ∊ [8,9]     = "8"
         | otherwise = error "unknown node"
        entryOf "1" = 1
        entryOf "5" = 5
        entryOf "8" = 8
        exitOf "1" = 4
        exitOf "5" = 7
        exitOf "8" = 9
        tcfg = mkGraph (genLNodes 1 9)  $
                       [(1,2,nop),(2,4,true),(2,3,false),(3,5,spawn),(3,2,nop)]
                   ++  [(5,6,nop),(6,8,spawn),(6,7,nop)]
                   ++  [(8,9,nop)]


{-
  if (H==0) {
    spawn {
      while (true) {skip;}
    }
  }
  skip     // c
  spawn {
    L=0    // n
  }
  spawn {
    L=1    // n'
  }
-}
joachim2 :: Program Gr
joachim2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                         `Seq` -- Notwendig, da sonst die Controlabhängigkeit vom Start-Knoten zu viel tainted.
           ReadFromChannel (Global "h") stdIn    `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (SpawnThread 4)
              (Skip)                    `Seq`
           Skip                         `Seq`
           SpawnThread 2                `Seq`
           SpawnThread 3
          ),
          (2, PrintToChannel (Val 0) stdOut),
          (3, PrintToChannel (Val 1) stdOut),
          (4, Skip                      `Seq`
              Skip                      `Seq`
              Skip
          )
         ]

{-
  if(H=0) {              || skip;  || skip;
    while (true) {skip}  || skip;  || skip;
  }                      || L=0;   || L=1;
-}
joachim3 :: Program Gr
joachim3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           SpawnThread 2                `Seq`
           SpawnThread 3                `Seq`
           ReadFromChannel (Global "h") stdIn    `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)
          ),
          (2,
           Skip                         `Seq`
           Skip                         `Seq`
           Ass (Global "l") (Val 0)
          ),
          (3,
           Skip                         `Seq`
           Skip                         `Seq`
           Ass (Global "l") (Val 1)
          )
         ]


noFlow :: Program Gr
noFlow = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel (Global "h") stdIn     `Seq`
           Ass             (Global "x") (Val 42)  `Seq`
           PrintToChannel  (Var (Global "x")) stdOut
          )
         ]

directFlow :: Program Gr
directFlow = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel (Global "h") stdIn     `Seq`
           PrintToChannel  (Var (Global "h"))  stdOut
          )
         ]

directFlowThread :: Program Gr
directFlowThread = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel (Global "h") stdIn     `Seq`
           Ass (Global "x") (Var (Global "h"))             `Seq`
           SpawnThread 2
          ),
          (2,
           PrintToChannel (Var (Global "x")) stdOut
          )
         ]


noDirectFlowThread :: Program Gr
noDirectFlowThread = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Ass (Global "h") (Val 0)               `Seq`
           Ass (Global "x") (Var (Global "h"))             `Seq`
           ReadFromChannel (Global "h") stdIn     `Seq`
           SpawnThread 2
          ),
          (2,
           PrintToChannel (Var (Global "x")) stdOut
          )
         ]


indirectFlow :: Program Gr
indirectFlow = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel (Global "h") stdIn     `Seq`
           Ass (Global "x") (Val 42)              `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Ass (Global "x") (Val 17))
              (Skip)                     `Seq`
           PrintToChannel (Var (Global "x")) stdOut
          )
         ]


orderConflict :: Program Gr
orderConflict = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           SpawnThread 2                 `Seq`
           ReadFromChannel (Global "h") stdIn     `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip)
              (Skip)                     `Seq`
           PrintToChannel (Val 17) stdOut
          ),
          (2,
           PrintToChannel (Val 42) stdOut
          )
         ]


-- Intuitiv sollte dieses Programm eigentlich sicher sein,
-- da man wohl nicht annehmen sollte, dass bei einer Output-Anweisung sichtbar ist, welche variable ausgelesen wird.
-- In unserm modell ist das aber so!
dubiousOrderConflict :: Program Gr
dubiousOrderConflict = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Ass (Global "x") (Val 42)              `Seq`
           Ass (Global "y") (Val 42)              `Seq`
           SpawnThread 2                 `Seq`
           ReadFromChannel (Global "h") stdIn     `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip)
              (Skip)                     `Seq`
           PrintToChannel (Var (Global "x")) stdOut
          ),
          (2,
           PrintToChannel (Var (Global "y")) stdOut
          )
         ]


cdomIsBroken :: Program Gr
cdomIsBroken = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           Ass (Global "x") (Val 42)                                                 `Seq`
           SpawnThread 2                                                    `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           Ass (Global "x") (Val 17)                                                 `Seq`
           SpawnThread 2
          ),
          (2,
           Skip                                                             `Seq`
           PrintToChannel (Var (Global "x")) stdOut
          )
         ]


{-
cdomIsBroken' ist PNI-unsicher (s.u).
cdomIsBroken' ist ein Beispiel für ein Programm, dass bei der "timingClassification"-Analyse fälschlicheweise als sicher akzeptiert wird,
wenn man cdomChef (statt: cdomMohrEtAl) verwendet.

> showCounterExamplesPniFor cdomIsBroken' defaultInput defaultInput'
i  = fromList [("stdIn",[1,2,1,2,1])] ...     i' = fromList [("stdIn",[-1,-2,-1,-2,-1])] ... 
-----------------
p  = 57 % 64 ≃ 0.89062                                  p' = 2015 % 2048 ≃ 0.98389
fromList []
---(17,PrintEvent 1 "stdOut")-->
fromList []
fromList []
---(18,PrintEvent 2 "stdOut")-->
fromList []
fromList []
---(17,PrintEvent 1 "stdOut")-->
fromList []
fromList []
---(18,PrintEvent 2 "stdOut")-->
fromList []
-----------------
p  = 7 % 64 ≃ 0.10938                                  p' = 33 % 2048 ≃ 0.01611
fromList []
---(17,PrintEvent 1 "stdOut")-->
fromList []
fromList []
---(17,PrintEvent 1 "stdOut")-->
fromList []
fromList []
---(18,PrintEvent 2 "stdOut")-->
fromList []
fromList []
---(18,PrintEvent 2 "stdOut")-->
fromList []
-}
cdomIsBroken' :: Program Gr
cdomIsBroken' = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           SpawnThread 2                                                    `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           SpawnThread 2
          ),
          (2,
           Skip                                                             `Seq`
           PrintToChannel (Val 1) stdOut                                    `Seq`
           PrintToChannel (Val 2) stdOut
          )
         ]



cdomIsBroken2 :: Program Gr
cdomIsBroken2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           ForC 2 (
              If (Leq (Var (Global "h")) (Val 0))
                (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
                (Skip)                                                      `Seq`
              PrintToChannel (Val 42) stdOut                                `Seq`
              SpawnThread 2
           )
          ),
          (2,
           Skip                                                             `Seq`
           PrintToChannel (Val 17) stdOut
          )
         ]

-- from: Noninterfering Schedulers, Andrei Popescu, Johannes Hölzl, and Tobias Nipkow
-- http://dx.doi.org/10.1007/978-3-642-40206-7_18
noninterferingSchedulers :: Program Gr
noninterferingSchedulers = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           ForC 2 (
              ReadFromChannel (Global "l1") lowIn1                                   `Seq`
              ReadFromChannel (Global "l2") lowIn2                                   `Seq`
              SpawnThread 42                                                `Seq`
              SpawnThread 11                                                `Seq`
              SpawnThread 12
           )
          ),
          (42,
           Skip                                                             `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           Ass (Global "h") (Var (Global "h") `Plus` Var (Global "l1") )
          ),
          (11,
           Skip                                                             `Seq`
           Ass (Global "l") (Var (Global "l1"))                                               `Seq`
           PrintToChannel (Var (Global "l")) stdOut
          ),
          (12,
           Skip                                                             `Seq`
           Ass (Global "l") (Var (Global "l2"))                                               `Seq`
           PrintToChannel (Var (Global "l")) stdOut
          )
         ]



timingVsFSI3 :: Program Gr
timingVsFSI3 = code2Program timingVsFSI3Code

timingVsFSI3For :: ForProgram
timingVsFSI3For = code2ForProgram timingVsFSI3Code
  
timingVsFSI3Code = code where
         code = Map.fromList $ [
           (1, Skip                                         `Seq`   -- remove this line to obtain a program that is FSI-Secure, but which timingAnalysis cannot determine!
               ReadFromChannel (Global "a") "stdIn"                  `Seq`
               SpawnThread 2
           ),
           (2, ReadFromChannel (Global "x") "lowIn1"                 `Seq`
               Ass (Global "a") (Times (Var (Global "x")) (Var (Global "a")))
           )
          ]




timingDependenceExample:: Program Gr
timingDependenceExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
           (1, Skip                                         `Seq`
               Ass (Global "x") (Val 0) `Seq`
               ReadFromChannel (Global "h") "stdIn"                  `Seq`
               SpawnThread 2                                `Seq`
               ForV (Global "h") (Ass (Global "x") (Val 42))                  `Seq`
               PrintToChannel (Var (Global "x")) stdOut
           ),
           (2, ReadFromChannel (Global "x") "lowIn1"                 `Seq`
               ForC 5 Skip                                  `Seq`
               Ass (Global "x") (Val 17)
           )
          ]


code2Program :: Map Integer For -> Program Gr
code2Program code = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram (Map.fromList [ (thread, show thread) | thread <- Map.keys code]) (Map.fromList [(show thread, for) | (thread, for) <- Map.assocs code])

code2ForProgram :: Map Integer For -> ForProgram
code2ForProgram code = ForProgram {
    code = code,
    channelTyping = defaultChannelObservability,
    mainThreadFor = 1
  }


code2ResumptionForProgram :: Map Integer For -> Maybe Res.ForProgram
code2ResumptionForProgram code = do
  code' <- Res.for2ResumptionFor code 1
  return $ Res.ForProgram {
    Res.code = code',
    Res.channelTyping = defaultChannelObservability
  }



timingAtUsesVsResumptionBasedBugInTranslationExample2 = code2Program timingAtUsesVsResumptionBasedBugInTranslationExample2Code
timingAtUsesVsResumptionBasedBugInTranslationExample2Code = code where
        code = Map.fromList $ [
          (1,(ForC 2
                 (Seq
                 (Seq
                 (Seq (SpawnThread 2)
                      (PrintToChannel (Val (-1)) "stdOut"))
                      (ForC 2
                          (Ass (Global "x") (Val 1))
                      ))
                      (ForV (Global "x")
                          (Seq (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x"))))
                               Skip))
                      ))),
          (2, Skip `Seq` 
             (ForC 2
                 (ForC 1
                     (Seq (ForC 1
                              (PrintToChannel (Val 17) "stdOut"))
                     (Seq (ReadFromChannel (Global "x") "stdIn")
                          Skip)))
                 )
              )
         ]

timingAtUsesVsResumptionBasedBugInTranslationExample1 = code2Program timingAtUsesVsResumptionBasedBugInTranslationExample1Code
timingAtUsesVsResumptionBasedBugInTranslationExample1Code = code where
        code = Map.fromList $ [
          (1, Skip `Seq`
              (Seq
              (Seq
              (Seq
              (Seq (Ass (Global "x") (Val 1))
                   (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))
                   (ForV (Global "x") (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "x"))))))
                   (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x"))))
                       (Seq Skip
                            (ReadFromChannel (Global "x") "lowIn1"))
                   {- else -}
                       (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x"))))
                             (SpawnThread 2)
                             (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))))
                   (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x"))))
                       (Seq (ForC 1 Skip)
                            (ForC 1 (SpawnThread 3)))
                   {- else -}
                       (ForC 1
                           (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x"))))
                               (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")
                               (ReadFromChannel (Global "b") "lowIn1")))))),
          (2, Skip `Seq`
              (ForV (Global "x")
                  (Seq
                  (Seq
                  (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")
                       (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))
                  (Seq (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x"))))
                       (PrintToChannel (Times (Var (Global "c")) (Var (Global "x"))) "stdOut")))
                  (Seq (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "x"))))
                           (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c"))))
                           Skip)
                  (Seq Skip
                       (ReadFromChannel (Global "y") "lowIn1")))))),
          (3, Skip `Seq`
              (Seq (ForV (Global "x")
                       (Seq
                       (Seq (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x"))))
                            (ReadFromChannel (Global "c") "lowIn1"))
                            (ForC 1 (PrintToChannel (Times (Var (Global "c")) (Var (Global "z"))) "stdOut"))))
              (Seq
              (Seq
              (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")
                   (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))
                   (ForC 2
                       (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "b"))))))
              (Seq (ForV (Global "x")
                       (ReadFromChannel (Global "z") "stdIn"))
              (Seq (ReadFromChannel (Global "c") "stdIn")
                   (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))))))
         ]



simpleExample1Code = code where
        code = Map.fromList $ [
          (1,
           ReadFromChannel (Global "y") "stdIn"                                      `Seq`
           ReadFromChannel (Global "a") "stdIn"                                      `Seq`
           ForV (Global "a")
             (ReadFromChannel (Global "b") "lowIn1")
          )
         ]


figure1leftCode = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           If (Leq (Var (Global "h")) (Val 1234))
              (PrintToChannel (Val 0) stdOut)
              (Skip)                                                        `Seq`
           Ass (Global "l") (Var (Global "h"))                                                `Seq`
           PrintToChannel (Var (Global "l")) stdOut
          )
         ]


figure2midIrlsod16 = code2Program figure2midIrlsod16Code
  
figure2midIrlsod16Code = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "l") (Val 0)                                         `Seq`
           Ass (Global "h") (Val 0)                                         `Seq`
           SpawnThread 2                                                    `Seq`
           SpawnThread 3                                                    `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           -- PrintToChannel (Val 17) stdOut                                   `Seq`
           Ass (Global "l") (Val 42)                                        `Seq`
           ReadFromChannel (Global "h") stdIn                               `Seq`
           Skip
          ),
          (3,
           Skip                                                             `Seq`
           PrintToChannel (Var (Global "l")) stdOut                         `Seq`
           Ass (Global "l") (Var (Global "h"))                              `Seq`
           Skip
          )
         ]


figure1midIrlsod18 = code2Program figure1midIrlsod18Code
  
figure1midIrlsod18Code = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "l") (Val 0)                                         `Seq`
           Ass (Global "h") (Val 0)                                         `Seq`
           SpawnThread 2                                                    `Seq`
           SpawnThread 3                                                    `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           ReadFromChannel (Global "l") lowIn1                              `Seq`
           PrintToChannel  (Var (Global "l")) stdOut                        `Seq`
           Skip
          ),
          (3,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                               `Seq`
           Ass (Global "l") (Var (Global "h"))                              `Seq`
           Skip
          )
         ]



figureDissLSOD1 = code2Program figureDissLSOD1Code
figureDissLSOD1Code = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           SpawnThread 2                                                    `Seq`
           SpawnThread 3                                                    `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           PrintToChannel (Val 17) stdOut                                   
          ),
          (3,
           Skip                                                             `Seq`
           PrintToChannel (Val 42) stdOut                                   
          )
         ]


figureDissLSOD2 = code2Program figureDissLSOD2Code
figureDissLSOD2Code = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "l") lowIn1                              `Seq`
           SpawnThread 2                                                    `Seq`
           SpawnThread 3                                                    `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           If ((Var (Global "l") `Leq` (Val 1)))
             (Skip `Seq` Skip)
             (Skip)                                                         `Seq`
           PrintToChannel (Val 17) stdOut                                   
          ),
          (3,
           Skip                                                             `Seq`
           (Skip `Seq` Skip)                                                `Seq`
           PrintToChannel (Val 42) stdOut                                   
          )
         ]

figureDissLSOD2High = code2Program figureDissLSOD2HighCode
figureDissLSOD2HighCode = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "l") stdIn                               `Seq`
           SpawnThread 2                                                    `Seq`
           SpawnThread 3                                                    `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           If ((Val 1) `Leq` (Var (Global "l")))
             (Skip `Seq` Skip `Seq` Skip `Seq` Skip)
             (Skip)                                                         `Seq`
           PrintToChannel (Val 17) stdOut                                   
          ),
          (3,
           Skip                                                             `Seq`
           If ((Val 1) `Leq` (Var (Global "l")))
             (Skip)
             (Skip `Seq` Skip `Seq` Skip `Seq` Skip)                        `Seq`
           PrintToChannel (Val 42) stdOut                                   
          )
         ]




figure5left = code2Program figure5leftCode
  
figure5leftCode = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           SpawnThread 2                                                    `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           PrintToChannel (Val 17) stdOut
          )
         ]


figure5right = code2Program figure5rightCode

figure5rightCode = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           Ass (Global "tmp") (Val 0)                                                `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Ass (Global "tmp") (Val 8))
              (Skip)                                                        `Seq`
           SpawnThread 2                                                    `Seq`
           ForV (Global "tmp") (
             Skip
           )                                                                `Seq`
           Ass (Global "tmp2") (Val 0)                                               `Seq`
           SpawnThread 3                                                    `Seq`
           ForV (Global "tmp2") (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass (Global "tmp2") (Val 3)
          ),
          (3,
           PrintToChannel (Val 17) stdOut
          )
         ]



exampleD4 = code2Program exampleD4Code
exampleD4Code = code where
        code = Map.fromList $ [
          (1, ReadFromChannel (Global "h") stdIn                                     `Seq`
              If ((Var (Global "h")) `Leq` (Val 0))
                (Ass (Global "h") (Val 1)  `Seq` Ass (Global "h") (Val 2))
                (Ass (Global "h") (Val 3)                       )                    `Seq`
              Ass (Global "l") (Val 4)                                               `Seq`
              PrintToChannel (Var (Global "l")) stdOut
          )
         ]


{-
192575
1171150
i  = fromList [("lowIn1",[1,2,3,4,5]),("lowIn2",[1,2,3,4,5]),("stdIn",[1,2,1,2,1])] ...     i' = fromList [("lowIn1",[1,2,3,4,5]),("lowIn2",[1,2,3,4,5]),("stdIn",[-1,-2,-1,-2,-1])] ... 
-----------------
p  = 88570212217 % 1253826625536 ≃ 0.07064                                  p' = 3246863447557 % 164341563462254592 ≃ 0.00002
fromList []
---(21,PrintEvent 42 "stdOut")-->
fromList []
fromList []
---(4,PrintEvent 17 "stdOut")-->
fromList []
-----------------
p  = 1165256413319 % 1253826625536 ≃ 0.92936                                  p' = 164338316598807035 % 164341563462254592 ≃ 0.99998
fromList []
---(4,PrintEvent 17 "stdOut")-->
fromList []
fromList []
---(21,PrintEvent 42 "stdOut")-->
fromList []

real    5m31.213s
user    5m28.054s
sys     0m2.974s
-}
figure5right' :: Program Gr
figure5right' = p { observability = defaultObservabilityMap (tcfg p)  }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           Ass (Global "tmp") (Val 0)                                                `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Ass (Global "tmp") (Val 5))
              (Skip)                                                        `Seq`
           SpawnThread 2                                                    `Seq`
           ForV (Global "tmp") (
             Skip
           )                                                                `Seq`
           Ass (Global "tmp2") (Val 5)                                               `Seq`
           SpawnThread 3                                                    `Seq`
           ForV (Global "tmp2") (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass (Global "tmp2") (Val 0)
          ),
          (3,
           PrintToChannel (Val 17) stdOut
          )
         ]


figure5right'' :: Program Gr
figure5right'' = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           Ass (Global "tmp") (Val 0)                                                `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Ass (Global "tmp") (Val 10))
              (Skip)                                                        `Seq`
           SpawnThread 2                                                    `Seq`
           ForV (Global "tmp") (
             Skip
           )                                                                `Seq`
           Ass (Global "tmp2") (Val 0)                                               `Seq`
           SpawnThread 3                                                    `Seq`
           Ass (Global "loop2") (Var (Global "tmp2"))                                        `Seq`
           ForV (Global "loop2") (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass (Global "tmp2") (Val 3)
          ),
          (3,
           PrintToChannel (Val 17) stdOut
          )
         ]


ijisLSODistkaputt :: Program Gr
ijisLSODistkaputt = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           SpawnThread 2                                                    `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           Ass (Global "x") (Val 17)
          ),
          (2,
           Skip                                                             `Seq`
           Ass (Global "x") (Val 42)                                                 `Seq`
           PrintToChannel (Var (Global "x")) stdOut
          )
         ]

minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD ::  Program Gr
minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD = code2Program minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODCode

minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODCode = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "h") (Val 0)                                                  `Seq`
           SpawnThread 2                                                    `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           Ass (Global "h2") (Var (Global "h"))                                               `Seq`
           Ass (Global "x") (Val 42)                                                 `Seq`
           PrintToChannel (Var (Global "x")) stdOut
          )
         ]

minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODFor :: ForProgram
minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODFor = code2ForProgram minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODCode


minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD2 ::  Program Gr
minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           SpawnThread 2                                                    `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           PrintToChannel (Val 42) stdOut
          )
         ]


minimalClassificationIsLessPreciseThanSimonClassification ::  Program Gr
minimalClassificationIsLessPreciseThanSimonClassification = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           If (Leq (Val 0) (Val 1))                                         
               (ReadFromChannel (Global "h") stdIn)                                  
               (SpawnThread 2)                                                `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           PrintToChannel (Val 17) stdOut
          )
         ]



timingSecureButNotCombinedTimingSecure ::  Program Gr
timingSecureButNotCombinedTimingSecure = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           Ass (Global "tmp") (Val 0)                                                `Seq`
           If (Leq (Var (Global "h")) (Val 0))
              (Ass (Global "tmp") (Val 8))
              (Skip)                                                        `Seq`
           ForV (Global "tmp") (
             Skip
           )                                                                `Seq`
           SpawnThread 2                                                    `Seq`
           Ass (Global "tmp2") (Val 0)                                               `Seq`
           PrintToChannel (Var (Global "tmp2")) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass (Global "tmp2") (Val 3)
          )
         ]

timingSecureButNotCombinedTimingSecureGenerated :: Program Gr
timingSecureButNotCombinedTimingSecureGenerated = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList [(1,Seq (If CTrue (If CFalse (Seq Skip Skip) (Seq (ReadFromChannel (Global "x") "lowIn1") (Ass (Global "y") (Plus (Var (Global "x")) (Var (Global "x")))))) (Seq (Seq Skip (ReadFromChannel (Global "x") "stdIn")) (If (Leq (Val 0) (Plus (Var (Global "x")) (Var (Global "x")))) Skip (Ass (Global "a") (Plus (Var (Global "x")) (Var (Global "x"))))))) (Seq (If CTrue (If CFalse (PrintToChannel (Val 42) "stdOut") (ReadFromChannel (Global "c") "stdIn")) (ForC 1 (Ass (Global "z") (Val 1)))) (If CFalse (Seq (PrintToChannel (Val 17) "stdOut") Skip) (Seq (Ass (Global "z") (Val 0)) (SpawnThread 2))))),(2,ForV (Global "z") (Seq (ForC 2 (Seq Skip (PrintToChannel (Plus (Var (Global "z")) (Var (Global "z"))) "stdOut"))) (Seq (Seq (Ass (Global "c") (Plus (Var (Global "z")) (Var (Global "z")))) (ReadFromChannel (Global "y") "lowIn1")) (Seq Skip (PrintToChannel (Plus (Var (Global "z")) (Var (Global "y"))) "stdOut")))))]

someGeneratedProgram :: Program Gr
someGeneratedProgram = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList [(1,Seq (ForC 3 (If CTrue (Seq Skip Skip) (Seq (ReadFromChannel (Global "x") "stdIn") (ReadFromChannel (Global "y") "lowIn1")))) (Seq (ForC 2 (Seq (PrintToChannel (Val 1) "stdOut") (ReadFromChannel (Global "c") "lowIn1"))) (ForV (Global "c") (If (Leq (Val 0) (Plus (Var (Global "c")) (Var (Global "c")))) (SpawnThread 3) (ReadFromChannel (Global "y") "stdIn"))))),(3,ForV (Global "c") (If (Leq (Val 0) (Plus (Var (Global "c")) (Var (Global "c")))) (Seq (ForC 3 (ReadFromChannel (Global "b") "stdIn")) (If (Leq (Val 0) (Plus (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "x") "stdIn") (PrintToChannel (Plus (Var (Global "c")) (Var (Global "b"))) "stdOut"))) (Seq (Seq (PrintToChannel (Plus (Var (Global "c")) (Var (Global "c"))) "stdOut") (PrintToChannel (Plus (Var (Global "c")) (Var (Global "c"))) "stdOut")) (Seq (Ass (Global "a") (Plus (Var (Global "c")) (Var (Global "c")))) (Ass (Global "x") (Plus (Var (Global "a")) (Var (Global "a"))))))))]

-- this one generates *very* long (inifinitely so?!?!) executions with defaultInput'
anotherGeneratedProgram :: Program Gr
anotherGeneratedProgram = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        -- code = Map.fromList [(1,Seq (Seq (ForC 2 (ForC 2 (PrintToChannel (Val 1) "stdOut"))) (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (ReadFromChannel (Global "a") "lowIn1")) (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut")))) (ForC 1 (Seq (Seq (ReadFromChannel (Global "x") "stdIn") (SpawnThread 3)) (ForV (Global "a") (ReadFromChannel (Global "c") "lowIn1"))))),(2,Seq (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "x")))) (ForV (Global "x") (ReadFromChannel (Global "z") "lowIn1")) (ForC 2 (ReadFromChannel (Global "a") "stdIn"))) (Seq (Seq (ReadFromChannel (Global "a") "lowIn1") Skip) (ForV (Global "x") (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "a"))))))) (Seq (Seq (ForV (Global "a") Skip) (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "a"))) "stdOut"))) (ForC 2 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "x") (Times (Var (Global "a")) (Var (Global "x")))) (ReadFromChannel (Global "z") "lowIn1"))))),(3,ForV (Global "a") (ForC 1 (Seq (ForV (Global "x") (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "a")))) (SpawnThread 2) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")))))]
        code = Map.fromList [
          (1,Seq (Seq (ForC 2
                            (ForC 2
                                  (PrintToChannel (Val 1) "stdOut")))
            (Seq (Seq (ReadFromChannel (Global "a") "stdIn")
                      (ReadFromChannel (Global "a") "lowIn1"))
                 (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut")
                      (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))))
                      (ForC 1
                  (Seq (Seq (ReadFromChannel (Global "x") "stdIn")
                            (SpawnThread 3))
                            (ForV (Global "a")
                                  (ReadFromChannel (Global "c") "lowIn1"))))),
          (2,Seq (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "x"))))
                          (ForV (Global "x") (ReadFromChannel (Global "z") "lowIn1"))
                          (ForC 2 (ReadFromChannel (Global "a") "stdIn")))
            (Seq (Seq (ReadFromChannel (Global "a") "lowIn1")
                       Skip)
                      (ForV (Global "x")
                            (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "a")))))))
            (Seq (Seq (ForV (Global "a") Skip)
                 (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")
                      (PrintToChannel (Times (Var (Global "x")) (Var (Global "a"))) "stdOut")))
                      (ForC 2 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x"))))
                                  (Ass (Global "x") (Times (Var (Global "a")) (Var (Global "x"))))
                                  (ReadFromChannel (Global "z") "lowIn1"))))),
          (3,         ForV (Global "a")
                           (ForC 1
                            (Seq (ForV (Global "x")
                                       (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "x")))))
                                 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "a"))))
                                     (SpawnThread 2)
                                     (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")))))]


-- this one appears to be secure, but cannot be proven so
aSecureGeneratedProgram :: Program Gr
aSecureGeneratedProgram = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList [(1,ForC 1 (If CTrue (Seq (SpawnThread 3) (SpawnThread 2)) (Seq (PrintToChannel (Val 42) "stdOut") (Ass (Global "z") (Val 1))))),(2,Seq (Seq (ForC 2 (PrintToChannel (Val 0) "stdOut")) (Seq (ReadFromChannel (Global "a") "lowIn1") Skip)) (Seq (Seq Skip Skip) (ForV (Global "a") (ReadFromChannel (Global "y") "lowIn1")))),(3,If CFalse (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (ReadFromChannel (Global "b") "stdIn")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) Skip Skip)) (If CFalse (If CFalse (ReadFromChannel (Global "c") "stdIn") (Ass (Global "y") (Val 0))) (If CFalse (Ass (Global "a") (Val (-1))) (ReadFromChannel (Global "y") "lowIn1"))))]



idomIsTreeProgramIdomBischofExample :: Program Gr
idomIsTreeProgramIdomBischofExample = toProgram generated
  where generated = GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (Ass (Global "c") (Val 1)) (CallProcedure "foo")) undefined undefined undefined),("baz",Generated (ForC 1 (ForC 1 (CallProcedure "bar"))) undefined undefined undefined),("foo",Generated (Seq (PrintToChannel (Val 4) "stdOut") (PrintToChannel (Val (-1)) "stdOut")) undefined undefined undefined),("main",Generated (Seq (If CTrue (Seq (CallProcedure "foo") (SpawnThread 2)) (Seq (CallProcedure "foo") (Ass (Global "c") (Val 0)))) (If CTrue (Seq (Ass (Global "y") (Val 0)) Skip) (Seq (Ass (Global "b") (Val 0)) (ReadFromChannel (Global "b") "stdIn")))) undefined undefined undefined),("thread2",Generated (If CTrue (ForC 1 (Seq (Seq (CallProcedure "baz") (PrintToChannel (Val 9) "stdOut")) (Seq (ReadFromChannel (Global "x") "stdIn") (ReadFromChannel (Global "y") "lowIn1")))) (Seq (If CFalse (ReadFromChannel (Global "a") "lowIn1") (PrintToChannel (Val 0) "stdOut")) (Seq (ReadFromChannel (Global "x") "lowIn1") (SpawnThread 3)))) undefined undefined undefined),("thread3",Generated (Seq (Seq Skip (PrintToChannel (Neg (Var (Global "x"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ReadFromChannel (Global "c") "lowIn1") (CallProcedure "foo"))) undefined undefined undefined)])


clientServerKeyExampleSimple ::  Program Gr
clientServerKeyExampleSimple = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (setup,
           Skip                                                             `Seq`
           Ass (Global "privKey") (Val 42)                                           `Seq`
           SpawnThread server                                               `Seq`
           ForC 3 (
             ReadFromChannel (Global "msg") "stdIn"                                  `Seq`
             SpawnThread client
           )
          ),
          (server,
           Skip
          ),
          (client,
           Skip                                                             `Seq`
           Ass (Global "msg_enc") (Val 0)                                            `Seq`  -- not (Var (Global "msg")) `Plus` (Var (Global "privKey"))), since we do not declassify or anything here
           PrintToChannel (Var (Global "msg_enc")) "stdOut"
          )
         ]
        setup  = 1
        server = 2
        client = 3


clientServerKeyExample ::  Program Gr
clientServerKeyExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (setup,
           Skip                                                             `Seq`
           Ass (Global "privKey") (Val 7)                                            `Seq`
           ReadFromChannel (Global "privKeyRndSeed") "stdIn"                         `Seq`
           ForV (Global "privKeyRndSeed") (
             Ass (Global "privKey") ((Var (Global "privKey")) `Plus` (Val 3))
           )                                                                `Seq`  -- "initialization of the private key ... and [its] runtime may depend on HIGH information."
           SpawnThread server                                               `Seq`
           ForC 3 (
             ReadFromChannel (Global "msg") "stdIn"                                  `Seq`
             SpawnThread client
           )
          ),
          (server,
           Skip
          ),
          (client,
           Skip                                                             `Seq`
           ForV (Global "privKey") (
             Skip
           )                                                                `Seq`  -- "encryption .. happen before the send operation and [its] runtime may depend on HIGH information."
           Ass (Global "msg_enc") (Val 0)                                            `Seq`  -- "due to ideal encryption no explicit and implicit information flow occurs between the secret message and its encryption.
           PrintToChannel (Var (Global "msg_enc")) "stdOut"
          )
         ]
        setup  = 1
        server = 2
        client = 3


clientSetupKeyExample ::  Program Gr
clientSetupKeyExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (setup,
           Skip                                                             `Seq`
           ReadFromChannel (Global "secretBit") "stdIn"                              `Seq`
           Ass (Global "privKey") (Val 0)                                         `Seq`
           ReadFromChannel (Global "privKeyRndSeed") "stdIn"                         `Seq`  --
           ForV (Global "privKeyRndSeed") (
             Ass (Global "privKey") ((Var (Global "privKey")) `Plus` (Val 3))
           )                                                                `Seq`  -- "initialization of the private key ... and [its] runtime may depend on HIGH information."
           SpawnThread server                                               `Seq`
           ForC 3 (
             ReadFromChannel (Global "msg1") "lowIn1"                                 `Seq`
             ReadFromChannel (Global "msg2") "lowIn2"                                 `Seq`
             If ((Var (Global "secretBit")) `Leq` (Val 0))
                 (Ass (Global "msg") (Var (Global "msg1")))
                 (Ass (Global "msg") (Var (Global "msg2")))                                   `Seq`
             SpawnThread client
           )
          ),
          (server,
           Skip
          ),
          (client,
           Skip                                                             `Seq`
           ForV (Global "privKey") (
             Skip
           )                                                                `Seq`  -- "encryption .. happen before the send operation and [its] runtime may depend on HIGH information."
           Ass (Global "msg_enc") (Val 0)                                            `Seq`  -- "due to ideal encryption no explicit and implicit information flow occurs between the secret message and its encryption.
           PrintToChannel (Var (Global "msg_enc")) "stdOut"
          )
         ]
        setup  = 1
        server = 2
        client = 3

singleThreadedDelay :: Program Gr
singleThreadedDelay = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           PrintToChannel (Val 42) "stdOut"                                 `Seq`
           ReadFromChannel (Global "h") "stdIn"                                      `Seq`
           ForV (Global "h") (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 17) "stdOut"
          )
         ]


-- similiar to http://dx.doi.org/10.1109/csf.2012.15
environmentTotalAssumption1 :: Program Gr
environmentTotalAssumption1 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ForC 100 (
              ReadFromChannel (Global "h") stdIn                                     `Seq`
              PrintToChannel (Val 42) stdOut
           )
          )
         ]
environmentTotalAssumption2 :: Program Gr
environmentTotalAssumption2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel (Global "h") stdIn                                        `Seq`
           Ass (Global "bit") (Val 1)                                                `Seq`
           ForC 16 (
              If (Leq ((Var (Global "h")) `Times` (Var (Global "bit"))) (Val 0))
                (PrintToChannel (Val 1) highOut1)
                (PrintToChannel (Val 1) highOut2)
           )
          )
         ]

simple :: Program Gr
simple = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "a") (Val 42)                                        `Seq`
           Ass (Global "x") (Var (Global "a"))                                                `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Ass (Global "z") (Val 1))
              (Ass (Global "z") (Val 0))
          )
         ]
simple2 :: Program Gr
simple2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "a") (Val 42)                                        `Seq`
           Ass (Global "x") (Var (Global "a"))                                                `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Skip)
              (Skip)                                                        `Seq`
           Ass (Global "z") (Val 0)
          )

         ]

simple3 :: Program Gr
simple3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "z") (Val 42)                                        `Seq`
           Ass (Global "a") (Val 17)                                        `Seq`
           Ass (Global "tmp") ((Var (Global "z")) `Plus` (Val 1))                             `Seq`
           Ass (Global "x") (Var (Global "a"))                                                `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Skip)
              (Skip)                                                        `Seq`
           Ass (Global "z") (Var (Global "tmp"))
          )

         ]

simple4 :: Program Gr
simple4 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "a") (Val 42)                                        `Seq`
           Ass (Global "b") (Var (Global "a"))                                                `Seq`
           Ass (Global "c") (Var (Global "a"))                                                `Seq`
           Ass (Global "d") (Var (Global "a"))                                                `Seq`
           Ass (Global "x") (Var (Global "a"))                                                `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Ass (Global "x") (Var (Global "b")))
              (Ass (Global "x") (Var (Global "d")))                                           `Seq`
           Ass (Global "z") (Val 0)                                                           `Seq`
           Ass (Global "a") (Val 42)                                                          `Seq`
           If (Leq (Var (Global "a")) (Val 0))
              (Skip)
              (Skip)                                                                          `Seq`
           Ass (Global "c") (Val 42)
          )

         ]

simple4' :: Program Gr
simple4' = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "a") (Val 42)                                        `Seq`
           Ass (Global "b") (Var (Global "a"))                                                `Seq`
           Ass (Global "c") (Var (Global "a"))                                                `Seq`
           Ass (Global "d") (Var (Global "a"))                                                `Seq`
           Ass (Global "x") (Var (Global "a"))                                                `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Ass (Global "x") (Var (Global "b")))
              (Ass (Global "x") (Var (Global "d")))                                           `Seq`
           Ass (Global "z") (Val 0)                                                           `Seq`
           Ass (Global "a") (Val 42)                                                          `Seq`
           If (Leq (Var (Global "b")) (Val 0))
              (Skip)
              (Skip)                                                                          `Seq`
           Ass (Global "c") (Val 42)
          )

         ]

simple4'2 :: Program Gr
simple4'2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                            `Seq`
           Ass (Global "a") (Val 1)                                        `Seq`
           Ass (Global "b") (Val 2)                                        `Seq`
           Ass (Global "c") (Val 3)                                        `Seq`
           Ass (Global "d") (Val 4)                                        `Seq`
           Ass (Global "x") (Val 24)                                       `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Ass (Global "y") (Var (Global "b")))
              (Ass (Global "y") (Var (Global "d")))                                           `Seq`
           Ass (Register 0) (Var (Global "a"))                                                `Seq`
           Ass (Register 1) (Var (Global "b"))                                                `Seq`
           Skip
          )

         ]




simple4'' :: Program Gr
simple4'' = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "a") (Val 42)                                        `Seq`
           Ass (Global "b") (Var (Global "a"))                                                `Seq`
           Ass (Global "d") (Var (Global "a"))                                                `Seq`
           Ass (Global "c") (Var (Global "a"))                                                `Seq`
           Ass (Global "x") (Var (Global "a"))                                                `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Ass (Global "x") (Var (Global "b")))
              (Ass (Global "x") (Var (Global "d")))                                           `Seq`
           Ass (Global "a") (Val 42)                                                          `Seq`
           If (Leq (Var (Global "b")) (Val 0))
              (Skip)
              (Skip)                                                                          `Seq`
           If (Leq (Var (Global "d")) (Val 0))
              (Skip)
              (Skip)                                                                          `Seq`
           Ass (Global "c") (Val 42)
          )

         ]



simple4''2 :: Program Gr
simple4''2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Ass (Global "a") (Val 1)                                        `Seq`
           Ass (Global "b") (Val 2)                                        `Seq`
           Ass (Global "c") (Val 3)                                        `Seq`
           Ass (Global "d") (Val 4)                                        `Seq`
           Ass (Global "x") (Val 24)                                       `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Ass (Global "y") (Var (Global "b") `Plus` (Var (Global "c"))))
              (Ass (Global "y") (Var (Global "d") `Plus` (Var (Global "d"))))                 `Seq`
           -- Ass (Register 0) (Var (Global "a"))                                                `Seq`
           Ass (Register 1) (Var (Global "b"))                                                `Seq`
           Ass (Register 2) (Var (Global "y"))                                                `Seq`
           If (Leq (Var (Register 2)) (Val 3))
              (Ass (Register 3) (Var (Global "a")))
              (Ass (Register 3) (Var (Global "b")))                                           `Seq`
           Ass (Register 4) (Var (Global "c"))               
          )

         ]

simple4''3 :: Program Gr
simple4''3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Ass (Global "a") (Val 1)                                        `Seq`
           Ass (Global "b") (Val 2)                                        `Seq`
           Ass (Global "c") (Val 3)                                        `Seq`
           Ass (Global "d") (Val 4)                                        `Seq`
           Ass (Global "x") (Val 24)                                       `Seq`
           If (Leq (Var (Global "x")) (Val 0))
              (Ass (Global "y") (Var (Global "b") `Plus` (Var (Global "c"))))
              (Ass (Global "y") (Var (Global "d")))                                           `Seq`
           -- Ass (Register 0) (Var (Global "a"))                                                `Seq`
           Ass (Register 1) (Var (Global "b"))                                                `Seq`
           Ass (Register 2) (Var (Global "y"))                                                `Seq`
           If (Leq (Var (Register 2)) (Val 3))
              (Ass (Register 3) (Var (Global "a")))
              (Ass (Register 3) (Var (Global "b")))                                           `Seq`
           Ass (Register 5) (Var (Global "e"))               `Seq`
           Ass (Register 6) (Var (Global "f"))               `Seq`
           Ass (Register 7) (Var (Global "g"))               `Seq`
           Ass (Register 4) (Var (Global "c"))               
          )

         ]





twoLoops :: Program Gr
twoLoops = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ForC 5 Skip                                                      `Seq`
           ForC 5 Skip                                                      `Seq`
           Ass (Global "z") (Var (Global "tmp"))
          )

         ]


twoLoopsWithAss :: Program Gr
twoLoopsWithAss = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ForC 5 (Ass (Global "x") (Val 42))                               `Seq`
           ForV (Global "x") Skip                                           `Seq`
           Skip
          )

         ]


{-    1
      2<---
      |   |
      |   6
      |   ^
      |   |
      3----
      |
      8<---
      |   |
      |   7
      |   ^
      |   |
      4---|
      |
      5
-}
twoLoops' :: Program Gr
twoLoops' = Program {
    tcfg = tcfg,
    procedureOf = show,
    staticProcedureOf = staticProcedureOf,
    staticThreads  = Set.fromList [1],
    staticProcedures  = Set.fromList ["1"],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticProcedureOf n 
         | n ∊ [1..8] = "1"
         | otherwise = error "uknown node"
        entryOf "1" = 1
        exitOf "1" = 5
        tcfg = mkGraph (genLNodes 1 8) $
                        [(1,2,NoOp), (2,3,NoOp), (3,8,Guard True CTrue), (8,4,NoOp), (4,5, Guard True CTrue)]
                    ++  [(3,6,Guard False CTrue), (6,2, NoOp), (4,7,Guard False CTrue), (7,8,NoOp)]

forIf :: Program Gr
forIf = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass (Global "x") (Val 42)                                                 `Seq`
           ForC 5 (
              If (Leq (Var (Global "x")) (Val 0)) Skip Skip
           )                                                                `Seq`
           Skip
          )
         ]


minimalClassificationVstimingClassificationDomPathsCounterExampleSimon:: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExampleSimon = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel (Global "h") "stdIn"   `Seq`
           SpawnThread 2                 `Seq`
           ForV (Global "h") (Ass (Global "h") ((Var (Global "h")) `Plus` (Val (-1)))) `Seq`
           PrintToChannel (Val 42) "stdOut"
          ),
          (2, Skip
          )
          ]


minimalClassificationVstimingClassificationDomPathsCounterExampleMartin:: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExampleMartin = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel (Global "h") "stdIn"   `Seq`
           SpawnThread 2                 `Seq`
           Ass (Global "h2") (Var (Global "h"))            `Seq`
           PrintToChannel (Val 42) "stdOut"
          ),
          (2, Skip                       `Seq`
              PrintToChannel (Val 17) "stdOut"
          )
          ]



minimalClassificationVstimingClassificationDomPathsCounterExample :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           ForC 2 (
               If CTrue
                  (SpawnThread 3)
                  (SpawnThread 2)
               )
          ),
          (2, Skip `Seq`
              ForC 2 (
                     (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z"))))
                         Skip
                         (ReadFromChannel (Global "z") "stdIn"))
             )
          ),
          (3, Skip `Seq`
              ReadFromChannel (Global "z") "lowIn1"
          )
          ]


minimalClassificationVstimingClassificationDomPathsCounterExample2 :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (Seq (Seq (If CFalse (Seq (SpawnThread 3) (PrintToChannel (Val 1) "stdOut")) (If CFalse (ReadFromChannel (Global "c") "lowIn1") (SpawnThread 2))) (If CFalse (If CTrue (Ass (Global "a") (Val (-1))) (Ass (Global "y") (Val 17))) (ForC 1 (PrintToChannel (Val 42) "stdOut")))) (ForC 1 (Seq (If CFalse (ReadFromChannel (Global "c") "lowIn1") (ReadFromChannel (Global "b") "lowIn1")) (If CFalse (ReadFromChannel (Global "x") "lowIn1") (Ass (Global "z") (Val 0)))))) ),
          (2, (Seq (Seq (Seq (ForC 1 (Ass (Global "y") (Val (-1)))) (Seq (ReadFromChannel (Global "b") "lowIn1") (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) Skip (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "b"))))) (Seq (ReadFromChannel (Global "x") "stdIn") (ReadFromChannel (Global "b") "stdIn")))) (ForV (Global "x") (ForV (Global "b") (Seq (Ass (Global "x") ((Var (Global "x")) `Plus` (Val (-1)))) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "x")))) (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "b")))) (ReadFromChannel (Global "a") "stdIn")))))) ),
          (3,(ForC 2 (Seq (Seq (Seq (PrintToChannel (Val 17) "stdOut") (Ass (Global "b") (Val 42))) (ForC 2 (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))) (Seq (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut") (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut")) (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))))))))
          ]



minimalClassificationVstimingClassificationDomPathsCounterExample2Essential :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample2Essential = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, Skip                             `Seq`
              Ass (Global "x") (Val 1)                  `Seq`
              If CTrue
                (SpawnThread 2)
                (SpawnThread 3)                `Seq`
              ReadFromChannel (Global "x") "lowIn1"
          ),
          (2, Skip                             `Seq`
              ReadFromChannel (Global "h") "stdIn"      `Seq`
              If (Leq (Var (Global "h")) (Val 0))
                 (Skip `Seq` Skip)
                 (Skip)                        `Seq`
              Ass (Global "x") (Val 42)
          ),
          (3, Skip                             `Seq`
              PrintToChannel (Var (Global "x")) "stdOut"
          )
          ]


-- counter example 3 and 4 are essential the same as minimalClassificationVstimingClassificationDomPathsCounterExampleEssential
minimalClassificationVstimingClassificationDomPathsCounterExample3 :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(Seq (Seq (ForC 2 (Seq (SpawnThread 3) (SpawnThread 2))) (Seq (If CTrue (ReadFromChannel (Global "z") "lowIn1") (PrintToChannel (Val (-1)) "stdOut")) (ForC 1 (Ass (Global "x") (Val 1))))) (ForC 2 (Seq (ForC 1 Skip) (Seq (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "x") "lowIn1")))))),
         (2,(Seq (Seq (Seq (Seq Skip (ReadFromChannel (Global "x") "lowIn1")) (ForV (Global "x") Skip)) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (ForC 2 (ReadFromChannel (Global "x") "lowIn1")))) (ForV (Global "x") (Seq (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (ReadFromChannel (Global "z") "lowIn1")) (Seq (ReadFromChannel (Global "z") "lowIn1") (PrintToChannel (Times (Var (Global "x")) (Var (Global "z"))) "stdOut")))))),
         (3,(Seq (Seq (Seq (Seq (Ass (Global "b") (Val 17)) (ReadFromChannel (Global "b") "lowIn1")) (ForC 2 (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))))) (Seq (Seq (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "y")))) (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))) (ForC 1 (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))))) (ForC 1 (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (ReadFromChannel (Global "c") "stdIn")) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "b") "stdIn") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "c")))))))))
         ]

minimalClassificationVstimingClassificationDomPathsCounterExample4 :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample4 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(If CFalse (ForC 2 (Seq (Seq Skip (ReadFromChannel (Global "b") "lowIn1")) (ForC 2 (SpawnThread 2)))) (If CFalse (Seq (Seq (SpawnThread 3) (ReadFromChannel (Global "z") "lowIn1")) (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "y") "lowIn1"))) (If CFalse (Seq (Ass (Global "a") (Val 1)) (ReadFromChannel (Global "x") "lowIn1")) (Seq (PrintToChannel (Val 17) "stdOut") (ReadFromChannel (Global "a") "stdIn"))))) ),
          (2,(ForV (Global "b") (Seq (Ass (Global "b") ((Var (Global "b")) `Plus` (Val (-1)))) (Seq (ForC 2 (Seq (ReadFromChannel (Global "a") "stdIn") (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "a")))))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "b")))) (ForC 1 (ReadFromChannel (Global "y") "stdIn")) (Seq Skip (Ass (Global "x") (Times (Var (Global "b")) (Var (Global "c"))))))))) ),
          (3,(ForC 2 (If CFalse (Seq (Seq Skip (PrintToChannel (Val 1) "stdOut")) (Seq Skip Skip)) (Seq (Seq Skip (PrintToChannel (Val (-1)) "stdOut")) (Seq (ReadFromChannel (Global "c") "lowIn1") (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "c")))))))))
         ]


minimalClassificationVstimingClassificationDomPathsCounterExampleEssential :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExampleEssential = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, Skip                             `Seq`
              Ass (Global "x") (Val 0)                  `Seq`
              SpawnThread 2                    `Seq`
              ReadFromChannel (Global "h") "stdIn"      `Seq`
              If (Leq (Var (Global "h")) (Val 0))
                 (Skip `Seq` Skip)
                 (Skip)                        `Seq`
              Ass (Global "x") (Val 1)
          ),
          (2, Skip                             `Seq`
              ReadFromChannel (Global "x") "lowIn1"
          )
          ]


-- This was spurioulsy reported as a counterExample to allSound [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD ] in some test run: probably just bad luck in sampling executions ¯\__(ツ)__/¯
notReallyUnsound :: Program Gr
notReallyUnsound = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(Seq (Seq (Seq (Seq Skip (Ass (Global "z") (Val 0))) (ForV (Global "z") Skip)) (Seq (Seq (SpawnThread 2) (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (ReadFromChannel (Global "c") "lowIn1") (ReadFromChannel (Global "b") "stdIn")))) (Seq (ForC 2 (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut") Skip)) (ForC 2 (Seq (SpawnThread 3) Skip))))),
          (2,(Seq (ForC 2 (ForV (Global "z") (ForC 2 (Ass (Global "y") (Times (Var (Global "z")) (Var (Global "z"))))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (Seq (ForC 1 (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")) (ForC 2 (ReadFromChannel (Global "x") "lowIn1"))) (ForV (Global "z") (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (Ass (Global "x") (Times (Var (Global "z")) (Var (Global "z")))) (ReadFromChannel (Global "x") "lowIn1")))))),
          (3,(If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (ForV (Global "z") (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut") (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "z"))))) (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut") (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "z"))))))) (ForV (Global "z") (ForC 2 (Seq Skip (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "z")))))))))
         ]


-- similiar to notReallyUnsound
-- here, at least i could reproduce the empirical "leak" once, but only with marginally difference in probabilities. Most of the times, the difference in empirical probabilities is within the set threshold.
-- *Program.Tests> mainEquivAnnotatedSome
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[1,2,1,2,1])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,-2,-1,-2,-1])] ... 
-- -----------------
-- p  = 2011 % 7500 ≃ 0.26813                                  p' = 607 % 2500 ≃ 0.24280
-- fromList []
-- ---(36,PrintEvent 0 "stdOut")-->
-- fromList []
-- fromList []
-- ---(73,PrintEvent 1 "stdOut")-->
-- fromList []
-- fromList []
-- ---(85,PrintEvent 17 "stdOut")-->
-- fromList []
-- fromList []
-- ---(85,PrintEvent 17 "stdOut")-->
-- fromList []
notReallyUnsound2 :: Program Gr
notReallyUnsound2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(If CFalse (If CFalse (If CFalse (Seq (PrintToChannel (Val 42) "stdOut") Skip) (Seq (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val (-1)) "stdOut"))) (Seq (If CTrue (SpawnThread 2) (Ass (Global "x") (Val 0))) (ForC 1 (PrintToChannel (Val 17) "stdOut")))) (Seq (ForC 1 (If CFalse (PrintToChannel (Val 17) "stdOut") (SpawnThread 3))) (If CTrue (Seq Skip (PrintToChannel (Val 0) "stdOut")) (ForC 2 Skip))))),
          (2,(ForC 2 (Seq (If CFalse (If CFalse (Ass (Global "x") (Val 42)) (ReadFromChannel (Global "c") "stdIn")) (Seq Skip (PrintToChannel (Val 1) "stdOut"))) (Seq (Seq (Ass (Global "x") (Val 0)) (ReadFromChannel (Global "b") "lowIn1")) (ForC 2 (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "b"))))))))),
          (3,(Seq (If CFalse (If CFalse (Seq (Ass (Global "a") (Val 17)) Skip) (Seq (Ass (Global "z") (Val 17)) (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut"))) (ForC 1 (Seq (PrintToChannel (Val 1) "stdOut") Skip))) (If CFalse (Seq (Seq Skip Skip) (Seq (Ass (Global "c") (Val 42)) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut"))) (Seq (ForC 2 (PrintToChannel (Val 17) "stdOut")) (Seq (Ass (Global "y") (Val 0)) (ReadFromChannel (Global "y") "stdIn"))))))
          ]


-- see notReallyUnsound
notReallyUnsound3 :: Program Gr
notReallyUnsound3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (Seq (ForC 1 (SpawnThread 2)) (If CTrue (ReadFromChannel (Global "y") "lowIn1") (ReadFromChannel (Global "c") "stdIn")))),
          (2, (Seq (Seq (Ass (Global "a") (Val 0)) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut")) (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))))
         ]

-- see notReallyUnsound
notReallyUnsound4 :: Program Gr
notReallyUnsound4 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(Seq (Seq (Ass (Global "y") (Val 1)) (SpawnThread 3)) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "y") "lowIn1") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "y"))))))),
          (3,(If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (Seq (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "c") "lowIn1")) (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut") (ReadFromChannel (Global "b") "lowIn1"))))
         ]

-- see notReallyUnsound
notReallyUnsound5 :: Program Gr
notReallyUnsound5 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(Seq (Seq (SpawnThread 2) (Ass (Global "c") (Val 1))) (Seq (Ass (Global "c") (Times (Var (Global "c")) (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut")))),
          (2,(Seq (Seq (Ass (Global "y") (Val (-1))) (Ass (Global "a") (Times (Var (Global "y")) (Var (Global "y"))))) (Seq (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "x") "stdIn"))) )
         ]

-- see notReallyUnsound
notReallyUnsound6 :: Program Gr
notReallyUnsound6 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(Seq (Seq (SpawnThread 3) (SpawnThread 2)) (If CFalse (Ass (Global "a") (Val 1)) (PrintToChannel (Val 0) "stdOut")))),
           (2,(If CFalse (If CFalse (Ass (Global "c") (Val 1)) Skip) (Seq (PrintToChannel (Val (-1)) "stdOut") Skip))),
           (3,(ForC 1 (Seq Skip Skip)))
         ]

-- see notReallyUnsound
notReallyUnsound7 :: Program Gr
notReallyUnsound7 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(Seq (Seq (SpawnThread 2) (SpawnThread 3)) (If CTrue (PrintToChannel (Val (-1)) "stdOut") (ReadFromChannel (Global "a") "stdIn")))),
          (2,(Seq (If CTrue (ReadFromChannel (Global "y") "lowIn1") (ReadFromChannel (Global "c") "lowIn1")) (ForC 2 (ReadFromChannel (Global "a") "stdIn")))),
          (3,(If CTrue (Seq Skip (ReadFromChannel (Global "y") "lowIn1")) (ForC 2 (ReadFromChannel (Global "x") "lowIn1"))))
         ]

-- see notReallyUnsound
notReallyUnsound8 :: Program Gr
notReallyUnsound8 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1,(Seq (Seq (PrintToChannel (Val 0) "stdOut") (Ass (Global "x") (Val 42))) (Seq (SpawnThread 2) (ReadFromChannel (Global "x") "lowIn1")))),
          (2,(Seq (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (SpawnThread 3)) (ForV (Global "x") (ReadFromChannel (Global "b") "lowIn1")))),
          (3,(ForC 1 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))))))
         ]

-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/620/
-- p  = 253 % 500 ≃ 0.50600                                  p' = 791 % 1500 ≃ 0.52733
-- fromList []
-- ---(6,PrintEvent 0 "stdOut")-->
-- fromList []
-- fromList []
-- ---(8,PrintEvent 1 "stdOut")-->
-- fromList []
-- fromList []
-- ---(10,PrintEvent 1 "stdOut")-->
-- fromList []
-- fromList []
-- ---(12,ReadEvent 1 "lowIn1")-->
-- fromList [("y",1)]
-- fromList []
-- ---(13,ReadEvent 2 "lowIn1")-->
-- fromList [("b",2)]
-- fromList []
-- ---(17,PrintEvent (-1) "stdOut")-->
-- fromList []
-- fromList []
-- ---(20,PrintEvent (-1) "stdOut")-->
-- fromList []

notReallyUnsound9 :: Program Gr
notReallyUnsound9 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (Seq (Seq Skip
                        (PrintToChannel (Val 0) "stdOut")) (Seq
                        (SpawnThread 2)
                        (PrintToChannel (Val 1) "stdOut")))),
          (2, (Seq (Seq (PrintToChannel (Val 1) "stdOut")
                        (SpawnThread 3))
                   (Seq (ReadFromChannel (Global "y") "lowIn1")
                        (ReadFromChannel (Global "b") "lowIn1")))),
          (3,           (If CFalse
                             (Seq (ReadFromChannel (Global "x") "stdIn")
                                  (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))))
                          {- else -}
                             (Seq (PrintToChannel (Val (-1)) "stdOut")
                                  (PrintToChannel (Val (-1)) "stdOut"))))
         ]


-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/693/
-- λ> forever $ mainEquivAnnotatedSome 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- -----------------
-- p  = 569 % 1500 ≃ 0.37933                                  p' = 2687 % 7500 ≃ 0.35827
-- fromList []
-- ---(12,ReadEvent 1 "lowIn1")-->
-- fromList [("b",1)]
-- fromList [("b",1),("z",-1)]
-- ---(13,PrintEvent (-1) "stdOut")-->
-- fromList []
-- fromList []
-- ---(14,ReadEvent 2 "lowIn1")-->
-- fromList [("b",2)]
-- fromList []
-- ---(8,ReadEvent 3 "lowIn1")-->
-- fromList [("a",3)]
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- Interrupted.
notReallyUnsound10 :: Program Gr
notReallyUnsound10 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (Seq (Seq (SpawnThread 3) (ReadFromChannel (Global "c") "stdIn")) (ForC 1 (ReadFromChannel (Global "a") "lowIn1"))) ),
          (3, (Seq (Seq (Ass (Global "z") (Val (-1))) (ReadFromChannel (Global "b") "lowIn1")) (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut") (ReadFromChannel (Global "b") "lowIn1"))))
         ]


-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/694/
-- λ> forever $ mainEquivAnnotatedSome 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- Interrupted.
notReallyUnsound11 :: Program Gr
notReallyUnsound11 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (Seq (Seq (SpawnThread 3) (SpawnThread 2)) (ForC 2 (ReadFromChannel (Global "c") "lowIn1")))),
          (2, (ForC 2 (Seq (PrintToChannel (Val 1) "stdOut") (ReadFromChannel (Global "x") "stdIn")))),
          (3, (Seq (ForC 1 (ReadFromChannel (Global "c") "stdIn")) (ForC 2 (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c")))))))
         ]

-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/709/
-- λ> forever $ mainEquivAnnotatedSome 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- -----------------
-- p  = 419 % 2500 ≃ 0.16760                                  p' = 118 % 625 ≃ 0.18880
-- fromList []
-- ---(7,ReadEvent 1 "lowIn1")-->
-- fromList [("z",1)]
-- fromList []
-- ---(7,ReadEvent 2 "lowIn1")-->
-- fromList [("z",2)]
-- fromList [("z",2)]
-- ---(11,PrintEvent 4 "stdOut")-->
-- fromList []
-- fromList [("z",2)]
-- ---(12,PrintEvent 4 "stdOut")-->
-- fromList []
-- fromList [("z",2)]
-- ---(11,PrintEvent 4 "stdOut")-->
-- fromList []
-- fromList [("z",2)]
-- ---(12,PrintEvent 4 "stdOut")-->
-- fromList []
-- fromList [("z",2)]
-- ---(17,PrintEvent 4 "stdOut")-->
-- fromList []
-- fromList [("z",2)]
-- ---(17,PrintEvent 4 "stdOut")-->
-- fromList []
notReallyUnsound12 :: Program Gr
notReallyUnsound12 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (ForC 2 (Seq (ReadFromChannel (Global "z") "lowIn1") (SpawnThread 2)))),
          (2, (Seq (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut") (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")) (Seq Skip (SpawnThread 3)))),
          (3, (Seq (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z"))))
                      (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")
                      (Ass (Global "x") (Times (Var (Global "z")) (Var (Global "z"))))) (Seq (ReadFromChannel (Global "a") "stdIn") (ReadFromChannel (Global "x") "stdIn")))
          )
         ]

-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/695/
-- λ> forever $ mainEquivAnnotatedSome 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- Interrupted.
notReallyUnsound13 :: Program Gr
notReallyUnsound13 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (ForC 1 (Seq (SpawnThread 2) (PrintToChannel (Val (-1)) "stdOut")))),
          (2, (Seq (Seq (PrintToChannel (Val 1) "stdOut") (PrintToChannel (Val 1) "stdOut")) (If CFalse (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val 1) "stdOut"))))
         ]


-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/696/
-- λ> forever $ mainEquivAnnotatedSome 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- -----------------
-- p  = 1381 % 1875 ≃ 0.73653                                  p' = 381 % 500 ≃ 0.76200
-- fromList []
-- ---(7,PrintEvent (-1) "stdOut")-->
-- fromList []
-- fromList []
-- ---(10,PrintEvent 1 "stdOut")-->
-- fromList []
-- fromList []
-- ---(11,PrintEvent 1 "stdOut")-->
-- fromList []
-- fromList []
-- ---(14,PrintEvent 1 "stdOut")-->
-- fromList []
-- -----------------
-- p  = 87 % 625 ≃ 0.13920                                  p' = 297 % 2500 ≃ 0.11880
-- fromList []
-- ---(10,PrintEvent 1 "stdOut")-->
-- fromList []
-- fromList []
-- ---(7,PrintEvent (-1) "stdOut")-->
-- fromList []
-- fromList []
-- ---(11,PrintEvent 1 "stdOut")-->
-- fromList []
-- fromList []
-- ---(14,PrintEvent 1 "stdOut")-->
-- fromList []
notReallyUnsound14 :: Program Gr
notReallyUnsound14 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
            (1, (ForC 1 (Seq (SpawnThread 2) (PrintToChannel (Val (-1)) "stdOut")))),
            (2, (Seq (Seq (PrintToChannel (Val 1) "stdOut") (PrintToChannel (Val 1) "stdOut")) (If CFalse (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val 1) "stdOut"))))
         ]

-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/767/
-- λ> forever $ mainEquivAnnotatedSome
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
notReallyUnsound15 :: Program Gr
notReallyUnsound15 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
            (1,(Seq (Seq (PrintToChannel (Val 42) "stdOut") (Ass (Global "z") (Val 42))) (Seq (SpawnThread 3) (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")))),
            (2,(If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut") (Ass (Global "b") (Times (Var (Global "z")) (Var (Global "z"))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (ReadFromChannel (Global "a") "lowIn1") Skip))),
            (3,(Seq (Seq (SpawnThread 2) (ReadFromChannel (Global "c") "stdIn")) (Seq (Ass (Global "c") (Times (Var (Global "z")) (Var (Global "z")))) (ReadFromChannel (Global "x") "lowIn1"))))
         ]



-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/767/
-- λ> forever $ mainEquivAnnotatedSome
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ...
notReallyUnsound16 :: Program Gr
notReallyUnsound16 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
            (1,(Seq (Seq (Ass (Global "a") (Val 17)) (SpawnThread 2)) (ForV (Global "a") (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "a"))))))),
            (2,(Seq (ForV (Global "a") (SpawnThread 3)) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (Ass (Global "b") (Times (Var (Global "a")) (Var (Global "a"))))))),
            (3,(If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (Seq Skip (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut")) (ForC 1 (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "a")))))))
         ]


-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/800/
-- λ> forever $ mainEquivAnnotatedSome
-- λ> forever $ mainEquivAnnotatedSome
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ...
-- ... (90 times) ..
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- -----------------
-- p  = 1123 % 1875 ≃ 0.59893                                  p' = 1078 % 1875 ≃ 0.57493
-- fromList []
-- ---(10,PrintEvent 42 "stdOut")-->
-- fromList []
-- fromList []
-- ---(15,ReadEvent 1 "lowIn1")-->
-- fromList [("c",1)]
-- fromList []
-- ---(15,ReadEvent 2 "lowIn1")-->
-- fromList [("c",2)]
-- fromList [("c",2)]
-- ---(22,PrintEvent 4 "stdOut")-->
-- fromList []
-- fromList [("c",2)]
-- ---(22,PrintEvent 4 "stdOut")-->
-- fromList []
-- fromList [("c",2)]
-- ---(22,PrintEvent 4 "stdOut")-->
-- fromList []
notReallyUnsound18 :: Program Gr
notReallyUnsound18 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
            (1,(Seq (If CTrue Skip (ReadFromChannel (Global "a") "lowIn1")) (Seq (PrintToChannel (Val 42) "stdOut") (SpawnThread 2)))),
            (2,(ForC 2 (Seq (ReadFromChannel (Global "c") "lowIn1") (SpawnThread 3))) ),
            (3,(ForV (Global "c") (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (ReadFromChannel (Global "a") "stdIn"))))
         ]



-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/814/
-- λ> forever $ mainEquivAnnotatedSome
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
notReallyUnsound17 :: Program Gr
notReallyUnsound17 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
            (1, (Seq (Seq (SpawnThread 2) (PrintToChannel (Val 0) "stdOut")) (Seq (PrintToChannel (Val 0) "stdOut") (ReadFromChannel (Global "b") "lowIn1")))),
            (2, (ForC 2 (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "x") "lowIn1"))))
         ]



-- see notReallyUnsound
-- reported in run http://i44pc16:8080/job/irlsod/835/
-- λ> forever $ mainEquivAnnotatedSome
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
-- i  = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[2,1,2,1,2])] ...     i' = fromList [("lowIn1",[1,2,3,4,1]),("lowIn2",[4,3,2,1,4]),("stdIn",[-1,0,-1,0,-1])] ... 
notReallyUnsound19 :: Program Gr
notReallyUnsound19 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
            (1,(Seq (Seq (Ass (Global "y") (Val 17)) (Ass (Global "a") (Times (Var (Global "y")) (Var (Global "y"))))) (ForC 2 (SpawnThread 3)))),
            (2,(ForC 1 (Seq (ReadFromChannel (Global "c") "stdIn") (ReadFromChannel (Global "c") "stdIn")))),
            (3,(ForV (Global "y") (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut") (SpawnThread 2))))
         ]


notReallyUnsound20 :: Program Gr
notReallyUnsound20 = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram (Map.fromList [ (1, "main"), (3,"thread3")]) code
        code = Map.fromList $ [
          ("main",  (Seq (SpawnThread 3) (CallProcedure "procH"))
          ),
          ("procH", (PrintToChannel (Val 17) "stdOut")
          ),
          ("thread3",
           (Seq (Ass (Global "b") (Val 42)) (ReadFromChannel (Global "y") "lowIn1"))
          )
         ]

notReallyUnsound21 :: Program Gr
notReallyUnsound21 = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram (Map.fromList [ (1, "main"),(2, "thread2"),(3,"thread3")]) code
        code = Map.fromList $ [
          ("main", (Seq (SpawnThread 2) (CallProcedure "baz"))),
          ("thread2",(If CFalse (ReadFromChannel (Global "y") "stdIn") (CallProcedure "procG"))),
          ("thread3", (ReadFromChannel (Global "y") "lowIn1")),
          ("baz", (SpawnThread 3)),
          ("procG", (PrintToChannel (Val 42) "stdOut"))
         ]

{- someGen7 -}
notReallyUnsound22 :: Program Gr
notReallyUnsound22 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (Seq (Seq (SpawnThread 3) (SpawnThread 2)) (ForC 1 (ForC 2 (Ass (Global "z") (Val 9))))) undefined undefined undefined),
        ("thread2",Generated (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") Skip) (If CTrue (PrintToChannel (Val 0) "stdOut") (ReadFromChannel (Global "x") "lowIn1"))) undefined undefined undefined),
        ("thread3",Generated (Seq (Ass (Global "a") (Val 4)) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut")) undefined undefined undefined)
    ])

{- someGen5 -}
notReallyUnsound23 :: Program Gr
notReallyUnsound23 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [("main",Generated (ForC 2 (ForC 1 (Seq (Seq (SpawnThread 2) (SpawnThread 3)) (If CTrue (PrintToChannel (Val 0) "stdOut") (Ass (Global "y") (Val 4)))))) undefined undefined undefined),
                   ("thread2",Generated (Seq (Seq (ReadFromChannel (Global "z") "lowIn1") (PrintToChannel (Plus (Var (Global "z")) (Var (Global "z"))) "stdOut")) (ForC 1 (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut") (ReadFromChannel (Global "c") "lowIn1")))) undefined undefined undefined),
                   ("thread3",Generated (If CFalse (PrintToChannel (Val 0) "stdOut") (PrintToChannel (Val 1) "stdOut")) undefined undefined undefined)
    ])


{- someGen4 -}
notReallyUnsound24 :: Program Gr
notReallyUnsound24 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (ForC 2 (ForC 2 (Seq (Seq (SpawnThread 3) (SpawnThread 2)) (Seq (PrintToChannel (Val 0) "stdOut") (PrintToChannel (Val 17) "stdOut"))))) undefined undefined undefined),
        ("thread2",Generated (Seq (ForC 1 (Seq (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val 0) "stdOut"))) (Seq (Ass (Global "a") (Val 42)) (ReadFromChannel (Global "b") "stdIn"))) undefined undefined undefined),
        ("thread3",Generated (Seq (PrintToChannel (Val 1) "stdOut") Skip) undefined undefined undefined)
    ])



{- someGen3 -}
notReallyUnsound25 :: Program Gr
notReallyUnsound25 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [
        ("main",Generated (Seq (ForC 2 (ForC 1 (SpawnThread 2))) (Seq (SpawnThread 3) (ReadFromChannel (Global "c") "lowIn1"))) undefined undefined undefined),
        ("thread2",Generated (ForC 2 (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 17) "stdOut")) (If CFalse (Ass (Global "c") (Val 0)) (ReadFromChannel (Global "a") "lowIn1")))) undefined undefined undefined),
        ("thread3",Generated (If CTrue (PrintToChannel (Val 1) "stdOut") Skip) undefined undefined undefined)
    ])

{- http://i44pc16:8080/job/irlsod/3143/testReport/(root)/soundness%20Properties%20(concerning%20soundness)/allSoundIntraMulti___timingClassificationAtUses__timingClassificationDomPaths__timingClassification__timingClassificationSimple___timingClassificationIdomBischof__minimalClassification__giffhornLSOD__simonClassification___/ -}
notReallyUnsound26 :: Program Gr
notReallyUnsound26 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2")])
    (Map.fromList [("main",Generated (Seq (If CTrue (ReadFromChannel (Global "z") "lowIn1") Skip) (ForC 2 (Seq (SpawnThread 2) (ReadFromChannel (Global "b") "stdIn")))) undefined undefined undefined),
                   ("thread2",Generated
                    (Seq (Seq (Ass (Global "y") (Val 9)) (ReadFromChannel (Global "x") "lowIn1")) (ForC 2 (Seq (ReadFromChannel (Global "b") "lowIn1") (PrintToChannel (Neg (Var (Global "x"))) "stdOut")))) undefined undefined undefined)
    ])


notReallyUnsound27 :: Program Gr
notReallyUnsound27 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2")])
    (Map.fromList [("main",Generated (ForC 2 (Seq (Seq (PrintToChannel (Val 1) "stdOut") (Ass (Global "a") (Val (-1)))) (Seq (PrintToChannel (Var (Global "a")) "stdOut") (SpawnThread 2)))) undefined undefined undefined),
                   ("thread2",Generated (If (Leq (Val 0) (Neg (Var (Global "a")))) (Seq (PrintToChannel (Var (Global "a")) "stdOut") (PrintToChannel (Plus (Var (Global "a")) (Var (Global "a"))) "stdOut")) (ForC 1 (Seq (Ass (Global "c") (Neg (Var (Global "a")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut")))) undefined undefined undefined)
     ])

{- http://i44pc16:8080/job/irlsod/3157/testReport/junit/(root)/soundness%20Properties%20(concerning%20soundness)/allSoundIntraMulti___timingClassificationAtUses__timingClassificationDomPaths__timingClassification__timingClassificationSimple___timingClassificationIdomBischof__minimalClassification__giffhornLSOD__simonClassification___/ -}
notReallyUnsound28 :: Program Gr
notReallyUnsound28 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2")])
    (Map.fromList [("main",Generated (ForC 2 (Seq (ForC 1 (ReadFromChannel (Global "a") "lowIn1")) (Seq (SpawnThread 2) (ReadFromChannel (Global "z") "lowIn1")))) undefined undefined undefined),
                   ("thread2",Generated (ForC 2 (Seq (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (Ass (Global "x") (Plus (Var (Global "a")) (Var (Global "a"))))) (ForV (Global "a") (Ass (Global "x") (Neg (Var (Global "a"))))))) undefined undefined undefined)])


{- http://i44pc16:8080/job/irlsod/3177/testReport/junit/(root)/soundness%20Properties%20(concerning%20soundness)/allSoundIntraMulti___timingClassificationAtUses__timingClassificationDomPaths__timingClassification__timingClassificationSimple___timingClassificationIdomBischof__minimalClassification__giffhornLSOD__simonClassification___/ -}
notReallyUnsound29 :: Program Gr
notReallyUnsound29 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [("main",Generated (Seq (Seq (PrintToChannel (Val 0) "stdOut") (SpawnThread 3)) (If CFalse (Ass (Global "b") (Val 4)) (Ass (Global "y") (Val 9)))) undefined undefined undefined),
                   ("thread2",Generated (ForC 2 (If CTrue (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "c") "lowIn1"))) undefined undefined undefined),
                   ("thread3",Generated (ForC 2 (Seq (Seq (PrintToChannel (Val 1) "stdOut") (PrintToChannel (Val 0) "stdOut")) (Seq (SpawnThread 2) (PrintToChannel (Val 9) "stdOut")))) undefined undefined undefined)])

{- http://i44pc16:8080/job/irlsod/3188/testReport/junit/(root)/soundness%20Properties%20(concerning%20soundness)/allSoundIntraMulti___timingClassificationAtUses__timingClassificationDomPaths__timingClassification__timingClassificationSimple___timingClassificationIdomBischof__minimalClassification__giffhornLSOD__simonClassification___/ -}
notReallyUnsound30 :: Program Gr
notReallyUnsound30 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [("main",Generated (Seq (Seq Skip (SpawnThread 3)) (Seq (SpawnThread 2) (ReadFromChannel (Global "c") "lowIn1"))) undefined undefined undefined),
                   ("thread2",Generated (Seq (ForC 1 (If CTrue (PrintToChannel (Val 9) "stdOut") (PrintToChannel (Val (-1)) "stdOut"))) (If CTrue (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "c") "stdIn"))) undefined undefined undefined),
                   ("thread3",Generated (If CTrue (PrintToChannel (Val (-1)) "stdOut") (ReadFromChannel (Global "x") "stdIn")) undefined undefined undefined)])



notReallyUnsound31 :: Program Gr
notReallyUnsound31 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
    (Map.fromList [("main",Generated (Seq (Seq (SpawnThread 2) (Ass (Global "b") (Val 4))) (If (Leq (Val 0) (Val (-1))) (ReadFromChannel (Global "a") "lowIn1") (Ass (Global "b") (Times (Var (Global "b")) (Var (Global "b")))))) undefined undefined undefined),
                   ("thread2",Generated (Seq (Seq (Ass (Global "y") (Val 0)) (SpawnThread 3)) (If (Leq (Val 0) (Val 4)) (PrintToChannel (Plus (Var (Global "y")) (Var (Global "y"))) "stdOut") (PrintToChannel (Neg (Var (Global "y"))) "stdOut"))) undefined undefined undefined),
                   ("thread3",Generated (Seq (PrintToChannel (Var (Global "y")) "stdOut") (PrintToChannel (Neg (Var (Global "y"))) "stdOut")) undefined undefined undefined)])

controlDepExample :: Program Gr
controlDepExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = code2Program code
        code = Map.fromList $ [
          (1, (ForC 1
                 (If CFalse (Seq (PrintToChannel (Val 0) "stdOut") (PrintToChannel (Val 1) "stdOut"))
                            (ForC 1 (ReadFromChannel (Global "c") "lowIn1"))
                 )
              ) `Seq`
              (Ass (Global "x") (Val 0))
          )
         ]


simpleBlocking :: Program Gr
simpleBlocking =  p { observability = defaultObservabilityMap (tcfg p) } 
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                            `Seq`
           SpawnThread 2                   `Seq`
           SpawnThread 3
          ),
          (2, Skip `Seq`
              ReadFromChannel (Global "z") stdIn    `Seq`
              PrintToChannel (Val 2) stdOut
          ),
          (3, Skip `Seq`
              ReadFromChannel (Global "z") stdIn2   `Seq`
              PrintToChannel (Val 1) stdOut
          )
         ]



exampleTimingDep :: Program Gr 
exampleTimingDep=  p { observability = defaultObservabilityMap (tcfg p) } 
  where p = code2Program code
        code = Map.fromList $ [
          (1,
           Skip                            `Seq`
           If (CTrue)
             (If (CTrue)
                Skip
                Skip)
             (Skip `Seq` Skip `Seq` Skip)
          )
         ]

simpleProcedural :: Program Gr
simpleProcedural  =  p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram (Map.fromList [ (1, "Main") ]) code
        code = Map.fromList $ [
          ("Main",
           Skip                            `Seq`
           Ass (Global "sum") (Val 0)      `Seq`
           Ass (Global "n")   (Val 10)     `Seq`
           Ass (Global "i")   (Val 1)      `Seq`
           ForV (Global "n") (
             CallProcedure "Add"           `Seq`
             CallProcedure "Increment"     `Seq`
             CallProcedure "Decrement"     `Seq`
             CallProcedure "Increment"
           )                               `Seq`
           Skip
          ),
          ("Add", Skip `Seq`
              Ass (Global "sum") ((Var $ Global "sum") `Plus` (Var $ Global "i"))
          ),
          ("Increment", Skip `Seq`
              Ass (Global "i") ((Var $ Global "i") `Plus` (Val 1))
          ),
          ("Decrement", Skip `Seq`
              Ass (Global "i") ((Var $ Global "i") `Plus` (Val (-1)))
          )
         ]


simpleProcedural2 :: Program Gr
simpleProcedural2  =  p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram (Map.fromList [ (1, "Main") ]) code
        code = Map.fromList $ [
          ("Main",
           Skip                            `Seq`
           CallProcedure "Init"            `Seq`
           ForV (Global "n") (
             CallProcedure "Add"           `Seq`
             CallProcedure "Increment"     `Seq`
             CallProcedure "Decrement"     `Seq`
             CallProcedure "Increment"
           )                               `Seq`
           Ass (Global "sum") (Val 0)      `Seq`
           Ass (Global "i")   (Val 1)      `Seq`
           CallProcedure "Add"             `Seq`
           Ass (Global "result") (Var $ Global "sum") `Seq`
           Skip
          ),
          ("Init", Skip `Seq`
           Ass (Global "sum") (Val 0)      `Seq`
           Ass (Global "n")   (Val 10)     `Seq`
           Ass (Global "i")   (Val 1)
          ),
          ("Add", Skip `Seq`
              Ass (Global "sum") ((Var $ Global "sum") `Plus` (Var $ Global "i"))
          ),
          ("Increment", Skip `Seq`
              Ass (Global "i") ((Var $ Global "i") `Plus` (Val 1))
          ),
          ("Decrement", Skip `Seq`
              Ass (Global "i") ((Var $ Global "i") `Plus` (Val (-1)))
          )
         ]


simpleProcedural3 :: Program Gr
simpleProcedural3  =  p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram (Map.fromList [ (1, "Main") ]) code
        code = Map.fromList $ [
          ("Main",
           Skip                            `Seq`
           Ass (Global "sum") (Val 0)      `Seq`
           Ass (Global "n")   (Val 10)     `Seq`
           CallProcedure "Compute"         `Seq`
           Skip
          ),
          ("Compute",
           Skip                            `Seq`
           CallProcedure "ReallyCompute"   `Seq`
           CallProcedure "ReallyCompute"   `Seq`
           Skip
          ),
          ("ReallyCompute",
           Skip                            `Seq`
           Ass (Global "i")   (Val 1)      `Seq`
           ForV (Global "n") (
             CallProcedure "Add"           `Seq`
             CallProcedure "Increment"     `Seq`
             CallProcedure "Decrement"     `Seq`
             CallProcedure "Increment"
           )                               `Seq`
           Skip
          ),
          ("Add", Skip `Seq`
              Ass (Global "sum") ((Var $ Global "sum") `Plus` (Var $ Global "i"))
          ),
          ("Increment", Skip `Seq`
              Ass (Global "i") ((Var $ Global "i") `Plus` (Val 1))
          ),
          ("Decrement", Skip `Seq`
              Ass (Global "i") ((Var $ Global "i") `Plus` (Val (-1)))
          )
         ]



simpleRecursive :: Program Gr
simpleRecursive  =  p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram (Map.fromList [ (1, "Main") ]) code
        code = Map.fromList $ [
          ("Main",
           Skip                            `Seq`
           CallProcedure "Init"            `Seq`
           CallProcedure "Fak"             `Seq`
           Skip
          ),
          ("Init", Skip `Seq`
           Ass (Global "n")      (Val 5)   `Seq`
           Ass (Global "fak")    (Val 1)   `Seq`
           Ass (Global "result") (Val 0)
          ),
          ("Fak", Skip `Seq`
              If ((Var $ Global "n") `Leq` (Val 1)) (
                  Ass (Global "result") (Var $ Global "fak")
                ) {- ELSE -} (
                  Ass (Global "fak") ((Var $ Global "fak") `Times` (Var $ Global "n"))   `Seq`
                  Ass (Global "n")   ((Var $ Global "n")   `Plus`  (Val (-1) ))          `Seq`
                  CallProcedure "Fak"
                )
          )
         ]





indepsCounterExample :: Program Gr
indepsCounterExample = toProgram $ GeneratedProgram
 (Map.fromList [(1,"main"),(3,"thread3")])
 (Map.fromList [("bar",Generated (ForV (Global "b") (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (Seq (ReadFromChannel (Global "c") "lowIn1") (ReadFromChannel (Global "y") "lowIn1")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) Skip (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))))
                 undefined undefined undefined
                ),
                ("baz",Generated (Seq (ForC 1 (If CTrue (SpawnThread 3) (Ass (Global "c") (Val 17)))) (ForC 2 (Seq (ReadFromChannel (Global "b") "stdIn") (CallProcedure "bar"))))
                 -- (fromList [Global "b"]) (fromList [(3,fromList [])]) (Map.fromList [("bar",fromList [Global "b"])])
                 undefined undefined undefined
                ),
                ("main",Generated (Seq (Seq (ForC 2 Skip) (If CTrue (CallProcedure "baz") (ReadFromChannel (Global "y") "lowIn1"))) (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "a"))))) (Seq Skip (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "z")))))))
                 -- (fromList [Global "a",Global "z"]) (fromList []) (fromList [("baz",fromList [])])
                                  undefined undefined undefined
                ),
                ("thread3",Generated (Seq (If CTrue (Seq (PrintToChannel (Val 17) "stdOut") (PrintToChannel (Val 42) "stdOut")) (ForC 1 Skip)) (Seq (Seq (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "x") "stdIn")) (ForV (Global "x") (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))))
                 -- (fromList [Global "b",Global "x"]) (fromList []) (fromList [])
                 undefined undefined undefined
                )
  ]
 )

indepsExceptionExample :: Program Gr
indepsExceptionExample = toProgram $ GeneratedProgram
 (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
 (Map.fromList [("bar",Generated (Seq (If CTrue (If CFalse (PrintToChannel (Val 0) "stdOut") Skip) (Seq (ReadFromChannel (Global "y") "stdIn") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "y")))))) (Seq (Seq (Ass (Global "c") (Val 0)) (CallProcedure "foo")) (Seq (CallProcedure "foo") (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut"))))
                  undefined undefined undefined),
                ("baz",Generated (Seq (If CFalse (If CFalse (ReadFromChannel (Global "y") "stdIn") (Ass (Global "y") (Val (-1)))) (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "x") "lowIn1"))) (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (Ass (Global "b") (Val (-1)))) (Seq (CallProcedure "baz") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))))))
                  undefined undefined undefined),
                ("foo",Generated (ForC 1 (Seq (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c"))))) (ForC 2 (ReadFromChannel (Global "c") "lowIn1"))))
                  undefined undefined undefined),
                ("main",Generated (Seq (Seq (Seq (SpawnThread 3) (SpawnThread 2)) (Seq (CallProcedure "bar") (PrintToChannel (Val 1) "stdOut"))) (ForC 1 (If CFalse (ReadFromChannel (Global "z") "stdIn") Skip)))                 undefined undefined undefined),
                ("thread2",Generated (If CTrue (If CFalse (ForC 1 (PrintToChannel (Val 42) "stdOut")) (Seq (ReadFromChannel (Global "x") "lowIn1") Skip)) (Seq (If CFalse (ReadFromChannel (Global "b") "stdIn") (CallProcedure "bar")) (Seq (CallProcedure "baz") (Ass (Global "z") (Val 17)))))
                 undefined undefined undefined),
                ("thread3",Generated (ForC 1 (Seq (If CTrue Skip (ReadFromChannel (Global "a") "stdIn")) (Seq (Ass (Global "a") (Val 42)) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))))
                 undefined undefined undefined)])


summaryExample :: Program Gr
summaryExample = toProgram $ GeneratedProgram
 (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")])
 (Map.fromList [("bar",Generated (Seq (ForC 2 (If CTrue (Ass (Global "y") (Val 0)) (ReadFromChannel (Global "z") "stdIn"))) (If CTrue (Seq (ReadFromChannel (Global "c") "lowIn1") Skip) (Seq (CallProcedure "bar") (PrintToChannel (Val 42) "stdOut"))))
                 undefined undefined undefined),
                ("foo",Generated (ForC 2 (If CFalse (Seq (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val 0) "stdOut")) (If CTrue (PrintToChannel (Val 17) "stdOut") (Ass (Global "y") (Val 0)))))
                  undefined undefined undefined),
                ("main",Generated (Seq (If CFalse (If CTrue (ReadFromChannel (Global "c") "stdIn") Skip) (Seq (CallProcedure "bar") (SpawnThread 2))) (ForC 2 (If CTrue (PrintToChannel (Val 1) "stdOut") (PrintToChannel (Val (-1)) "stdOut"))))
                  undefined undefined undefined),
                ("thread2",Generated (If CTrue (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 0) "stdOut")) (Seq (SpawnThread 3) (ReadFromChannel (Global "c") "stdIn"))) (Seq (Seq (CallProcedure "foo") (Ass (Global "a") (Val 0))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (CallProcedure "foo"))))
                  undefined undefined undefined),
                ("thread3",Generated (Seq (Seq (Seq (Ass (Global "b") (Val 42)) (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "b"))))) (Seq Skip (Ass (Global "b") (Times (Var (Global "b")) (Var (Global "c")))))) (Seq (Seq Skip (ReadFromChannel (Global "b") "stdIn")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "c")))) Skip (PrintToChannel (Times (Var (Global "c")) (Var (Global "b"))) "stdOut"))))
                  undefined undefined undefined)
 ])


summaryExample2 :: Program Gr
summaryExample2 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (CallProcedure "foo") Skip)) (Seq (Seq (ReadFromChannel (Global "a") "lowIn1") (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "x"))))) (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (CallProcedure "foo")))) (ForV (Global "x") (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (ReadFromChannel (Global "a") "stdIn"))))) undefined undefined undefined),("baz",Generated (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (ForV (Global "x") (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (CallProcedure "bar") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (ReadFromChannel (Global "b") "lowIn1") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "x"))))))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "z"))) "stdOut"))) (Seq (Seq Skip (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))))) undefined undefined undefined),("foo",Generated (ForC 1 (Seq (Seq (If CFalse (Ass (Global "c") (Val 0)) (Ass (Global "c") (Val 17))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c")))) (CallProcedure "foo"))) (Seq (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "x") "stdIn") (CallProcedure "foo")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "x") "lowIn1"))))) undefined undefined undefined),("main",Generated (Seq (Seq (If CTrue (If CTrue (ReadFromChannel (Global "y") "lowIn1") (ReadFromChannel (Global "c") "stdIn")) (Seq (ReadFromChannel (Global "z") "stdIn") (Ass (Global "y") (Times (Var (Global "z")) (Var (Global "z")))))) (If CTrue (Seq (SpawnThread 3) (PrintToChannel (Val (-1)) "stdOut")) (Seq (PrintToChannel (Val 42) "stdOut") (ReadFromChannel (Global "b") "lowIn1")))) (Seq (Seq (Seq Skip (ReadFromChannel (Global "y") "stdIn")) (Seq (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y")))) (CallProcedure "foo"))) (ForC 2 (ForV (Global "b") (SpawnThread 2))))) undefined undefined undefined),("thread2",Generated (Seq (ForV (Global "b") (ForC 1 (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "b")))) (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "c") "lowIn1")))) (Seq (Seq (Seq (Ass (Global "x") (Times (Var (Global "b")) (Var (Global "y")))) (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "y"))))) (Seq (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "a") "stdIn"))) (ForC 2 (ForV (Global "x") (ReadFromChannel (Global "y") "stdIn"))))) undefined undefined undefined),("thread3",Generated (If CFalse (Seq (ForC 1 (If CFalse (ReadFromChannel (Global "c") "lowIn1") Skip)) (ForC 2 (ForC 2 (Ass (Global "b") (Val 1))))) (ForC 1 (If CFalse (Seq (ReadFromChannel (Global "x") "stdIn") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq (ReadFromChannel (Global "x") "stdIn") (CallProcedure "baz"))))) undefined undefined undefined)])


summaryExample3 :: Program Gr
summaryExample3 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (ForC 1 (ForC 2 Skip)) (Seq (If CTrue Skip (ReadFromChannel (Global "b") "stdIn")) (If CTrue (Ass (Global "a") (Val 17)) (CallProcedure "bar")))) undefined undefined undefined),("baz",Generated (Seq (If CFalse (ForC 1 (Ass (Global "y") (Val (-1)))) (Seq Skip (PrintToChannel (Val 42) "stdOut"))) (If CFalse (ForC 1 (ReadFromChannel (Global "a") "lowIn1")) (Seq (PrintToChannel (Val 0) "stdOut") (CallProcedure "bar")))) undefined undefined undefined),("main",Generated (Seq (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (SpawnThread 3)) (Seq (Ass (Global "z") (Val 0)) Skip)) (ForV (Global "z") (Seq (ReadFromChannel (Global "x") "stdIn") (Ass (Global "b") (Times (Var (Global "z")) (Var (Global "x"))))))) undefined undefined undefined),("thread3",Generated (Seq (Seq (If CFalse (CallProcedure "baz") (PrintToChannel (Val 0) "stdOut")) (If CFalse (PrintToChannel (Val 0) "stdOut") (Ass (Global "b") (Val 1)))) (ForC 1 (Seq (Ass (Global "z") (Val 17)) (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")))) undefined undefined undefined)])


summaryExample4 :: Program Gr
summaryExample4 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (Seq (ForV (Global "b") (ForV (Global "z") (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "b")))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (Seq (Ass (Global "a") (Times (Var (Global "z")) (Var (Global "b")))) (ReadFromChannel (Global "b") "lowIn1")) (Seq (CallProcedure "bar") (Ass (Global "z") (Times (Var (Global "b")) (Var (Global "b"))))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (Seq (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (ReadFromChannel (Global "z") "stdIn") (Ass (Global "c") (Times (Var (Global "z")) (Var (Global "z"))))) (Seq (Ass (Global "x") (Times (Var (Global "b")) (Var (Global "b")))) Skip)) (Seq (ForC 2 (CallProcedure "baz")) (ForV (Global "b") (CallProcedure "baz"))))) undefined undefined undefined),("baz",Generated (Seq (ForV (Global "z") (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "z")))) (ForV (Global "b") Skip) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut") Skip))) (ForC 2 (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (ForV (Global "b") (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut")) (Seq (CallProcedure "baz") (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut"))))) undefined undefined undefined),("foo",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (Seq (Seq (CallProcedure "foo") (Ass (Global "z") (Times (Var (Global "b")) (Var (Global "z"))))) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "z")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut") (CallProcedure "bar"))) (Seq (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "z")))) (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "z")))) (CallProcedure "baz")) (ForV (Global "z") (ReadFromChannel (Global "a") "stdIn")))) (ForC 1 (ForC 2 (ForC 1 (CallProcedure "bar"))))) undefined undefined undefined),("main",Generated (ForC 2 (Seq (Seq (Seq Skip (Ass (Global "b") (Val (-1)))) (Seq (ReadFromChannel (Global "z") "lowIn1") (Ass (Global "z") (Times (Var (Global "z")) (Var (Global "z")))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) (ForV (Global "b") (ReadFromChannel (Global "x") "stdIn")) (ForC 1 (SpawnThread 3))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (Seq (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))) (CallProcedure "foo")) (ForC 1 (Ass (Global "b") (Times (Var (Global "z")) (Var (Global "b")))))) (Seq (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "b"))) "stdOut") Skip) (ForV (Global "z") (Ass (Global "x") (Times (Var (Global "z")) (Var (Global "z"))))))) (ForV (Global "b") (ForV (Global "z") (Seq (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "z")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut"))))) undefined undefined undefined),("thread3",Generated (ForV (Global "z") (Seq (Seq (Seq (SpawnThread 2) (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut")) (ForV (Global "b") (PrintToChannel (Times (Var (Global "b")) (Var (Global "z"))) "stdOut"))) (ForC 1 (Seq (PrintToChannel (Times (Var (Global "z")) (Var (Global "b"))) "stdOut") (Ass (Global "x") (Times (Var (Global "z")) (Var (Global "b")))))))) undefined undefined undefined)])

summaryExample5 :: Program Gr
summaryExample5 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (ForC 2 (Seq (Seq (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "y")))) (ReadFromChannel (Global "y") "stdIn") (CallProcedure "bar")))) (Seq (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (PrintToChannel (Times (Var (Global "a")) (Var (Global "b"))) "stdOut")) (ForV (Global "b") (ReadFromChannel (Global "y") "stdIn"))) (Seq (ForV (Global "y") (CallProcedure "foo")) (ForV (Global "a") (ReadFromChannel (Global "z") "stdIn"))))) undefined undefined undefined),("baz",Generated (Seq (Seq (ForC 1 (Seq (PrintToChannel (Val 0) "stdOut") (Ass (Global "y") (Val 42)))) (ForV (Global "y") (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (CallProcedure "bar") (ReadFromChannel (Global "b") "stdIn")))) (Seq (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (ForV (Global "y") (CallProcedure "bar")) (ForC 2 (Ass (Global "z") (Times (Var (Global "y")) (Var (Global "y")))))) (ForV (Global "y") (Seq Skip (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "y")))))))) undefined undefined undefined),("foo",Generated (Seq (If CTrue (If CFalse (Seq (PrintToChannel (Val 1) "stdOut") (PrintToChannel (Val 17) "stdOut")) (If CTrue (PrintToChannel (Val 42) "stdOut") (ReadFromChannel (Global "x") "lowIn1"))) (Seq (Seq (ReadFromChannel (Global "c") "lowIn1") (ReadFromChannel (Global "x") "lowIn1")) (Seq (ReadFromChannel (Global "y") "stdIn") (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))))) (Seq (Seq (Seq (Ass (Global "y") (Val 1)) (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))) (Seq Skip (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "b")))))) (Seq (Seq (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "b")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "y"))) "stdOut")) (ForV (Global "c") (CallProcedure "foo"))))) undefined undefined undefined),("main",Generated (Seq (If CTrue (Seq (If CTrue (PrintToChannel (Val 0) "stdOut") (ReadFromChannel (Global "a") "lowIn1")) (ForC 1 (ReadFromChannel (Global "x") "stdIn"))) (ForC 2 (ForC 1 (CallProcedure "baz")))) (Seq (If CFalse (Seq (Ass (Global "x") (Val 0)) Skip) (Seq (SpawnThread 2) (PrintToChannel (Val (-1)) "stdOut"))) (Seq (ForC 2 (CallProcedure "baz")) (Seq (PrintToChannel (Val 17) "stdOut") (ReadFromChannel (Global "a") "stdIn"))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (Seq (Seq Skip (ReadFromChannel (Global "c") "stdIn")) (Seq (ReadFromChannel (Global "c") "stdIn") (SpawnThread 3))) (Seq (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (ReadFromChannel (Global "y") "stdIn")) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") Skip))) (ForV (Global "c") (Seq (ForC 2 (Ass (Global "z") (Times (Var (Global "c")) (Var (Global "c"))))) (Seq (ReadFromChannel (Global "a") "lowIn1") (PrintToChannel (Times (Var (Global "z")) (Var (Global "c"))) "stdOut"))))) undefined undefined undefined),("thread3",Generated (Seq (ForC 1 (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))) (CallProcedure "foo")) (ForC 2 (Ass (Global "c") (Times (Var (Global "c")) (Var (Global "c"))))))) (Seq (ForC 2 (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "a") "lowIn1") (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))))) (Seq (Seq (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "b"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) Skip (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))))) undefined undefined undefined)])

summaryExample6 :: Program Gr
summaryExample6 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2")]) (Map.fromList [("baz",Generated (Seq (ReadFromChannel (Global "a") "lowIn1") (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a"))))) undefined undefined undefined),("main",Generated (Seq (PrintToChannel (Val 17) "stdOut") (SpawnThread 2)) undefined undefined undefined),("thread2",Generated (Seq (CallProcedure "baz") (ReadFromChannel (Global "y") "stdIn")) undefined undefined undefined)])

summaryExample7 :: Program Gr
summaryExample7 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("baz",Generated (Seq (Seq (ForC 2 (Seq (CallProcedure "baz") (Ass (Global "c") (Val 42)))) (Seq (ForC 1 (SpawnThread 2)) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") Skip))) (ForV (Global "c") (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (ReadFromChannel (Global "z") "stdIn") (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "z"))))) (ForC 1 (ReadFromChannel (Global "y") "stdIn"))))) undefined undefined undefined),("foo",Generated (Seq (ForC 1 (ForC 2 (Seq (PrintToChannel (Val 42) "stdOut") (CallProcedure "baz")))) (Seq (Seq (Seq (Ass (Global "y") (Val 0)) (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut")) (Seq (CallProcedure "foo") (CallProcedure "baz"))) (Seq (ForV (Global "y") (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut")) (ForC 2 (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "y")))))))) undefined undefined undefined),("main",Generated (Seq (Seq (ForC 1 (Seq (SpawnThread 3) (Ass (Global "b") (Val (-1))))) (ForV (Global "b") (ForC 2 (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "b"))))))) (Seq (ForC 2 (ForV (Global "b") (Ass (Global "y") (Times (Var (Global "b")) (Var (Global "b")))))) (ForC 1 (Seq (Ass (Global "a") (Times (Var (Global "b")) (Var (Global "b")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (ForV (Global "c") (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c")))))) (Seq (Seq (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "c")))) Skip) (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "c"))))))) (ForV (Global "y") (ForC 1 (ForC 1 (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "c")))))))) undefined undefined undefined),("thread3",Generated (ForC 1 (Seq (Seq (Seq Skip (CallProcedure "foo")) (Seq (ReadFromChannel (Global "x") "lowIn1") (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x")))))) (ForV (Global "y") (Seq (ReadFromChannel (Global "x") "stdIn") Skip)))) undefined undefined undefined)])

summaryExample7' :: Program Gr
summaryExample7' = toProgram $ GeneratedProgram (
  Map.fromList [(1,"main")])
 (Map.fromList [
     ("baz",Generated (Seq (Seq (ForC 2 (Seq (CallProcedure "baz") Skip)) Skip) Skip) undefined undefined undefined),
     ("foo",Generated (Seq (Seq Skip (CallProcedure "baz")) (Seq (Seq Skip (Seq (CallProcedure "foo") (CallProcedure "baz"))) Skip)) undefined undefined undefined),
     ("main",Generated (ForC 1 (CallProcedure "foo")) undefined undefined undefined)
 ])


summaryExample8 :: Program Gr
summaryExample8 =toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(3,"thread3")]) (Map.fromList [("bar",Generated (ForV (Global "b") (Seq (Seq (ForC 2 (PrintToChannel (Times (Var (Global "b")) (Var (Global "y"))) "stdOut")) (ForC 2 (CallProcedure "foo"))) (Seq (Seq Skip (ReadFromChannel (Global "y") "stdIn")) (Seq Skip (ReadFromChannel (Global "z") "stdIn"))))) undefined undefined undefined),("foo",Generated (Seq (ForV (Global "x") (Seq (ForC 2 (PrintToChannel (Times (Var (Global "x")) (Var (Global "y"))) "stdOut")) (ForV (Global "b") (ReadFromChannel (Global "y") "stdIn")))) (Seq (ForV (Global "x") (ForV (Global "y") (ReadFromChannel (Global "b") "lowIn1"))) (Seq (ForV (Global "b") (PrintToChannel (Times (Var (Global "b")) (Var (Global "y"))) "stdOut")) (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "x"))) "stdOut") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "x")))))))) undefined undefined undefined),("main",Generated (ForC 1 (Seq (Seq (Seq (PrintToChannel (Val 0) "stdOut") (Ass (Global "y") (Val 0))) (Seq (Ass (Global "x") (Times (Var (Global "y")) (Var (Global "y")))) (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))) (Seq (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "y"))) "stdOut") (ReadFromChannel (Global "x") "stdIn")) (Seq Skip (SpawnThread 3))))) undefined undefined undefined),("thread3",Generated (ForV (Global "b") (ForC 1 (ForC 2 (ForC 1 (CallProcedure "bar"))))) undefined undefined undefined)])

summaryExample9 :: Program Gr
summaryExample9 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (ForC 2 (If CFalse (Seq (ReadFromChannel (Global "z") "lowIn1") (Ass (Global "z") (Times (Var (Global "z")) (Var (Global "z"))))) (Seq (ReadFromChannel (Global "a") "stdIn") (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "a"))))))) (Seq (Seq (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "x") "stdIn")) (ForC 1 (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "a")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "b")))) (CallProcedure "foo") (ReadFromChannel (Global "x") "lowIn1")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "a")))) (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "b")))) (CallProcedure "foo"))))) undefined undefined undefined),("baz",Generated (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "x")))) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "a")))) (ForV (Global "a") (ForV (Global "c") (ReadFromChannel (Global "y") "stdIn"))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "a")))) (ForV (Global "x") (PrintToChannel (Times (Var (Global "b")) (Var (Global "x"))) "stdOut")) (ForC 1 (CallProcedure "baz")))) (Seq (Seq (Seq Skip (CallProcedure "baz")) (ForC 1 (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (Seq (ForV (Global "x") (PrintToChannel (Times (Var (Global "b")) (Var (Global "x"))) "stdOut")) (Seq (ReadFromChannel (Global "a") "stdIn") (CallProcedure "baz"))))) undefined undefined undefined),("foo",Generated (Seq (Seq (ForC 1 (Seq (ReadFromChannel (Global "c") "lowIn1") (PrintToChannel (Times (Var (Global "c")) (Var (Global "a"))) "stdOut"))) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "a")))) (Seq (ReadFromChannel (Global "b") "stdIn") (CallProcedure "baz")) (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "c"))) "stdOut") (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "x"))))))) (ForV (Global "b") (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (ReadFromChannel (Global "x") "stdIn") (PrintToChannel (Times (Var (Global "x")) (Var (Global "a"))) "stdOut")) (ForC 2 (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "c")))))))) undefined undefined undefined),("main",Generated (Seq (If CFalse (If CFalse (ForC 1 (Ass (Global "x") (Val 0))) (Seq (PrintToChannel (Val (-1)) "stdOut") (ReadFromChannel (Global "z") "stdIn"))) (Seq (Seq (CallProcedure "bar") (PrintToChannel (Val 1) "stdOut")) (ForC 2 Skip))) (Seq (ForC 1 (Seq (Ass (Global "x") (Val (-1))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (Seq (Seq (SpawnThread 2) (SpawnThread 3)) (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") Skip)))) undefined undefined undefined),("thread2",Generated (Seq (Seq (ForV (Global "x") (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (ForC 2 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ReadFromChannel (Global "a") "lowIn1") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")))) (ForV (Global "x") (Seq (Seq (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x")))) Skip) (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "a") "lowIn1"))))) undefined undefined undefined),("thread3",Generated (Seq (ForC 1 (ForV (Global "x") (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")))) (ForC 2 (Seq (Seq (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "y")))) (Ass (Global "c") (Times (Var (Global "z")) (Var (Global "y")))) (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut"))))) undefined undefined undefined)])

summaryExample10 :: Program Gr
summaryExample10 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (If CTrue (ForC 2 (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 17) "stdOut")) (ForC 1 (SpawnThread 2)))) (Seq (Seq (ForC 2 (PrintToChannel (Val 1) "stdOut")) (Seq (CallProcedure "bar") (PrintToChannel (Val 1) "stdOut"))) (Seq (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val 1) "stdOut")) (Seq (ReadFromChannel (Global "b") "stdIn") (Ass (Global "b") (Times (Var (Global "b")) (Var (Global "b")))))))) undefined undefined undefined),("baz",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (Seq (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x")))) Skip) (Seq (CallProcedure "foo") (ReadFromChannel (Global "z") "lowIn1"))) (Seq (ForC 2 (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x"))))) (ForV (Global "x") (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x"))))))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForC 1 (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x"))))) (Seq (ReadFromChannel (Global "c") "lowIn1") (CallProcedure "baz"))) (Seq (Seq (CallProcedure "baz") (CallProcedure "foo")) (Seq (CallProcedure "foo") (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))))) undefined undefined undefined),("foo",Generated (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForC 1 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForC 2 (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (CallProcedure "foo") (ReadFromChannel (Global "b") "lowIn1")))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (CallProcedure "foo") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (ForC 1 (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) Skip (CallProcedure "foo"))))) undefined undefined undefined),("main",Generated (Seq (Seq (Seq (If CFalse (CallProcedure "bar") (ReadFromChannel (Global "b") "stdIn")) (ForC 2 (ReadFromChannel (Global "x") "stdIn"))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (ReadFromChannel (Global "c") "lowIn1")) (Seq (CallProcedure "baz") (CallProcedure "baz")))) (ForC 2 (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (CallProcedure "baz") (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (Seq (Seq (SpawnThread 3) (Ass (Global "c") (Val 0))) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "c")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ReadFromChannel (Global "x") "stdIn") (ReadFromChannel (Global "y") "stdIn")) (Seq Skip (ReadFromChannel (Global "b") "lowIn1")))) (ForV (Global "x") (ForV (Global "c") (Seq (ReadFromChannel (Global "z") "lowIn1") (PrintToChannel (Times (Var (Global "z")) (Var (Global "z"))) "stdOut"))))) undefined undefined undefined),("thread3",Generated (Seq (Seq (ForC 2 (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "c") "stdIn"))) (ForV (Global "c") (Seq Skip (PrintToChannel (Times (Var (Global "c")) (Var (Global "x"))) "stdOut")))) (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (ReadFromChannel (Global "y") "stdIn") (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "c"))))) (ForC 1 (ReadFromChannel (Global "z") "lowIn1"))) (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "x")))) (ForC 2 (Ass (Global "y") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "z")))) (ReadFromChannel (Global "x") "lowIn1") (Ass (Global "y") (Times (Var (Global "c")) (Var (Global "x")))))))) undefined undefined undefined)])

summaryExample11 :: Program Gr
summaryExample11 = toProgram $ GeneratedProgram (Map.fromList [(1,"main")]) (Map.fromList [("baz",Generated (ForC 1 (Seq (Seq (Seq (ReadFromChannel (Global "x") "stdIn") (PrintToChannel (Times (Var (Global "c")) (Var (Global "x"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "c")))) Skip)) (Seq (ForC 1 (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (CallProcedure "baz") (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))))) undefined undefined undefined),("main",Generated (Seq (If CTrue (Seq (Seq (ReadFromChannel (Global "y") "lowIn1") (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))) (ForV (Global "y") (Ass (Global "a") (Times (Var (Global "y")) (Var (Global "y")))))) (ForC 1 (ForC 2 Skip))) (Seq (Seq (Seq (ReadFromChannel (Global "c") "lowIn1") (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c"))))) (ForV (Global "c") Skip)) (Seq (ForV (Global "c") (CallProcedure "baz")) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "b")))) Skip (ReadFromChannel (Global "z") "stdIn"))))) undefined undefined undefined)])

summaryExample12 :: Program Gr
summaryExample12 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (ForV (Global "y") (Seq (ForC 1 (Ass (Global "c") (Times (Var (Global "y")) (Var (Global "y"))))) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "y"))) "stdOut") (ReadFromChannel (Global "b") "lowIn1")))) (Seq (Seq (ForV (Global "y") (CallProcedure "procH")) (Seq (CallProcedure "procF") Skip)) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "y")))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (CallProcedure "procG") Skip) (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut") Skip)))) undefined undefined undefined),("foo",Generated (Seq (Seq (Seq (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "x") "lowIn1")) (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut"))) (Seq (Seq (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "a")))) (ReadFromChannel (Global "c") "stdIn")) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "b") "lowIn1") (CallProcedure "procH")))) (ForV (Global "x") (Seq (Seq (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "a")))) (ReadFromChannel (Global "a") "stdIn")) (ForC 1 (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "a")))))))) undefined undefined undefined),("main",Generated (Seq (Seq (If CFalse (Seq (PrintToChannel (Val 1) "stdOut") (ReadFromChannel (Global "z") "lowIn1")) (Seq (Ass (Global "b") (Val 42)) (ReadFromChannel (Global "x") "lowIn1"))) (Seq (Seq (Ass (Global "a") (Val 17)) Skip) (ForC 1 Skip))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (ForC 2 (ReadFromChannel (Global "z") "lowIn1")) (ForV (Global "a") (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "a")))))) (Seq (Seq (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "a")))) (SpawnThread 2)) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) Skip (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "y")))))))) undefined undefined undefined),("procF",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (ForC 2 (PrintToChannel (Times (Var (Global "y")) (Var (Global "a"))) "stdOut")) (ForV (Global "a") (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))) (ForC 2 (ForV (Global "a") (PrintToChannel (Times (Var (Global "a")) (Var (Global "y"))) "stdOut")))) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (Seq (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "y"))) "stdOut") (CallProcedure "procF")) (ForV (Global "a") (Ass (Global "z") (Times (Var (Global "y")) (Var (Global "a")))))) (Seq (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "a")))) (ReadFromChannel (Global "y") "stdIn") (CallProcedure "procF")) (ForV (Global "a") (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "y")))))))) undefined undefined undefined),("procG",Generated (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (Seq (ForV (Global "a") (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "a")))) (ReadFromChannel (Global "y") "stdIn") (ReadFromChannel (Global "y") "lowIn1"))) (Seq (Seq (ReadFromChannel (Global "c") "lowIn1") (PrintToChannel (Times (Var (Global "c")) (Var (Global "y"))) "stdOut")) (ForC 2 (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y"))))))) (ForC 1 (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "a")))) (ForV (Global "y") (CallProcedure "procG")) (Seq (CallProcedure "procH") (ReadFromChannel (Global "y") "lowIn1"))))) undefined undefined undefined),("procH",Generated (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (ForV (Global "y") (ForC 1 (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "a")))) (Ass (Global "z") (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "x") "stdIn")))) (ForV (Global "a") (Seq (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "y"))) "stdOut")) (ForC 1 (ReadFromChannel (Global "y") "stdIn"))))) undefined undefined undefined),("thread2",Generated (ForV (Global "a") (ForC 2 (Seq (ForC 2 (CallProcedure "bar")) (ForC 2 (SpawnThread 3))))) undefined undefined undefined),("thread3",Generated (Seq (Seq (ForV (Global "a") (Seq (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "a")))) (CallProcedure "procF"))) (Seq (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a")))) (CallProcedure "procH")) (ForC 2 (CallProcedure "foo")))) (Seq (ForC 1 (ForC 2 (CallProcedure "procH"))) (Seq (Seq (CallProcedure "bar") Skip) (Seq (Ass (Global "z") (Times (Var (Global "y")) (Var (Global "a")))) (ReadFromChannel (Global "b") "lowIn1"))))) undefined undefined undefined)])

summaryExample13 :: Program Gr
summaryExample13 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (Seq (Seq (CallProcedure "bar") (ReadFromChannel (Global "x") "lowIn1")) (Seq (ReadFromChannel (Global "b") "stdIn") (CallProcedure "baz"))) (Seq (ForC 1 (PrintToChannel (Times (Var (Global "c")) (Var (Global "x"))) "stdOut")) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "b"))) "stdOut") (PrintToChannel (Times (Var (Global "c")) (Var (Global "b"))) "stdOut")))) (Seq (Seq (ForV (Global "c") (CallProcedure "bar")) (Seq (CallProcedure "procH") (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut"))) (ForC 1 (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (ReadFromChannel (Global "c") "lowIn1"))))) undefined undefined undefined),("baz",Generated (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) Skip (ReadFromChannel (Global "x") "stdIn")) (ForV (Global "c") Skip)) (Seq (Seq (CallProcedure "procH") (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c"))))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "x") (Times (Var (Global "b")) (Var (Global "c")))) (ReadFromChannel (Global "b") "lowIn1")))) (Seq (Seq (Seq (ReadFromChannel (Global "a") "stdIn") (ReadFromChannel (Global "x") "stdIn")) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "c")))) (CallProcedure "baz") Skip)) (Seq (ForV (Global "c") (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "a"))))) (ForV (Global "a") (CallProcedure "procG"))))) undefined undefined undefined),("foo",Generated (Seq (ForV (Global "c") (ForC 1 (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Ass (Global "b") (Times (Var (Global "c")) (Var (Global "c")))) (ReadFromChannel (Global "x") "stdIn")))) (Seq (Seq (Seq (CallProcedure "procG") (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut")) (ForV (Global "c") (ReadFromChannel (Global "b") "stdIn"))) (ForV (Global "c") (Seq (ReadFromChannel (Global "x") "lowIn1") (Ass (Global "z") (Times (Var (Global "x")) (Var (Global "c")))))))) undefined undefined undefined),("main",Generated (Seq (Seq (Seq (If CTrue (PrintToChannel (Val (-1)) "stdOut") (Ass (Global "a") (Val 17))) (If CFalse (PrintToChannel (Val 42) "stdOut") (CallProcedure "procG"))) (Seq (Seq (PrintToChannel (Val 17) "stdOut") (PrintToChannel (Val 0) "stdOut")) (ForC 1 (ReadFromChannel (Global "c") "lowIn1")))) (ForC 1 (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (Ass (Global "a") (Times (Var (Global "c")) (Var (Global "c")))) (CallProcedure "foo")) (Seq (SpawnThread 2) (ReadFromChannel (Global "c") "lowIn1"))))) undefined undefined undefined),("procG",Generated (If CTrue (Seq (Seq (Seq (PrintToChannel (Val 42) "stdOut") (CallProcedure "procH")) (Seq (ReadFromChannel (Global "y") "lowIn1") (ReadFromChannel (Global "c") "lowIn1"))) (ForV (Global "c") (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "y")))) (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "y")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "y"))) "stdOut")))) (Seq (Seq (ForC 2 (Ass (Global "z") (Val 0))) (Seq (CallProcedure "procG") (Ass (Global "c") (Times (Var (Global "z")) (Var (Global "z")))))) (ForV (Global "z") (ForC 1 (ReadFromChannel (Global "c") "lowIn1"))))) undefined undefined undefined),("procH",Generated (Seq (Seq (Seq (Seq (Ass (Global "y") (Val 0)) (ReadFromChannel (Global "a") "lowIn1")) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "y")))) Skip Skip)) (Seq (ForC 2 (PrintToChannel (Times (Var (Global "y")) (Var (Global "a"))) "stdOut")) (Seq (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a")))) (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a"))))))) (ForC 1 (ForC 1 (Seq (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "c")))) Skip)))) undefined undefined undefined),("thread2",Generated (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (ForC 1 (Seq (Seq Skip Skip) (Seq (ReadFromChannel (Global "y") "lowIn1") (CallProcedure "foo")))) (ForV (Global "c") (Seq (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (SpawnThread 3) (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut")) (ForC 1 (ReadFromChannel (Global "z") "lowIn1"))))) undefined undefined undefined),("thread3",Generated (Seq (Seq (Seq (ForC 2 (Ass (Global "c") (Times (Var (Global "c")) (Var (Global "c"))))) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (ReadFromChannel (Global "c") "lowIn1"))) (If (Leq (Val 0) (Times (Var (Global "c")) (Var (Global "c")))) (Seq (CallProcedure "baz") (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut")) (Seq Skip (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut")))) (ForV (Global "c") (Seq (ForC 1 (CallProcedure "foo")) (Seq (CallProcedure "bar") (ReadFromChannel (Global "x") "lowIn1"))))) undefined undefined undefined)])



summaryExample14 :: Program Gr
summaryExample14 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "y")))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "y")))) (ForC 1 (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "y"))))) (ForV (Global "x") (CallProcedure "procG"))) (ForC 1 (ForV (Global "y") (ReadFromChannel (Global "b") "lowIn1")))) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "x")))) (Seq (Seq (ReadFromChannel (Global "a") "lowIn1") (CallProcedure "procG")) (Seq (Ass (Global "b") (Times (Var (Global "y")) (Var (Global "y")))) (ReadFromChannel (Global "y") "stdIn"))) (Seq (Seq (CallProcedure "baz") (ReadFromChannel (Global "x") "lowIn1")) (Seq (CallProcedure "foo") (Ass (Global "y") (Times (Var (Global "y")) (Var (Global "x")))))))) undefined undefined undefined),("baz",Generated (Seq (ForC 1 (Seq (Seq (PrintToChannel (Val 42) "stdOut") (Ass (Global "x") (Val (-1)))) (ForC 1 (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "x"))))))) (Seq (Seq (Seq (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "a")))) (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x"))))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (PrintToChannel (Times (Var (Global "c")) (Var (Global "a"))) "stdOut") (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "a")))))) (Seq (Seq (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "c")))) (ReadFromChannel (Global "b") "lowIn1")) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") (ReadFromChannel (Global "c") "lowIn1"))))) undefined undefined undefined),("foo",Generated (ForC 2 (Seq (ForV (Global "x") (ForC 1 (ReadFromChannel (Global "b") "lowIn1"))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (Seq (CallProcedure "procH") (ReadFromChannel (Global "b") "stdIn")) (Seq (ReadFromChannel (Global "b") "lowIn1") Skip)))) undefined undefined undefined),("main",Generated (Seq (Seq (If CFalse (Seq (SpawnThread 3) (CallProcedure "baz")) (Seq (PrintToChannel (Val 42) "stdOut") (ReadFromChannel (Global "y") "lowIn1"))) (Seq (ForC 1 (SpawnThread 2)) (Seq (CallProcedure "procH") (PrintToChannel (Val 42) "stdOut")))) (Seq (Seq (ForC 1 (ReadFromChannel (Global "x") "stdIn")) (Seq (ReadFromChannel (Global "y") "stdIn") (PrintToChannel (Times (Var (Global "y")) (Var (Global "x"))) "stdOut"))) (Seq (Seq (Ass (Global "x") (Times (Var (Global "x")) (Var (Global "y")))) (CallProcedure "bar")) (ForC 1 (CallProcedure "procF"))))) undefined undefined undefined),("procF",Generated (ForC 2 (Seq (ForV (Global "x") (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut") (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut"))) (If (Leq (Val 0) (Times (Var (Global "y")) (Var (Global "y")))) (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (Ass (Global "c") (Times (Var (Global "x")) (Var (Global "x"))))) (ForV (Global "y") Skip)))) undefined undefined undefined),("procG",Generated (Seq (Seq (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) Skip (CallProcedure "procH")) (ForV (Global "x") (Ass (Global "b") (Times (Var (Global "x")) (Var (Global "x")))))) (Seq (Seq (ReadFromChannel (Global "x") "lowIn1") (ReadFromChannel (Global "x") "lowIn1")) (ForV (Global "x") (CallProcedure "procG")))) (Seq (Seq (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (CallProcedure "procH") (ReadFromChannel (Global "x") "lowIn1")) (ForC 1 (ReadFromChannel (Global "b") "lowIn1"))) (ForV (Global "b") (ForV (Global "x") (ReadFromChannel (Global "z") "stdIn"))))) undefined undefined undefined),("procH",Generated (ForC 2 (Seq (Seq (Seq (Ass (Global "c") (Val 0)) (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "c"))))) (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "c"))) "stdOut") (CallProcedure "procH"))) (ForC 1 (Seq (CallProcedure "procH") (ReadFromChannel (Global "x") "stdIn"))))) undefined undefined undefined),("thread2",Generated (Seq (Seq (Seq (Seq (PrintToChannel (Val 0) "stdOut") (ReadFromChannel (Global "x") "stdIn")) (Seq (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (CallProcedure "procH"))) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (ForV (Global "x") (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut")) (Seq Skip (CallProcedure "baz")))) (Seq (Seq (ForV (Global "x") (CallProcedure "procG")) (If (Leq (Val 0) (Times (Var (Global "x")) (Var (Global "x")))) (PrintToChannel (Times (Var (Global "x")) (Var (Global "x"))) "stdOut") (CallProcedure "foo"))) (ForC 1 (Seq (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "x")))) (Ass (Global "a") (Times (Var (Global "x")) (Var (Global "a")))))))) undefined undefined undefined),("thread3",Generated (ForC 1 (Seq (If CTrue (Seq (Ass (Global "a") (Val 0)) (CallProcedure "procH")) (Seq (ReadFromChannel (Global "b") "stdIn") (ReadFromChannel (Global "c") "stdIn"))) (Seq (ForC 2 (PrintToChannel (Val 0) "stdOut")) (If CTrue (ReadFromChannel (Global "c") "stdIn") (Ass (Global "c") (Val 0)))))) undefined undefined undefined)])


summaryExample15 :: Program Gr
summaryExample15 = toProgram $ GeneratedProgram (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")]) (Map.fromList [("bar",Generated (ForC 1 (ForV (Global "a") (Seq (Seq (CallProcedure "bar") (ReadFromChannel (Global "z") "lowIn1")) (Seq (ReadFromChannel (Global "y") "lowIn1") Skip)))) undefined undefined undefined),("baz",Generated (Seq (Seq (ForC 2 (If CTrue (ReadFromChannel (Global "b") "lowIn1") (ReadFromChannel (Global "a") "lowIn1"))) (Seq (If CFalse Skip (Ass (Global "c") (Val 42))) (Seq (CallProcedure "procF") (ReadFromChannel (Global "a") "lowIn1")))) (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (SpawnThread 2)) (Seq (ReadFromChannel (Global "a") "lowIn1") (CallProcedure "procH"))) (Seq (Seq (ReadFromChannel (Global "a") "lowIn1") (ReadFromChannel (Global "z") "stdIn")) (ForV (Global "z") (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "a")))))))) undefined undefined undefined),("foo",Generated (If CTrue (Seq (If CFalse (ForC 2 (PrintToChannel (Val (-1)) "stdOut")) (ForC 1 Skip)) (Seq (Seq (CallProcedure "baz") (PrintToChannel (Val 0) "stdOut")) (Seq (CallProcedure "procF") (Ass (Global "c") (Val 17))))) (Seq (Seq (If CTrue (ReadFromChannel (Global "a") "stdIn") (Ass (Global "a") (Val 0))) (Seq Skip (Ass (Global "z") (Times (Var (Global "a")) (Var (Global "a")))))) (Seq (ForV (Global "z") (ReadFromChannel (Global "c") "lowIn1")) (Seq (CallProcedure "procF") (CallProcedure "procF"))))) undefined undefined undefined),("main",Generated (If CFalse (Seq (Seq (Seq Skip (PrintToChannel (Val 1) "stdOut")) (ForC 2 (PrintToChannel (Val 0) "stdOut"))) (ForC 2 (Seq (Ass (Global "z") (Val 1)) (SpawnThread 3)))) (If CTrue (Seq (ForC 2 (CallProcedure "foo")) (Seq Skip (Ass (Global "c") (Val (-1))))) (Seq (Seq (Ass (Global "c") (Val (-1))) Skip) (Seq (PrintToChannel (Times (Var (Global "c")) (Var (Global "c"))) "stdOut") Skip)))) undefined undefined undefined),("procF",Generated (Seq (Seq (ForC 1 (Seq (ReadFromChannel (Global "b") "stdIn") (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))) (Seq (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut") (Ass (Global "b") (Times (Var (Global "b")) (Var (Global "b"))))) (ForV (Global "b") (ReadFromChannel (Global "y") "lowIn1")))) (Seq (ForV (Global "b") (If (Leq (Val 0) (Times (Var (Global "b")) (Var (Global "b")))) (Ass (Global "c") (Times (Var (Global "b")) (Var (Global "b")))) (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut"))) (ForV (Global "b") (Seq (PrintToChannel (Times (Var (Global "b")) (Var (Global "b"))) "stdOut") (ReadFromChannel (Global "a") "lowIn1"))))) undefined undefined undefined),("procG",Generated (Seq (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (ForC 1 (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))) (ForC 1 (ForV (Global "a") (CallProcedure "bar")))) (Seq (ForC 1 (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (ReadFromChannel (Global "b") "lowIn1") (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a")))))) (ForC 2 (Seq (Ass (Global "y") (Times (Var (Global "a")) (Var (Global "a")))) (ReadFromChannel (Global "y") "stdIn"))))) undefined undefined undefined),("procH",Generated (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (ForC 1 (CallProcedure "procH")) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (CallProcedure "procG") (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))) (Seq (ForV (Global "a") (ReadFromChannel (Global "b") "lowIn1")) (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (ReadFromChannel (Global "z") "lowIn1")))) (ForV (Global "a") (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (Seq (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut") (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut")) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a")))) (Ass (Global "b") (Times (Var (Global "a")) (Var (Global "a")))) (CallProcedure "procH"))))) undefined undefined undefined),("thread2",Generated (ForV (Global "a") (Seq (ForC 1 (Seq (Ass (Global "c") (Times (Var (Global "a")) (Var (Global "a")))) (PrintToChannel (Times (Var (Global "a")) (Var (Global "a"))) "stdOut"))) (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "c")))) (ForC 2 (Ass (Global "x") (Times (Var (Global "c")) (Var (Global "c"))))) (ForV (Global "c") (ReadFromChannel (Global "y") "lowIn1"))))) undefined undefined undefined),("thread3",Generated (ForV (Global "z") (Seq (Seq (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "z")))) (ReadFromChannel (Global "y") "stdIn") (ReadFromChannel (Global "b") "lowIn1")) (Seq (ReadFromChannel (Global "b") "stdIn") (Ass (Global "a") (Times (Var (Global "b")) (Var (Global "z")))))) (ForV (Global "b") (If (Leq (Val 0) (Times (Var (Global "z")) (Var (Global "b")))) Skip (ReadFromChannel (Global "c") "stdIn"))))) undefined undefined undefined)])



interestingResumtionVsTimingAtUsed =
  IntraGeneratedProgram
    (Map.fromList [(1,"main"),(2,"thread2"),(3,"thread3")] )
    (Map.fromList [("main",Generated (Seq (If CTrue
                                               (Seq (ReadFromChannel (Global "z") "stdIn") Skip)
                                           {- else -}
                                               (If CFalse
                                                   (Ass (Global "y") (Val 42))
                                               {- else -}
                                                   (PrintToChannel (Val 42) "stdOut")))
                                          (If CFalse
                                               (Seq (PrintToChannel (Val 0) "stdOut")
                                                    (SpawnThread 3))
                                          {- else -}
                                               (ForC 2 (SpawnThread 2))))
                    undefined undefined undefined),
                   ("thread2",Generated (ForC 1
                                          (If CTrue
                                              (Seq (Seq (ReadFromChannel (Global "y") "lowIn1") Skip)
                                                   (Seq (PrintToChannel (Times (Var (Global "y")) (Var (Global "y"))) "stdOut")
                                                        (Ass (Global "a") (Times (Var (Global "y")) (Var (Global "y"))))))
                                          {- else -}
                                              (Seq (Seq (PrintToChannel (Val 42) "stdOut")
                                                        (ReadFromChannel (Global "a") "stdIn"))
                                                        (If (Leq (Val 0) (Times (Var (Global "a")) (Var (Global "a"))))
                                                            (Ass (Global "a") (Times (Var (Global "a")) (Var (Global "a"))))
                                                        {- else -}
                                                            (ReadFromChannel (Global "b") "stdIn")))))
                    undefined undefined undefined),
                   ("thread3",Generated (Seq (Seq (Ass (Global "c") (Val 17))
                                             (Ass (Global "z") (Times (Var (Global "c")) (Var (Global "c")))))
                                             (ForC 1 (Ass (Global "x")
                                                 (Times (Var (Global "c")) (Var (Global "c")))))) undefined undefined undefined)]  )


exampleTimingDepInterestingTwoFinger :: DynGraph gr => gr () ()
exampleTimingDepInterestingTwoFinger = mkGraph [(-36,()),(-29,()),(-19,()),(39,()),(40,())] [(-36,-29,()),(-36,39,()),(-36,39,()),(-29,-19,()),(-19,39,()),(39,-19,()),(40,-36,()),(40,-29,()),(40,-19,()),(40,39,())]

exampleTimingDepInterestingTwoFinger2 :: DynGraph gr => gr () ()
exampleTimingDepInterestingTwoFinger2 = mkGraph [(-10,()),(-9,()),(-7,()),(-5,()),(13,()),(14,()),(15,()),(21,())] [(-10,15,()),(-10,15,()),(-9,-5,()),(-7,-10,()),(-7,13,()),(-7,13,()),(-7,14,()),(-5,-9,()),(13,15,()),(14,-5,()),(15,-9,()),(21,-10,()),(21,-9,()),(21,-7,()),(21,-5,()),(21,13,()),(21,14,()),(21,15,())]


exampleTimingDepInterestingTwoFinger3 :: DynGraph gr => gr () ()
exampleTimingDepInterestingTwoFinger3 = mkGraph [(-38,()),(-19,()),(-8,()),(24,()),(28,()),(41,()),(54,()),(58,())] [(-38,24,()),(-19,24,()),(-8,28,()),(-8,41,()),(-8,41,()),(24,54,()),(28,-19,()),(41,-38,()),(58,-38,()),(58,-19,()),(58,-8,()),(58,24,()),(58,28,()),(58,41,()),(58,54,())]

exampleTimingDepInterestingTwoFinger4 :: DynGraph gr => gr () ()
exampleTimingDepInterestingTwoFinger4 = mkGraph [(-12,()),(-10,()),(-4,()),(-2,()),(5,()),(19,()),(22,()),(25,())] [(-12,-2,()),(-10,-4,()),(-4,-10,()),(-2,-10,()),(5,-12,()),(5,22,()),(19,-10,()),(22,-4,()),(22,19,()),(25,-12,()),(25,-10,()),(25,-4,()),(25,-2,()),(25,5,()),(25,19,()),(25,22,())]

exampleTimingDepInterestingTwoFinger42 :: DynGraph gr => gr () ()
exampleTimingDepInterestingTwoFinger42 = mkGraph [(-12,()),(-10,()),(-4,()),(-2,()),(5,()),(19,()),(22,()),(25,())] [(-12,-2,()),(-10,-4,()),(-4,-10,()),(-2,-10,()),(5,-12,()),(5,22,()),(19,-10,()),(22,-4,()),(22,19,()),(25,5,()),(25,22,())]

exampleTimingDepInterestingTwoFinger5 :: DynGraph gr => gr () ()
exampleTimingDepInterestingTwoFinger5 = mkGraph [(-16,()),(-9,()),(1,()),(3,()),(6,()),(14,()),(21,())] [(-16,-9,()),(-16,1,()),(-16,1,()),(-16,3,()),(-9,6,()),(1,6,()),(3,14,()),(6,-9,()),(14,-9,()),(21,-16,()),(21,-9,()),(21,1,()),(21,3,()),(21,6,()),(21,14,())]


exampleTimingDepInterestingTwoFinger6 :: DynGraph gr => gr () ()
exampleTimingDepInterestingTwoFinger6 = mkGraph [(-122,()),(-73,()),(-20,()),(83,()),(111,()),(122,()),(135,())] [(-122,122,()),(-73,83,()),(-73,111,()),(-20,122,()),(83,-122,()),(83,-20,()),(122,-20,()),(135,-122,()),(135,-73,()),(135,-20,()),(135,83,()),(135,111,()),(135,122,())]


exampleTimingDepCorrectionInterestingSimon1 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInterestingSimon1 =  mkGraph [(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,()),(8,()),(9,()),(10,()),(11,()),(12,()),(13,())] [(1,2,()),(1,3,()),(2,4,()),(2,7,()),(3,5,()),(3,6,()),(4,5,()),(5,7,()),(5,8,()),(6,8,()),(7,9,()),(8,9,()),(8,10,()),(9,11,()),(10,13,()),(11,12,()),(12,13,())]


exampleTimingDepCorrectionInterestingSimon2 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInterestingSimon2 = mkGraph [(1,()),(2,()),(3,()),(4,()),(5,()),(6,()),(7,()),(8,()),(9,()),(10,()),(11,()),(12,()),(13,()),(14,()),(15,()),(16,()),(17,()),(18,())] [(1,2,()),(2,3,()),(3,4,()),(4,10,()),(4,11,()),(1,5,()),(1,7,()),(5,6,()),(7,12,()),(7,14,()),(8,9,()),(9,10,()),(10,18,()),(11,12,()),(12,18,()),(13,15,()),(14,15,()),(15,16,()),(16,17,()),(17,18,()),(6,8,()), (6,13,())]


exampleTimingDepCorrectionInteresting3 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting3 = mkGraph [(-29,()),(-21,()),(6,()),(7,()),(10,()),(11,()),(18,()),(19,()),(23,()),(24,())] [(-29,7,()),(-29,7,()),(-21,11,()),(6,18,()),(7,11,()),(7,11,()),(10,-29,()),(10,6,()),(10,23,()),(11,-21,()),(18,-29,()),(18,11,()),(18,19,()),(19,-21,()),(23,7,()),(24,-29,()),(24,-21,()),(24,6,()),(24,7,()),(24,10,()),(24,11,()),(24,18,()),(24,19,()),(24,23,())]

exampleTimingDepCorrectionInteresting4 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting4 = mkGraph [(-21,()),(10,()),(15,()),(16,()),(28,()),(30,())] [(-21,28,()),(10,-21,()),(10,15,()),(10,15,()),(15,28,()),(16,-21,()),(16,10,()),(28,15,()),(30,-21,()),(30,10,()),(30,15,()),(30,16,()),(30,28,())]

exampleTimingDepCorrectionInteresting5 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting5 = mkGraph [(-13,()),(-10,()),(11,()),(20,()),(21,())] [(-13,11,()),(-13,20,()),(-10,-13,()),(-10,11,()),(-10,11,()),(11,-10,()),(11,20,()),(20,-10,()),(21,-13,()),(21,-10,()),(21,11,()),(21,20,())]

exampleTimingDepCorrectionInteresting6 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting6 = mkGraph [(-14,()),(-11,()),(6,()),(11,()),(26,())] [(-14,-11,()),(-14,11,()),(-11,6,()),(6,11,()),(11,-14,()),(26,-14,()),(26,-11,()),(26,6,()),(26,11,())]

exampleTimingDepCorrectionInteresting7 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting7 = mkGraph [(-13,()),(-12,()),(-4,()),(1,()),(4,()),(12,()),(13,())] [(-13,-4,()),(-12,-4,()),(-12,12,()),(-4,4,()),(1,-13,()),(1,-4,()),(4,4,()),(12,1,()),(13,-13,()),(13,-12,()),(13,-4,()),(13,1,()),(13,4,()),(13,12,())]

exampleTimingDepCorrectionInteresting8 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting8 = mkGraph [(-18,()),(-15,()),(-8,()),(5,()),(16,()),(18,()),(20,()),(21,())] [(-18,18,()),(-18,20,()),(-15,20,()),(-8,18,()),(5,16,()),(5,20,()),(16,-18,()),(16,-15,()),(16,-8,()),(18,-15,()),(18,20,()),(20,-8,()),(21,-18,()),(21,-15,()),(21,-8,()),(21,5,()),(21,16,()),(21,18,()),(21,20,())]


exampleTimingDepCorrectionInteresting9 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting9 = mkGraph [(1,()),(4,()),(5,())] [(1,4,()),(4,1,()),(5,1,()),(5,4,())]

exampleTimingDepCorrectionInteresting10 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting10 = mkGraph [(-15,()),(-11,()),(-10,()),(-6,()),(-4,()),(-1,()),(0,()),(2,()),(3,()),(5,()),(11,()),(15,()),(16,())] [(-15,15,()),(-11,-15,()),(-10,0,()),(-10,11,()),(-10,15,()),(-6,-15,()),(-1,-6,()),(-1,5,()),(0,-1,()),(3,-10,()),(5,-6,()),(5,15,()),(11,-15,()),(11,-6,()),(11,-4,()),(15,-15,()),(15,-11,()),(16,-15,()),(16,-11,()),(16,-10,()),(16,-6,()),(16,-4,()),(16,-1,()),(16,0,()),(16,2,()),(16,3,()),(16,5,()),(16,11,()),(16,15,())] -- Set.fromList [-11,-10]


exampleTimingDepCorrectionInteresting11 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting11 = mkGraph [(-33,()),(-30,()),(-28,()),(-24,()),(-22,()),(-21,()),(-18,()),(-16,()),(-13,()),(-9,()),(-8,()),(-6,()),(6,()),(10,()),(12,()),(17,()),(22,()),(24,()),(25,()),(33,()),(34,())] [(-30,6,()),(-28,-30,()),(-22,-33,()),(-21,17,()),(-18,-28,()),(-13,12,()),(-9,22,()),(-6,25,()),(6,24,()),(22,-30,()),(22,-18,()),(22,-18,()),(22,24,()),(24,-18,()),(25,-24,()),(25,33,()),(33,-33,()),(33,22,()),(34,-33,()),(34,-30,()),(34,-28,()),(34,-24,()),(34,-22,()),(34,-21,()),(34,-18,()),(34,-16,()),(34,-13,()),(34,-9,()),(34,-8,()),(34,-6,()),(34,6,()),(34,10,()),(34,12,()),(34,17,()),(34,22,()),(34,24,()),(34,25,()),(34,33,())] -- ,fromList [-30,-16,6],fromList [-30,-16,6,25,33,34],fromList [-30,-16,6,22,25,33,34])


exampleTimingDepCorrectionInteresting11Simple :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting11Simple = mkGraph [(-30,()),(6,()),(-18,()),(22,()),(24,())] [(-30,6,()),(24,-18,()),(-18,-30,()),(6,24,()),(22,-30,()),(22,-18,()),(22,24,())] -- ,fromList [-30,6]

exampleTimingDepCorrectionInteresting11Simple2 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting11Simple2 = mkGraph [(-30,()),(6,()),(22,()),(24,())] [(-30,6,()),(24, -30, ()),(6,24,()),(22,-30,()),(22,24,())]


exampleTimingDepCorrectionInteresting11Simple3 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting11Simple3 = mkGraph (fmap (\(n,()) -> (f n, ())) [(-30,()),(6,()),(-18,()),(22,()),(24,())]) (fmap (\(n,m,()) -> (f n, f m, ()))  [(-30,6,()),(24,-18,()),(-18,-30,()),(6,24,()),(22,-30,()),(22,24,())])
  where f   22  = 0
        f (-30) = 1
        f    6  = 2
        f   24  = -1
        f (-18) = -2


-- exampleTimingDepCorrectionInteresting11Simple :: DynGraph gr => gr () ()
-- exampleTimingDepCorrectionInteresting11Simple = mkGraph [(-30,()),(-28,()),(-18,()),(6,()),(22,()),(24,())] [(-30,6,()),(-28,-30,()),(-18,-28,()),(6,24,()),(22,-30,()),(22,-18,()),(22,-18,()),(22,24,()),(24,-18,())] -- ,fromList [-30,6]

exampleTimingDepCorrectionInteresting12 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting12 = mkGraph [(-10,()),(-1,()),(2,()),(4,()),(11,()),(12,())] [(-10,2,()),(-1,4,()),(2,11,()),(4,-10,()),(11,-1,()),(11,4,()),(12,-10,()),(12,-1,()),(12,2,()),(12,4,()),(12,11,())]


exampleTimingDepCorrectionInteresting13 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting13 = mkGraph [(-29,()),(-18,()),(-17,()),(-14,()),(-5,()),(0,()),(23,()),(30,()),(31,())] [(-18,-5,()),(-17,-18,()),(-17,-5,()),(-14,30,()),(-5,-14,()),(-5,23,()),(0,-18,()),(0,0,()),(0,0,()),(23,-18,()),(30,23,()),(31,-29,()),(31,-18,()),(31,-17,()),(31,-14,()),(31,-5,()),(31,0,()),(31,23,()),(31,30,())]

exampleTimingDepCorrectionInteresting14 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting14 = mkGraph [(-22,()),(-19,()),(-17,()),(-2,()),(1,()),(3,()),(4,()),(6,()),(7,()),(10,()),(11,()),(16,()),(18,()),(23,()),(24,())] [(-22,16,()),(-19,7,()),(-17,-2,()),(-2,4,()),(4,7,()),(7,-17,()),(10,3,()),(11,-19,()),(11,7,()),(16,-2,()),(18,3,()),(23,23,()),(24,-22,()),(24,-19,()),(24,-17,()),(24,-2,()),(24,1,()),(24,3,()),(24,4,()),(24,6,()),(24,7,()),(24,10,()),(24,11,()),(24,16,()),(24,18,()),(24,23,())]

exampleTimingDepCorrectionInteresting15 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting15 = mkGraph [(-4,()),(-3,()),(-2,()),(0,()),(4,()),(6,()),(9,()),(10,())] [(-4,-2,()),(-2,9,()),(-2,9,()),(0,-4,()),(0,9,()),(4,-2,()),(4,-2,()),(6,0,()),(9,-4,()),(9,4,()),(10,-4,()),(10,-3,()),(10,-2,()),(10,0,()),(10,4,()),(10,6,()),(10,9,())]


exampleTimingDepCorrectionInteresting16 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting16 = mkGraph [(-12,()),(-7,()),(-6,()),(-5,()),(1,()),(3,()),(10,()),(13,()),(14,()),(15,())] [(-12,10,()),(-7,14,()),(-6,-7,()),(-5,13,()),(1,-6,()),(3,-6,()),(3,1,()),(3,1,()),(10,13,()),(13,-6,()),(13,1,()),(13,3,()),(14,-5,()),(15,-12,()),(15,-7,()),(15,-6,()),(15,-5,()),(15,1,()),(15,3,()),(15,10,()),(15,13,()),(15,14,())] -- (Set.fromList [-12,-7,14])


exampleTimingDepCorrectionInteresting17 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting17 = mkGraph [(-7,()),(-5,()),(-4,()),(4,()),(6,()),(11,()),(12,())] [(-7,6,()),(-5,-7,()),(-5,-4,()),(-5,4,()),(-4,-7,()),(-4,6,()),(4,-7,()),(4,-4,()),(6,4,()),(11,-4,()),(11,4,()),(12,-7,()),(12,-5,()),(12,-4,()),(12,4,()),(12,6,()),(12,11,())] -- Set.fromList [6]


exampleTimingDepCorrectionInteresting18 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting18 = mkGraph [(-9,()),(-2,()),(-1,()),(0,()),(1,())] [(-9,-1,()),(-9,0,()),(-9,0,()),(-2,-9,()),(-2,0,()),(-1,0,()),(0,-1,()),(0,-1,()),(0,-1,()),(1,-9,()),(1,-2,()),(1,-1,()),(1,0,())]
  where cost = Map.fromList [((-9,-1),10),((-9,0),18),((-2,-9),8),((-2,0),26),((-1,0),8),((0,-1),15),((1,-9),16),((1,-2),28),((1,-1),4),((1,0),1)]

exampleTimingDepCorrectionInteresting18' :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting18' = mkGraph [(-9,()),(-2,()),(-1,()),(0,()),(1,())] [(-9,-1,()),(-9,0,()),(-2,-9,()),(-2,0,()),(-1,0,()),(0,-1,()),(1,-9,()),(1,-2,()),(1,-1,()),(1,0,())]
  where cost = Map.fromList [((-9,-1),1),((-9,0),2),((-2,-9),1),((-2,0),3),((-1,0),1),((0,-1),1),((1,-9),1),((1,-2),1),((1,-1),1),((1,0),1)]


exampleTimingDepCorrectionInteresting18''' :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting18''' = mkGraph [(-9,()),(-2,()),(-1,()),(0,())] [(-9,-1,()),(-9,0,()),(-2,-9,()),(-2,0,()),(-1,0,()),(0,-1,())]
  where cost = Map.fromList [((-9,-1),1),((-9,0),2),((-2,-9),1),((-2,0),3),((-1,0),1),((0,-1),1)]


exampleTimingDepCorrectionInteresting18'' :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting18'' = mkGraph [(-9,()),(-99,()),(-2,()),(-22,()),(-222,()),(-1,()),(0,()),(1,())] [(-9,-99,()),(-99,0,()),(-9,-1,()),(-2,-22,()),(-22,-222,()), (-222,0,()),(-2,-9,()),(-1,0,()),(0,-1,()),(1,-9,()),(1,-2,()),(1,-1,()),(1,0,())]

exampleTimingDepCorrectionInteresting18'''' :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting18'''' = mkGraph [(-9,()),(-99,()),(-2,()),(-22,()),(-222,()),(-1,()),(0,())] [(-9,-99,()),(-99,0,()),(-9,-1,()),(-2,-22,()),(-22,-222,()), (-222,0,()),(-2,-9,()),(-1,0,()),(0,-1,())]




exampleTimingDepCorrectionInteresting19 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting19 = mkGraph [(-22,()),(-21,()),(-18,()),(-16,()),(-5,()),(1,()),(16,()),(21,())] [(-22,-16,()),(-21,-22,()),(-21,16,()),(-18,1,()),(-18,16,()),(-16,-16,()),(-5,-16,()),(1,16,()),(16,-16,()),(16,-5,()),(21,-22,()),(21,-21,()),(21,-18,()),(21,-16,()),(21,-5,()),(21,1,()),(21,16,())]
  where cost =  Map.fromList [((-22,-16),7),((-21,-22),21),((-21,16),4),((-18,1),13),((-18,16),22),((-16,-16),1),((-5,-16),9),((1,16),7),((16,-16),7),((16,-5),14),((21,-22),14),((21,-21),1),((21,-18),4),((21,-16),22),((21,-5),1),((21,1),11),((21,16),24)]


exampleTimingDepCorrectionInteresting20 :: DynGraph gr => gr () ()
exampleTimingDepCorrectionInteresting20 = mkGraph [(-19,()),(-18,()),(-11,()),(-10,()),(-6,()),(-2,()),(-1,()),(15,()),(16,())] [(-19,-6,()),(-18,-6,()),(-11,-10,()),(-6,-18,()),(-2,-1,()),(-2,15,()),(-1,-18,()),(-1,-6,()),(15,-1,()),(16,-19,()),(16,-18,()),(16,-11,()),(16,-10,()),(16,-6,()),(16,-2,()),(16,-1,()),(16,15,())]
  where cost = Map.fromList [((-19,-6),19),((-18,-6),27),((-11,-10),10),((-6,-18),9),((-2,-1),26),((-2,15),32),((-1,-18),2),((-1,-6),29),((15,-1),30),((16,-19),13),((16,-18),10),((16,-11),19),((16,-10),30),((16,-6),25),((16,-2),20),((16,-1),3),((16,15),13)]


exampleTimingWorklist :: DynGraph gr => gr () ()
exampleTimingWorklist = mkGraph [(-168,()),(-135,()),(-130,()),(-122,()),(-36,()),(-22,()),(26,()),(35,()),(65,()),(66,()),(67,()),(68,()),(72,()),(137,()),(180,()),(189,()),(236,()),(253,()),(257,()),(258,()),(260,()),(265,())] [(-168,258,()),(-135,-130,()),(-130,260,()),(-122,35,()),(-36,253,()),(-22,-36,()),(-22,180,()),(26,-22,()),(26,189,()),(35,72,()),(65,66,()),(66,68,()),(67,-122,()),(68,137,()),(72,26,()),(137,67,()),(180,-168,()),(180,236,()),(189,-135,()),(189,257,()),(236,258,()),(253,258,()),(258,189,()),(260,65,()),(265,-168,()),(265,-135,()),(265,-130,()),(265,-122,()),(265,-36,()),(265,-22,()),(265,26,()),(265,35,()),(265,65,()),(265,66,()),(265,67,()),(265,68,()),(265,72,()),(265,137,()),(265,180,()),(265,189,()),(265,236,()),(265,253,()),(265,257,()),(265,258,()),(265,260,())]



isinkdomTwoFingerExample1 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample1 = mkGraph [(-46,()),(-45,()),(-33,()),(-29,()),(-16,()),(-12,()),(-10,()),(-9,()),(3,()),(7,()),(8,()),(31,()),(41,()),(42,()),(44,()),(45,())] [(-46,-33,()),(-46,-9,()),(-45,-46,()),(-45,-29,()),(-45,8,()),(-33,-12,()),(-33,7,()),(-33,42,()),(-29,42,()),(-29,42,()),(-16,-46,()),(-16,3,()),(-16,3,()),(-12,-16,()),(-12,7,()),(-12,31,()),(-10,31,()),(-10,44,()),(-9,-45,()),(-9,31,()),(3,-46,()),(3,41,()),(3,44,()),(7,7,()),(7,31,()),(8,44,()),(31,-29,()),(31,42,()),(41,-33,()),(41,-10,()),(41,7,()),(41,8,()),(41,31,()),(42,-45,()),(42,31,()),(42,42,()),(45,-46,()),(45,-45,()),(45,-33,()),(45,-29,()),(45,-16,()),(45,-12,()),(45,-10,()),(45,-9,()),(45,3,()),(45,7,()),(45,8,()),(45,31,()),(45,41,()),(45,42,()),(45,44,())]

isinkdomTwoFingerExample2 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample2 = mkGraph [(-11,()),(-10,()),(-6,()),(1,()),(2,())] [(-11,-11,()),(-11,-11,()),(-11,-10,()),(-11,-10,()),(-11,-6,()),(-11,1,()),(-11,1,()),(-10,-10,()),(-10,-6,()),(-10,-6,()),(-6,1,()),(-6,1,()),(1,-10,()),(1,-6,()),(1,-6,()),(1,1,()),(2,-11,()),(2,-10,()),(2,-6,()),(2,1,())]

isinkdomTwoFingerExample3 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample3 = mkGraph [(-44,()),(-29,()),(-22,()),(13,()),(37,()),(47,())] [(-44,13,()),(-29,13,()),(-22,-29,()),(-22,37,()),(13,-44,()),(13,-22,()),(47,-44,()),(47,-29,()),(47,-22,()),(47,13,()),(47,37,())]

isinkdomTwoFingerExample4 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample4 = mkGraph [(-44,()),(-25,()),(-23,()),(-20,()),(-1,()),(4,()),(8,()),(13,()),(18,()),(19,()),(31,()),(32,())] [(-44,8,()),(-44,31,()),(-25,-44,()),(-23,19,()),(-23,31,()),(-20,-1,()),(-20,8,()),(-1,18,()),(8,-23,()),(8,4,()),(8,13,()),(13,13,()),(13,19,()),(18,-23,()),(18,13,()),(19,8,()),(31,19,()),(32,-44,()),(32,-25,()),(32,-23,()),(32,-20,()),(32,-1,()),(32,4,()),(32,8,()),(32,13,()),(32,18,()),(32,19,()),(32,31,())]

isinkdomTwoFingerExample5 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample5 = mkGraph [(-14,()),(-11,()),(7,()),(9,()),(13,()),(14,()),(15,())] [(-14,-11,()),(-14,9,()),(-14,13,()),(-11,9,()),(-11,14,()),(7,9,()),(7,13,()),(9,-14,()),(9,9,()),(15,-14,()),(15,-11,()),(15,7,()),(15,9,()),(15,13,()),(15,14,())]

isinkdomTwoFingerExample6 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample6 = mkGraph [(-21,()),(-6,()),(8,()),(9,())] [(-21,-21,()),(-21,-6,()),(-21,8,()),(-6,-6,()),(-6,-6,()),(8,-21,()),(8,-6,()),(9,-21,()),(9,-6,()),(9,8,())]

isinkdomTwoFingerExample7 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample7 = mkGraph  [(-10,()),(-9,()),(-5,()),(6,()),(8,()),(10,())] [(-10,-5,()),(-10,8,()),(-9,6,()),(-5,-9,()),(6,-10,()),(6,-9,()),(10,-10,()),(10,-9,()),(10,-5,()),(10,6,()),(10,8,())]

isinkdomTwoFingerExample8 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample8 = mkGraph [(-48,()),(-43,()),(-35,()),(-32,()),(-30,()),(-28,()),(-26,()),(-23,()),(-19,()),(-2,()),(-1,()),(24,()),(27,()),(29,()),(30,())] [(-48,29,()),(-43,-48,()),(-43,-30,()),(-43,27,()),(-35,-35,()),(-35,-28,()),(-35,24,()),(-35,27,()),(-32,-43,()),(-32,-2,()),(-32,-1,()),(-30,-48,()),(-30,-48,()),(-30,-23,()),(-30,29,()),(-28,-48,()),(-28,-26,()),(-26,-23,()),(-26,-19,()),(-26,27,()),(-23,-1,()),(-19,-35,()),(-19,-1,()),(-19,24,()),(-2,-23,()),(-1,-43,()),(-1,-30,()),(24,-48,()),(24,-35,()),(24,-30,()),(24,-28,()),(27,-48,()),(27,-32,()),(27,-30,()),(29,-48,()),(29,-32,()),(29,-30,()),(29,-30,()),(29,-30,()),(29,29,()),(30,-48,()),(30,-43,()),(30,-35,()),(30,-32,()),(30,-30,()),(30,-28,()),(30,-26,()),(30,-23,()),(30,-19,()),(30,-2,()),(30,-1,()),(30,24,()),(30,27,()),(30,29,())]

isinkdomTwoFingerExample9 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample9 = mkGraph [(-15,()),(0,()),(4,()),(6,()),(9,()),(10,()),(16,()),(17,())] [(-15,-15,()),(-15,4,()),(-15,6,()),(-15,10,()),(0,4,()),(0,4,()),(0,9,()),(4,-15,()),(4,6,()),(4,9,()),(6,0,()),(6,0,()),(9,0,()),(9,4,()),(9,16,()),(10,4,()),(17,-15,()),(17,0,()),(17,4,()),(17,6,()),(17,9,()),(17,10,()),(17,16,())]

isinkdomTwoFingerExample10 :: DynGraph gr => gr () ()
isinkdomTwoFingerExample10 = mkGraph [(-46,()),(-31,()),(-13,()),(-12,()),(-7,()),(-5,()),(-4,()),(10,()),(13,()),(34,()),(50,()),(53,()),(57,()),(59,()),(64,()),(65,()),(68,()),(70,()),(78,()),(79,())] [(-46,34,()),(-31,59,()),(-31,78,()),(-13,68,()),(-12,65,()),(-7,-5,()),(-7,70,()),(-5,65,()),(-5,70,()),(-4,-13,()),(-4,-5,()),(10,34,()),(10,53,()),(10,68,()),(13,59,()),(13,64,()),(34,13,()),(34,53,()),(50,10,()),(53,13,()),(53,68,()),(57,-7,()),(57,10,()),(57,70,()),(64,-12,()),(64,13,()),(64,34,()),(65,-46,()),(65,59,()),(65,78,()),(68,10,()),(68,50,()),(70,-12,()),(70,57,()),(79,-46,()),(79,-31,()),(79,-13,()),(79,-12,()),(79,-7,()),(79,-5,()),(79,-4,()),(79,10,()),(79,13,()),(79,34,()),(79,50,()),(79,53,()),(79,57,()),(79,59,()),(79,64,()),(79,65,()),(79,68,()),(79,70,()),(79,78,())]

imdomTwoFingerExample1 :: DynGraph gr => gr () ()
imdomTwoFingerExample1 = mkGraph [(-29,()),(-13,()),(-12,())] [(-29,-13,()),(-29,-13,()),(-13,-29,()),(-13,-29,()),(-12,-29,()),(-12,-13,())]


infinitelyDelaysExamle1 :: DynGraph gr => gr () ()
infinitelyDelaysExamle1 = mkGraph [(-11,()),(-6,()),(4,()),(6,()),(10,()),(11,())] [(-11,-11,()),(-11,10,()),(-6,10,()),(4,-11,()),(4,-6,()),(6,-11,()),(6,-6,()),(6,6,()),(10,4,()),(10,6,()),(11,-11,()),(11,-6,()),(11,4,()),(11,6,()),(11,10,())]
  where m1 = 11
        m2 = 10
        startNode = 6
        choice  = Map.fromList [(-11,-11),(4,-11),(6,-11),(10,4),(11,-11)]
        choice' = Map.fromList [(-11,-11),(4,-11),(6, -6),(10,4),(11,-11)]


infinitelyDelaysExamle2 :: DynGraph gr => gr () ()
infinitelyDelaysExamle2 = mkGraph [(-22,()),(-3,()),(5,()),(6,())] [(-22,-3,()),(-22,5,()),(-3,5,()),(5,-22,()),(5,5,()),(6,-22,())]
  where m1 = 6
        m2 = 3
        startNode = -22
        choice  = Map.fromList  [(-22,-3),(-3,5),(5,5),(6,-22)]
        choice' = Map.fromList  [(-22, 5),(-3,5),(5,5),(6,-22)]


infinitelyDelaysExamle3 :: DynGraph gr => gr () ()
infinitelyDelaysExamle3 = mkGraph [(-15,()),(-7,()),(8,()),(-2,()),(3,()),(6,()),(9,()),(10,())] [(-15,8,()),(-15,9,()),(-7,-7,()),(-7,8,()),(-7,3,()),(-7,9,()),(8,-15,()),(8,6,()),(8,9,()),(-2,-7,()),(6,-2,()),(6,3,()),(9,6,()),(9,9,()),(9,9,()),(10,-15,()),(10,-7,()),(10,8,()),(10,-2,()),(10,3,()),(10,6,()),(10,9,())]
  where  m1 = -2
         m2 = 6
         startNode = -2
         choice  = Map.fromList [(-15,9),(-7,8),(8,-15),(6,-2),(9,9),(10,-2)]

-- This example demonstrated an error in a former version of dodFast.
dodSuperFastCounterExample :: DynGraph gr => gr () ()
dodSuperFastCounterExample = mkGraph [(-82,()),(-81,()),(-74,()),(-28,()),(-6,()),(15,()),(23,()),(47,()),(66,())] [(-82,23,()),(-81,-74,()),(-81,15,()),(-74,-82,()),(-74,47,()),(-28,-81,()),(-28,47,()),(-6,15,()),(15,47,()),(15,47,()),(23,15,()),(47,-82,()),(47,-6,()),(66,-82,()),(66,-81,()),(66,-74,()),(66,-28,()),(66,-6,()),(66,15,()),(66,23,()),(66,47,())]


dodSuperFastCounterExample2:: DynGraph gr => gr () ()
dodSuperFastCounterExample2 = mkGraph [(-24,()),(-21,()),(8,()),(13,()),(14,())] [(-24,-21,()),(-24,8,()),(-24,8,()),(-21,8,()),(8,-21,()),(13,-24,()),(13,-24,()),(13,-21,()),(14,-24,()),(14,-21,()),(14,8,()),(14,13,())]


dodSuperFastCounterExample3:: DynGraph gr => gr () ()
dodSuperFastCounterExample3 = mkGraph [(-37,()),(-17,()),(-15,()),(-8,()),(-1,()),(6,()),(10,()),(20,()),(37,())] [(-37,-1,()),(-17,6,()),(-15,20,()),(-8,-17,()),(-8,10,()),(-1,-17,()),(6,10,()),(10,-15,()),(10,-1,()),(20,-37,()),(37,-37,()),(37,-17,()),(37,-15,()),(37,-8,()),(37,-1,()),(37,6,()),(37,10,()),(37,20,())]


dodSuperFastCounterExample4:: DynGraph gr => gr () ()
dodSuperFastCounterExample4 = mkGraph [(-10,()),(-7,()),(-4,()),(-1,()),(5,()),(14,()),(20,())] [(-10,-1,()),(-10,5,()),(-7,14,()),(-4,-7,()),(-1,-7,()),(-1,-7,()),(5,-4,()),(14,-1,()),(20,-10,()),(20,-7,()),(20,-4,()),(20,-1,()),(20,5,()),(20,14,())]

dodSuperFastCounterExample5:: DynGraph gr => gr () ()
dodSuperFastCounterExample5 = mkGraph [(-1,()),(22,()),(24,()),(28,()),(34,()),(40,()),(72,())] [(-1,40,()),(22,24,()),(24,-1,()),(28,24,()),(34,22,()),(34,40,()),(34,40,()),(40,28,()),(72,-1,()),(72,22,()),(72,24,()),(72,28,()),(72,34,()),(72,40,())]

dodSuperFastCounterExample6:: DynGraph gr => gr () ()
dodSuperFastCounterExample6 = mkGraph [(-22,()),(-18,()),(-12,()),(12,()),(14,()),(18,()),(28,()),(29,())] [(-22,-18,()),(-18,18,()),(-12,12,()),(-12,14,()),(12,-22,()),(12,28,()),(14,18,()),(18,28,()),(28,14,()),(29,-22,()),(29,-18,()),(29,-12,()),(29,12,()),(29,14,()),(29,18,()),(29,28,())]


wodDodInteresting1 :: DynGraph gr => gr () ()
wodDodInteresting1 = mkGraph [(-3,()),(7,()),(25,()),(29,()),(30,())] [(-3,-3,()),(-3,7,()),(-3,25,()),(7,-3,()),(7,7,()),(7,29,()),(25,-3,()),(25,7,()),(29,7,()),(30,-3,()),(30,7,()),(30,25,()),(30,29,())]


wodDodInteresting2 :: DynGraph gr => gr () ()
wodDodInteresting2 = mkGraph [(-16,()),(2,()),(9,()),(12,()),(28,()),(29,())] [(-16,2,()),(2,12,()),(9,2,()),(9,12,()),(12,-16,()),(28,9,()),(28,9,()),(28,12,()),(29,-16,()),(29,2,()),(29,9,()),(29,12,()),(29,28,())]

wodDodInteresting3 :: DynGraph gr => gr () ()
wodDodInteresting3 = mkGraph [(-15,()),(-12,()),(-10,()),(-8,()),(-7,())] [(-15,-10,()),(-15,-8,()),(-15,-8,()),(-12,-15,()),(-12,-12,()),(-12,-10,()),(-10,-12,()),(-10,-10,()),(-8,-10,()),(-7,-15,()),(-7,-12,()),(-7,-10,()),(-7,-8,())]

wodDodInteresting4 :: DynGraph gr => gr () ()
wodDodInteresting4 = mkGraph [(-21,()),(-18,()),(-16,()),(-15,()),(-14,()),(-12,()),(-11,()),(-9,()),(2,()),(4,()),(14,()),(17,()),(21,()),(22,())] [(-21,17,()),(-18,-9,()),(-16,-11,()),(-16,-9,()),(-16,21,()),(-14,-9,()),(-12,-16,()),(-11,4,()),(-9,-16,()),(-9,-16,()),(2,-15,()),(2,-9,()),(4,-12,()),(4,-9,()),(14,-15,()),(14,14,()),(14,17,()),(17,-14,()),(17,21,()),(21,-14,()),(22,-21,()),(22,-18,()),(22,-16,()),(22,-15,()),(22,-14,()),(22,-12,()),(22,-11,()),(22,-9,()),(22,2,()),(22,4,()),(22,14,()),(22,17,()),(22,21,())]

wodDodInteresting5 :: DynGraph gr => gr () ()
wodDodInteresting5 = mkGraph [(-23,()),(-20,()),(-18,()),(-16,()),(-11,()),(-8,()),(7,()),(24,()),(25,())] [(-23,-18,()),(-20,-8,()),(-18,7,()),(-16,-20,()),(-11,-16,()),(-8,-16,()),(-8,-8,()),(-8,24,()),(-8,24,()),(7,-20,()),(7,-11,()),(24,-23,()),(25,-23,()),(25,-20,()),(25,-18,()),(25,-16,()),(25,-11,()),(25,-8,()),(25,7,()),(25,24,())]

dFUpInteresting1 :: DynGraph gr => gr () ()
dFUpInteresting1 = mkGraph [(-7,()),(-2,()),(2,()),(3,())] [(-7,-2,()),(-2,2,()),(2,-7,()),(2,-7,()),(2,-2,()),(2,-2,()),(3,-7,()),(3,-2,()),(3,2,())]

dFUpInteresting2 :: DynGraph gr => gr () ()
dFUpInteresting2 = mkGraph [(-22,()),(-2,()),(31,()),(32,())] [(-22,-2,()),(-22,31,()),(31,-22,()),(32,-22,()),(32,-2,()),(32,31,())]


insecure  = [ 
              $(withName 'directFlow),
              $(withName 'directFlowThread),
              $(withName 'indirectFlow),
              $(withName 'orderConflict),
              $(withName 'dubiousOrderConflict),
              $(withName 'cdomIsBroken),
              $(withName 'cdomIsBroken'),
              $(withName 'cdomIsBroken2),
              $(withName 'timingDependenceExample),
              $(withName 'figure5right),
              $(withName 'figure5right'),
              $(withName 'figure5right''),
              $(withName 'ijisLSODistkaputt),
              $(withName 'anotherGeneratedProgram)
  ]

testsuite = [ $(withName 'example1),
              $(withName 'example2),
              $(withName 'example2'),
              $(withName 'example3),
              $(withName 'example4),
              $(withName 'example5),
              $(withName 'example6),
              $(withName 'example7),
              $(withName 'example8),
              $(withName 'threadSpawn1),
              $(withName 'joachim2),
              $(withName 'joachim3),
              $(withName 'noFlow),
              $(withName 'noDirectFlowThread),
              $(withName 'noninterferingSchedulers),
              $(withName 'figure5left),
              $(withName 'minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD),
              $(withName 'minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD2),
              $(withName 'minimalClassificationIsLessPreciseThanSimonClassification),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExampleMartin),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExampleSimon),
              $(withName 'timingSecureButNotCombinedTimingSecure),
              $(withName 'timingSecureButNotCombinedTimingSecureGenerated),
              $(withName 'someGeneratedProgram),
              $(withName 'aSecureGeneratedProgram),
              $(withName 'clientServerKeyExample),
              $(withName 'clientServerKeyExampleSimple),
              $(withName 'singleThreadedDelay),
              $(withName 'twoLoops),
              $(withName 'twoLoops'),
              $(withName 'controlDepExample),
              $(withName 'simpleBlocking),
              $(withName 'notReallyUnsound),
              $(withName 'notReallyUnsound2),
              $(withName 'notReallyUnsound3),
              $(withName 'notReallyUnsound4),
              $(withName 'notReallyUnsound5),
              $(withName 'notReallyUnsound6),
              $(withName 'notReallyUnsound7),
              $(withName 'notReallyUnsound8),
              $(withName 'notReallyUnsound9),
              $(withName 'notReallyUnsound10),
              $(withName 'notReallyUnsound11),
              $(withName 'notReallyUnsound12),
              $(withName 'notReallyUnsound13),
              $(withName 'notReallyUnsound14),
              $(withName 'notReallyUnsound15),
              $(withName 'notReallyUnsound16),
              $(withName 'notReallyUnsound17),
              $(withName 'notReallyUnsound18),
              $(withName 'notReallyUnsound19),
              $(withName 'notReallyUnsound20),
              $(withName 'notReallyUnsound21),
              $(withName 'notReallyUnsound22),
              $(withName 'notReallyUnsound23),
              $(withName 'notReallyUnsound24),
              $(withName 'notReallyUnsound25),
              $(withName 'notReallyUnsound26),
              $(withName 'notReallyUnsound27),
              $(withName 'notReallyUnsound28),
              $(withName 'notReallyUnsound29),
              $(withName 'notReallyUnsound30),
              $(withName 'forIf)
            ] ++
            precisionCounterExamples ++
            insecure ++
            []

-- These are counter-Examples to the claim that timingClassification (i.e.: the old version, not the "atUses" version)
-- is strictly more precise than minimalClassification.
precisionCounterExamples = [
              -- this no longer is a counterexample. i cannot quite figure out whu. possible causes: changes in the AST 2 cfg compiler, or due to the introduction of formal/actual nodes.
              -- it was a counterexample in, e.g., commit fb969553e31294c1255cba76eaa8ca7c72bf6002 Date:   Wed Feb 21 16:16:24 2018 +0100 "reenable unit tests for timing".
              -- $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample2),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample3),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample4),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExampleEssential),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample2Essential)
            ]


failingCdomIsCdom' = failingCdomIsCdom'Both

failingCdomIsCdom'Both = [
              $(withName 'example8),
              $(withName 'cdomIsBroken2),
              $(withName 'noninterferingSchedulers),
              $(withName 'figure5right'),
              $(withName 'figure5right''),
              $(withName 'someGeneratedProgram),
              $(withName 'anotherGeneratedProgram),
              $(withName 'aSecureGeneratedProgram),
              $(withName 'clientServerKeyExample),
              $(withName 'clientServerKeyExampleSimple),
              $(withName 'singleThreadedDelay),
              $(withName 'twoLoops),
              $(withName 'forIf),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample2),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample3)
            ]

failingCdomIsCdom'ChefOnly = [
              $(withName 'threadSpawn1),
              $(withName 'cdomIsBroken),
              $(withName 'cdomIsBroken')
            ]


failingNticd = [
              $(withName 'exampleNticd),
              $(withName 'exampleNticd2SmnF5)
            ]

failingNtscd = [
              $(withName 'exampleNtscd),
              $(withName 'exampleNtscd'),
              $(withName 'exampleNtscd2)
            ]

failingSnmF3F5 = [
              $(withName 'exampleNticd2SmnF5),
              $(withName 'exampleSmnF5)
            ]


myCDvsMyDom :: [(String, Gr () ())]
myCDvsMyDom = [
              $(withName 'wodDodInteresting3),
              $(withName 'wodDodInteresting4),
              $(withName 'wodDodInteresting5)
            ]

interestingDodWod :: [(String, Gr () ())]
interestingDodWod = [
              $(withName 'dFUpInteresting1),
              $(withName 'dFUpInteresting2),
              $(withName 'wodDodInteresting1),
              $(withName 'wodDodInteresting2),
              $(withName 'wodDodInteresting3),
              $(withName 'wodDodInteresting4),
              $(withName 'dodSuperFastCounterExample),
              $(withName 'dodSuperFastCounterExample2),
              $(withName 'dodSuperFastCounterExample3),
              $(withName 'dodSuperFastCounterExample4),
              $(withName 'dodSuperFastCounterExample5),
              $(withName 'dodSuperFastCounterExample6)
            ]

interestingIsinkdomTwoFinger :: [(String, Gr () ())]
interestingIsinkdomTwoFinger = [
              $(withName 'isinkdomTwoFingerExample1),
              $(withName 'isinkdomTwoFingerExample2),
              $(withName 'isinkdomTwoFingerExample3),
              $(withName 'isinkdomTwoFingerExample4),
              $(withName 'isinkdomTwoFingerExample5),
              $(withName 'isinkdomTwoFingerExample6),
              $(withName 'isinkdomTwoFingerExample7),
              $(withName 'isinkdomTwoFingerExample8),
              $(withName 'isinkdomTwoFingerExample9),
              $(withName 'isinkdomTwoFingerExample10)
            ]

interestingImdomTwoFinger :: [(String, Gr () ())]
interestingImdomTwoFinger = [
              $(withName ' imdomTwoFingerExample1)
            ]

interestingInfinitelyDelays :: [(String, Gr () ())]
interestingInfinitelyDelays = [
              $(withName ' infinitelyDelaysExamle1),
              $(withName ' infinitelyDelaysExamle2),
              $(withName ' infinitelyDelaysExamle3)
            ]


            
interestingTimingDep :: [(String, Gr () ())]
interestingTimingDep = [
              $(withName 'exampleTimingDepCorrectionInterestingSimon1),
              $(withName 'exampleTimingDepCorrectionInterestingSimon2),
              $(withName 'exampleTimingDepCorrectionInteresting3),
              $(withName 'exampleTimingDepCorrectionInteresting4),
              $(withName 'exampleTimingDepCorrectionInteresting5),
              $(withName 'exampleTimingDepCorrectionInteresting6),
              $(withName 'exampleTimingDepCorrectionInteresting7),
              $(withName 'exampleTimingDepCorrectionInteresting8),
              $(withName 'exampleTimingDepCorrectionInteresting9),
              $(withName 'exampleTimingDepCorrectionInteresting10),
              $(withName 'exampleTimingDepCorrectionInteresting11),
              $(withName 'exampleTimingDepCorrectionInteresting11Simple),
              $(withName 'exampleTimingDepCorrectionInteresting11Simple2),
              $(withName 'exampleTimingDepCorrectionInteresting11Simple3),
              $(withName 'exampleTimingDepCorrectionInteresting12),
              $(withName 'exampleTimingDepCorrectionInteresting13),
              $(withName 'exampleTimingDepCorrectionInteresting14),
              $(withName 'exampleTimingDepCorrectionInteresting15),
              $(withName 'exampleTimingDepCorrectionInteresting16),
              $(withName 'exampleTimingDepCorrectionInteresting17),
              $(withName 'exampleTimingDepCorrectionInteresting18),
              $(withName 'exampleTimingDepCorrectionInteresting18'),
              $(withName 'exampleTimingDepCorrectionInteresting18''),
              $(withName 'exampleTimingDepCorrectionInteresting18'''),
              $(withName 'exampleTimingDepCorrectionInteresting18''''),
              $(withName 'exampleTimingDepCorrectionInteresting19),
              $(withName 'exampleTimingDepCorrectionInteresting20),
              $(withName 'exampleTimingDepInterestingTwoFinger),
              $(withName 'exampleTimingDepInterestingTwoFinger2),
              $(withName 'exampleTimingDepInterestingTwoFinger3),
              $(withName 'exampleTimingDepInterestingTwoFinger4),
              $(withName 'exampleTimingDepInterestingTwoFinger5),
              $(withName 'exampleTimingDepInterestingTwoFinger6)
            ]

jcsPaperExamples = [
              $(withName 'figure5leftCode),
              $(withName 'figure1leftCode)
            ]

syntacticCodeExamples = jcsPaperExamples ++ [
              $(withName 'timingVsFSI3Code),
              $(withName 'timingAtUsesVsResumptionBasedBugInTranslationExample2Code),
              $(withName 'timingAtUsesVsResumptionBasedBugInTranslationExample1Code),
              $(withName 'simpleExample1Code),
              $(withName 'exampleD4Code)
            ]

failingWodNtscdReducible = [
              $(withName 'exampleSimonReducibleWod)
            ]


interproceduralTestSuit = [
                $(withName 'simpleProcedural),
                $(withName 'simpleProcedural2),
                $(withName 'summaryExample),
                $(withName 'summaryExample2),
                $(withName 'summaryExample3),
                $(withName 'summaryExample4),
                $(withName 'summaryExample5),
                $(withName 'summaryExample6),
                $(withName 'summaryExample7),
                $(withName 'summaryExample7'),
                $(withName 'summaryExample8),
                $(withName 'summaryExample9),
                $(withName 'summaryExample10),
                $(withName 'summaryExample11),
                $(withName 'summaryExample12),
                $(withName 'summaryExample13),
                $(withName 'summaryExample14),
                $(withName 'summaryExample15),
                $(withName 'simpleRecursive)
            ]
