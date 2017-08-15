{-# LANGUAGE TemplateHaskell #-}
module Program.Examples where


import Program
import Program.For
import Program.Defaults

import Program.Typing.FlexibleSchedulerIndependentChannels (ForProgram(..))


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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..3] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = undefined
        tcfg = mkGraph [(n,n) | n <- [1..3]] $
                       [(1,2,true), (1,3,false), (2,3,nop), (3,2,nop)]



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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..10] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 10
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..10] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 10
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..10] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 10
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..12] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 10
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..14] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 10
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1,2,7,8,9,10,11,12] = 1 
         | n `elem` [3,4,5,6] = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 3
        exitOf 1 = 12
        exitOf 2 = 6
        tcfg = mkGraph (genLNodes 1 12) $
                        [(1,2,Assign "x" (Val 42)),(2,3,spawn),(3,4,false),(3,5,true),(4,6,Print (Var "x") stdOut),(5,6,nop)]
                    ++  [(2,7,nop),(7,8,true),(8,9,nop),(9,10,nop),(10,11,true),(10,7,false),(11,12,Assign "x" (Var "x"))]


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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..12] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 12
        tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,Assign "x" (Val 42)), (2,3,Read "h" stdIn),(3,4,Guard True (Leq (Var "h") (Var "h"))),(3,5,Guard False (Leq (Var "h") (Var "h"))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(7,8,false),(8,9,nop),(9,7,nop),(7,10,true),(10,11,Assign "x" (Var "x")),(11,12,nop)]



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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..12] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 12
        tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,Assign "x" (Val 42)),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,Assign "x" (Var "x")),(6,7,nop)]
                   ++  [(7,8,nop),(8,9,nop),(9,10,nop),(10,7,false),(10,11,true),(11,12,Assign "x" (Var "x"))]




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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [3, 1, 6, 10, 15, 42] = 1
         | otherwise = error "uknown node"
        entryOf 1 = 15
        exitOf 1 = 42
        tcfg =  mkGraph [(15,15),(3,3),(1,1),(42,42)] [(3,1,nop),(3,42,nop),(1,3,nop),(1,42,nop),(15,1,nop),(15,42,nop)]



exampleSmnF5 :: Program Gr
exampleSmnF5 = Program {
    tcfg = tcfg,
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` [8, 5, 1, 12, 2] = 1
         | otherwise = error "uknown node"
        entryOf 1 = 12
        exitOf 1 = 5
        tcfg =  mkGraph [(8,8),(5,5),(1,1),(12,12),(2,2)] [(8,5,nop),(1,8,nop),(1,5,nop),(1,2,nop),(2,1,nop),(12,8,nop),(12,5,nop),(12,1,nop)]


exampleNticd2SmnF5 :: Program Gr
exampleNticd2SmnF5 = Program {
    tcfg = tcfg,
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` [17, 1, 2, 3, 7, 8] = 1
         | otherwise = error "uknown node"
        entryOf 1 = 8
        exitOf 1 = 7
        tcfg = mkGraph [(17,17),(1,1),(2,2),(3,3),(7,7),(8,8)] [(1,7,nop), (17,1,nop),(17,2,nop),(17,3,nop),(2,17,nop),(3,17,nop),(3,7,nop),(8,17,nop),(8,1,nop),(8,2,nop),(8,3,nop),(8,7,nop)]


exampleNtscd :: Program Gr
exampleNtscd = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
         (1,ForC 1 (Seq (ForC 2
                            (PrintToChannel (Times (Var "x") (Var "x")) "stdOut"))
                        (If (Leq (Val 0) (Times (Var "x") (Var "x")))
                            (ReadFromChannel "a" "stdIn")
                         {-else-}
                            (ReadFromChannel "a" "stdIn"))))
         ]


exampleNtscd2 :: Program Gr
exampleNtscd2 = Program {
    tcfg = tcfg,
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [-20,15,18,22,27] = 1
         | otherwise = error "uknown node"
        entryOf 1 = 27
        exitOf 1 = 18
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` [1,2,5,6,7] = 1
         | n `elem` [3,4]      = 2
         | otherwise = error "unknown node"
        entryOf 1 = 1
        entryOf 2 = 3
        exitOf 1 = 7
        exitOf 2 = 4
        tcfg = mkGraph (genLNodes 1 7)  $
                       [(1,2,nop),(2,3,spawn),(3,4,Assign "x" (Val 17))]
                   ++  [(2,5,nop),(5,6,Assign "x" (Val 4)),(6,7,Print (Var "x") stdOut)]




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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` ([1..7] ++ [10,11]) = 1
         | n `elem` ([8..9])           = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 8
        exitOf 1 = 11
        exitOf 2 = 9
        tcfg = mkGraph (genLNodes 1 11)  $
                       [(1,2,Assign "x" (Val 42)), (2,3,Read "h" stdIn),(3,4,Guard True (Leq (Var "h") (Var "h"))),(3,5,Guard False (Leq (Var "h") (Var "h"))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(7,8,Spawn),(7,10, NoOp), (10,11,Print (Var "x") stdOut),(8,9,Print (Var "x") stdOut)]


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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` ([1..7] ++ [10,11]) = 1
         | n `elem` ([8..9])         = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 8
        exitOf 1 = 10
        exitOf 2 = 9
        tcfg = mkGraph (genLNodes 1 11)  $
                       [(1,2,Assign "x" (Val 42)), (2,11, NoOp), (11,3,Read "h" stdIn),(3,4,Guard True (Leq (Var "h") (Var "h"))),(3,5,Guard False (Leq (Var "h") (Var "h"))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(2,8,Spawn),(7,10,Print (Var "x") stdOut),(8,9,Print (Var "x") stdOut)]






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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` ([1..8]   ++ [11,12]) = 1
         | n `elem` ([9..10])             = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 9
        exitOf 1 = 12
        exitOf 2 = 10
        tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,Assign "x" (Val 42)), (2,3,Read "h" stdIn),(3,4,false),(3,11,true),(11,12,Print (Var "x") stdOut),
                        (4,5,nop), (5,6,Guard True (Leq (Var "h") (Var "h"))),(5,7,Guard False (Leq (Var "h") (Var "h"))),
                                   (6,8,nop),                     (7,8,nop),
                        (8,3,nop),
                        (8,9,Spawn),(9,10,Print (Var "x") stdOut)]



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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` ([1..5]) = 1
         | n `elem` ([6..7]) = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 6
        exitOf 1 = 5
        exitOf 2 = 7
        tcfg = mkGraph (genLNodes 1 7)  $
                       [(1,2,Assign "x" (Val 42)), (2,3,nop), (3,4,Read "h" stdIn),(4,5,Print (Var "x") stdOut)]
                   ++  [(2,6,Spawn),(6,7,Print (Var "x") stdOut)]


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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2,3],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` ([1..17] ++ [20..23]) = 1
         | n `elem` ([201..202]) = 2
         | n `elem` ([301..302]) = 3
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 201
        entryOf 3 = 301
        exitOf 1 = 17
        exitOf 2 = 202
        exitOf 3 = 302
        tcfg = mkGraph [(n,n) | n <- [1..17] ++ [20..23] ++ [201..202] ++ [301..302]]  $
                       [( 1,23,nop),
                        (23,20,Read "h" stdIn),
                        (20,21, Assign "zero" (Val 0)),
                        (21,22, Assign "one" (Val 1)),
                        (22,2,Assign "tmp" (Val 1)), (2,3, Guard False (Leq (Var "h") (Var "h"))),
                                                     (2,4, Guard True  (Leq (Var "h") (Var "h"))),
                        (4,5,Assign "tmp" (Val 50)),
                        (3,5,nop),
                        (5,6,nop),
                        (6,7,nop),(6,201,Spawn),
                        (7,10, Guard False (Not $ Leq (Var "tmp") (Var "zero"))),
                        (7, 8, Guard True  (Not $ Leq (Var "tmp") (Var "zero"))),
                        (8, 9, Assign "tmp" (Plus (Var "tmp") (Val (-1)))),
                        (9, 7, nop),
                        (10,11,nop),
                        (11,12,Assign "tmp2" (Val 1)),
                        (12,301,Spawn),
                        (12,13,nop),
                        (13,16, Guard False (Not $ Leq (Var "tmp2") (Var "zero"))),
                        (13,14, Guard True  (Not $ Leq (Var "tmp2") (Var "zero"))),
                        (14,15, Assign "tmp2" (Plus (Var "tmp2") (Val (-1)))),
                        (15,13, nop),
                        (16,17, Print (Val 1) stdOut),

                        (201,202, Assign "tmp2" (Val 50)),

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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2,3],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` ([1..17] ++ [20..23]) = 1
         | n `elem` ([201..202]) = 2
         | n `elem` ([301..302]) = 3
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 201
        entryOf 3 = 301
        exitOf 1 = 17
        exitOf 2 = 202
        exitOf 3 = 302
        tcfg = mkGraph [(n,n) | n <- [1..17] ++ [20..23] ++ [201..202] ++ [301..302]]  $
                       [( 1,23,nop),
                        (23,20,Read "h" stdIn),
                        (20,21, Assign "zero" (Val 0)), -- TODO: entfernen
                        (21,22, Assign "one" (Val 1)),  -- TODO: entfernen
                        (22,2,Assign "tmp" (Val 1)), (2,3, Guard False (Leq (Var "h") (Var "h"))),
                                                     (2,4, Guard True  (Leq (Var "h") (Var "h"))),
                        (4,5,Assign "tmp" (Val 50)),
                        (3,5,nop),
                        (5,6,nop),
                        (6,7,nop),(6,201,Spawn),
                        (7,10, Guard False (Not $ Leq (Var "tmp2") (Var "zero"))),
                        (7, 8, Guard True  (Not $ Leq (Var "tmp2") (Var "zero"))),
                        (8, 9, Assign "tmp" (Plus (Var "tmp") (Val (-1)))),
                        (9, 7, nop),
                        (10,11,nop),
                        (11,12,Assign "tmp2" (Val 1)),
                        (12,301,Spawn),
                        (12,13,nop),
                        (13,16, Guard False (Not $ Leq (Var "tmp2") (Var "zero"))),
                        (13,14, Guard True  (Not $ Leq (Var "tmp2") (Var "zero"))),
                        (14,15, Assign "tmp2" (Plus (Var "tmp2") (Val (-1)))),
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,4,6],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` [1,2,3,7] = 1
         | n `elem` [4,5,8]   = 4
         | n `elem` [6,9]     = 6
         | otherwise = error "unknown node"
        entryOf 1 = 1
        entryOf 4 = 4
        entryOf 6 = 6
        exitOf 1 = 7
        exitOf 4 = 8
        exitOf 6 = 9
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,5,8],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n
         | n `elem` [1,2,3,4] = 1
         | n `elem` [5,6,7]   = 5
         | n `elem` [8,9]     = 8
         | otherwise = error "unknown node"
        entryOf 1 = 1
        entryOf 5 = 5
        entryOf 8 = 8
        exitOf 1 = 4
        exitOf 5 = 7
        exitOf 8 = 9
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                         `Seq` -- Notwendig, da sonst die Controlabhängigkeit vom Start-Knoten zu viel tainted.
           ReadFromChannel "h" stdIn    `Seq`
           If (Leq (Var "h") (Val 0))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           SpawnThread 2                `Seq`
           SpawnThread 3                `Seq`
           ReadFromChannel "h" stdIn    `Seq`
           If (Leq (Var "h") (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)
          ),
          (2,
           Skip                         `Seq`
           Skip                         `Seq`
           Ass "l" (Val 0)
          ),
          (3,
           Skip                         `Seq`
           Skip                         `Seq`
           Ass "l" (Val 1)
          )
         ]


noFlow :: Program Gr
noFlow = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           Ass             "x" (Val 42)  `Seq`
           PrintToChannel  (Var "x") stdOut
          )
         ]

directFlow :: Program Gr
directFlow = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           PrintToChannel  (Var "h")  stdOut
          )
         ]

directFlowThread :: Program Gr
directFlowThread = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           Ass "x" (Var "h")             `Seq`
           SpawnThread 2
          ),
          (2,
           PrintToChannel (Var "x") stdOut
          )
         ]


noDirectFlowThread :: Program Gr
noDirectFlowThread = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Ass "h" (Val 0)               `Seq`
           Ass "x" (Var "h")             `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           SpawnThread 2
          ),
          (2,
           PrintToChannel (Var "x") stdOut
          )
         ]


indirectFlow :: Program Gr
indirectFlow = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           Ass "x" (Val 42)              `Seq`
           If (Leq (Var "h") (Val 0))
              (Ass "x" (Val 17))
              (Skip)                     `Seq`
           PrintToChannel (Var "x") stdOut
          )
         ]


orderConflict :: Program Gr
orderConflict = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           SpawnThread 2                 `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           If (Leq (Var "h") (Val 0))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Ass "x" (Val 42)              `Seq`
           Ass "y" (Val 42)              `Seq`
           SpawnThread 2                 `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           If (Leq (Var "h") (Val 0))
              (Skip `Seq` Skip)
              (Skip)                     `Seq`
           PrintToChannel (Var "x") stdOut
          ),
          (2,
           PrintToChannel (Var "y") stdOut
          )
         ]


cdomIsBroken :: Program Gr
cdomIsBroken = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           Ass "x" (Val 42)                                                 `Seq`
           SpawnThread 2                                                    `Seq`
           If (Leq (Var "h") (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           Ass "x" (Val 17)                                                 `Seq`
           SpawnThread 2
          ),
          (2,
           Skip                                                             `Seq`
           PrintToChannel (Var "x") stdOut
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           SpawnThread 2                                                    `Seq`
           If (Leq (Var "h") (Val 0))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           ForC 2 (
              If (Leq (Var "h") (Val 0))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           ForC 2 (
              ReadFromChannel "l1" lowIn1                                   `Seq`
              ReadFromChannel "l2" lowIn2                                   `Seq`
              SpawnThread 42                                                `Seq`
              SpawnThread 11                                                `Seq`
              SpawnThread 12
           )
          ),
          (42,
           Skip                                                             `Seq`
           If (Leq (Var "h") (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           Ass "h" (Var "h" `Plus` Var "l1" )
          ),
          (11,
           Skip                                                             `Seq`
           Ass "l" (Var "l1")                                               `Seq`
           PrintToChannel (Var "l") stdOut
          ),
          (12,
           Skip                                                             `Seq`
           Ass "l" (Var "l2")                                               `Seq`
           PrintToChannel (Var "l") stdOut
          )
         ]



timingVsFSI3 :: Program Gr
timingVsFSI3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram timingVsFSI3Code

timingVsFSI3For :: ForProgram
timingVsFSI3For = ForProgram {
    code = timingVsFSI3Code,
    channelTyping = defaultChannelObservability,
    mainThreadFor = 1
  }
  
timingVsFSI3Code = code where
         code = Map.fromList $ [
           (1, Skip                                         `Seq`   -- remove this line to obtain a program that is FSI-Secure, but which timingAnalysis cannot determine!
               ReadFromChannel "a" "stdIn"                  `Seq`
               SpawnThread 2
           ),
           (2, ReadFromChannel "x" "lowIn1"                 `Seq`
               Ass "a" (Times (Var "x") (Var "a"))
           )
          ]




timingDependenceExample:: Program Gr
timingDependenceExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
           (1, Skip                                         `Seq`
               ReadFromChannel "h" "stdIn"                  `Seq`
               SpawnThread 2                                `Seq`
               ForV "h" (Ass "x" (Val 42))                  `Seq`
               PrintToChannel (Var "x") stdOut
           ),
           (2, ReadFromChannel "x" "lowIn1"                 `Seq`
               ForC 5 Skip                                  `Seq`
               Ass "x" (Val 17)
           )
          ]


code2Program :: Map Integer For -> Program Gr
code2Program code = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code

code2ForProgram :: Map Integer For -> ForProgram
code2ForProgram code = ForProgram {
    code = code,
    channelTyping = defaultChannelObservability,
    mainThreadFor = 1
  }

figure1leftCode = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           If (Leq (Var "h") (Val 1234))
              (PrintToChannel (Val 0) stdOut)
              (Skip)                                                        `Seq`
           Ass "l" (Var "h")                                                `Seq`
           PrintToChannel (Var "l") stdOut
          )
         ]

figure5left = code2Program figure5leftCode
  
figure5leftCode = code where
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           If (Leq (Var "h") (Val 0))
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

figure5right :: Program Gr
figure5right = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           Ass "tmp" (Val 0)                                                `Seq`
           If (Leq (Var "h") (Val 0))
              (Ass "tmp" (Val 8))
              (Skip)                                                        `Seq`
           SpawnThread 2                                                    `Seq`
           ForV "tmp" (
             Skip
           )                                                                `Seq`
           Ass "tmp2" (Val 0)                                               `Seq`
           SpawnThread 3                                                    `Seq`
           ForV "tmp2" (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass "tmp2" (Val 3)
          ),
          (3,
           PrintToChannel (Val 17) stdOut
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           Ass "tmp" (Val 0)                                                `Seq`
           If (Leq (Var "h") (Val 0))
              (Ass "tmp" (Val 5))
              (Skip)                                                        `Seq`
           SpawnThread 2                                                    `Seq`
           ForV "tmp" (
             Skip
           )                                                                `Seq`
           Ass "tmp2" (Val 5)                                               `Seq`
           SpawnThread 3                                                    `Seq`
           ForV "tmp2" (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass "tmp2" (Val 0)
          ),
          (3,
           PrintToChannel (Val 17) stdOut
          )
         ]


figure5right'' :: Program Gr
figure5right'' = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           Ass "tmp" (Val 0)                                                `Seq`
           If (Leq (Var "h") (Val 0))
              (Ass "tmp" (Val 10))
              (Skip)                                                        `Seq`
           SpawnThread 2                                                    `Seq`
           ForV "tmp" (
             Skip
           )                                                                `Seq`
           Ass "tmp2" (Val 0)                                               `Seq`
           SpawnThread 3                                                    `Seq`
           Ass  "loop2" (Var "tmp2")                                        `Seq`
           ForV "loop2" (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 42) stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass "tmp2" (Val 3)
          ),
          (3,
           PrintToChannel (Val 17) stdOut
          )
         ]


ijisLSODistkaputt :: Program Gr
ijisLSODistkaputt = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           SpawnThread 2                                                    `Seq`
           If (Leq (Var "h") (Val 0))
              (Skip `Seq` Skip `Seq` Skip `Seq` Skip `Seq` Skip)
              (Skip)                                                        `Seq`
           Ass "x" (Val 17)
          ),
          (2,
           Skip                                                             `Seq`
           Ass "x" (Val 42)                                                 `Seq`
           PrintToChannel (Var "x") stdOut
          )
         ]

minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD ::  Program Gr
minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODCode

minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODCode = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass "h" (Val 0)                                                  `Seq`
           SpawnThread 2                                                    `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           Ass "h2" (Var "h")                                               `Seq`
           Ass "x" (Val 42)                                                 `Seq`
           PrintToChannel (Var "x") stdOut
          )
         ]

minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODFor :: ForProgram
minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODFor = ForProgram {
    code = minimalClassificationIsLessPreciseThanGiffhornLSODandRLSODCode,
    channelTyping = defaultChannelObservability,
    mainThreadFor = 1
  }


minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD2 ::  Program Gr
minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           SpawnThread 2                                                    `Seq`
           Skip
          ),
          (2,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           PrintToChannel (Val 42) stdOut
          )
         ]


minimalClassificationIsLessPreciseThanSimonClassification ::  Program Gr
minimalClassificationIsLessPreciseThanSimonClassification = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           If (Leq (Val 0) (Val 1))                                         
               (ReadFromChannel "h" stdIn)                                  
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           Ass "tmp" (Val 0)                                                `Seq`
           If (Leq (Var "h") (Val 0))
              (Ass "tmp" (Val 8))
              (Skip)                                                        `Seq`
           ForV "tmp" (
             Skip
           )                                                                `Seq`
           SpawnThread 2                                                    `Seq`
           Ass "tmp2" (Val 0)                                               `Seq`
           PrintToChannel (Var "tmp2") stdOut
          ),
          (2,
           Skip                                                             `Seq`
           Ass "tmp2" (Val 3)
          )
         ]

timingSecureButNotCombinedTimingSecureGenerated :: Program Gr
timingSecureButNotCombinedTimingSecureGenerated = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList [(1,Seq (If CTrue (If CFalse (Seq Skip Skip) (Seq (ReadFromChannel "x" "lowIn1") (Ass "y" (Plus (Var "x") (Var "x"))))) (Seq (Seq Skip (ReadFromChannel "x" "stdIn")) (If (Leq (Val 0) (Plus (Var "x") (Var "x"))) Skip (Ass "a" (Plus (Var "x") (Var "x")))))) (Seq (If CTrue (If CFalse (PrintToChannel (Val 42) "stdOut") (ReadFromChannel "c" "stdIn")) (ForC 1 (Ass "z" (Val 1)))) (If CFalse (Seq (PrintToChannel (Val 17) "stdOut") Skip) (Seq (Ass "z" (Val 0)) (SpawnThread 2))))),(2,ForV "z" (Seq (ForC 2 (Seq Skip (PrintToChannel (Plus (Var "z") (Var "z")) "stdOut"))) (Seq (Seq (Ass "c" (Plus (Var "z") (Var "z"))) (ReadFromChannel "y" "lowIn1")) (Seq Skip (PrintToChannel (Plus (Var "z") (Var "y")) "stdOut")))))]

someGeneratedProgram :: Program Gr
someGeneratedProgram = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList [(1,Seq (ForC 3 (If CTrue (Seq Skip Skip) (Seq (ReadFromChannel "x" "stdIn") (ReadFromChannel "y" "lowIn1")))) (Seq (ForC 2 (Seq (PrintToChannel (Val 1) "stdOut") (ReadFromChannel "c" "lowIn1"))) (ForV "c" (If (Leq (Val 0) (Plus (Var "c") (Var "c"))) (SpawnThread 3) (ReadFromChannel "y" "stdIn"))))),(3,ForV "c" (If (Leq (Val 0) (Plus (Var "c") (Var "c"))) (Seq (ForC 3 (ReadFromChannel "b" "stdIn")) (If (Leq (Val 0) (Plus (Var "c") (Var "c"))) (ReadFromChannel "x" "stdIn") (PrintToChannel (Plus (Var "c") (Var "b")) "stdOut"))) (Seq (Seq (PrintToChannel (Plus (Var "c") (Var "c")) "stdOut") (PrintToChannel (Plus (Var "c") (Var "c")) "stdOut")) (Seq (Ass "a" (Plus (Var "c") (Var "c"))) (Ass "x" (Plus (Var "a") (Var "a")))))))]

-- this one generates *very* long (inifinitely so?!?!) executions with defaultInput'
anotherGeneratedProgram :: Program Gr
anotherGeneratedProgram = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        -- code = Map.fromList [(1,Seq (Seq (ForC 2 (ForC 2 (PrintToChannel (Val 1) "stdOut"))) (Seq (Seq (ReadFromChannel "a" "stdIn") (ReadFromChannel "a" "lowIn1")) (Seq (PrintToChannel (Times (Var "a") (Var "a")) "stdOut") (PrintToChannel (Times (Var "a") (Var "a")) "stdOut")))) (ForC 1 (Seq (Seq (ReadFromChannel "x" "stdIn") (SpawnThread 3)) (ForV "a" (ReadFromChannel "c" "lowIn1"))))),(2,Seq (Seq (If (Leq (Val 0) (Times (Var "a") (Var "x"))) (ForV "x" (ReadFromChannel "z" "lowIn1")) (ForC 2 (ReadFromChannel "a" "stdIn"))) (Seq (Seq (ReadFromChannel "a" "lowIn1") Skip) (ForV "x" (Ass "a" (Times (Var "a") (Var "a")))))) (Seq (Seq (ForV "a" Skip) (Seq (PrintToChannel (Times (Var "x") (Var "x")) "stdOut") (PrintToChannel (Times (Var "x") (Var "a")) "stdOut"))) (ForC 2 (If (Leq (Val 0) (Times (Var "x") (Var "x"))) (Ass "x" (Times (Var "a") (Var "x"))) (ReadFromChannel "z" "lowIn1"))))),(3,ForV "a" (ForC 1 (Seq (ForV "x" (Ass "z" (Times (Var "a") (Var "x")))) (If (Leq (Val 0) (Times (Var "x") (Var "a"))) (SpawnThread 2) (PrintToChannel (Times (Var "x") (Var "x")) "stdOut")))))]
        code = Map.fromList [
          (1,Seq (Seq (ForC 2
                            (ForC 2
                                  (PrintToChannel (Val 1) "stdOut")))
            (Seq (Seq (ReadFromChannel "a" "stdIn")
                      (ReadFromChannel "a" "lowIn1"))
                 (Seq (PrintToChannel (Times (Var "a") (Var "a")) "stdOut")
                      (PrintToChannel (Times (Var "a") (Var "a")) "stdOut"))))
                      (ForC 1
                  (Seq (Seq (ReadFromChannel "x" "stdIn")
                            (SpawnThread 3))
                            (ForV "a"
                                  (ReadFromChannel "c" "lowIn1"))))),
          (2,Seq (Seq (If (Leq (Val 0) (Times (Var "a") (Var "x")))
                          (ForV "x" (ReadFromChannel "z" "lowIn1"))
                          (ForC 2 (ReadFromChannel "a" "stdIn")))
            (Seq (Seq (ReadFromChannel "a" "lowIn1")
                       Skip)
                      (ForV "x"
                            (Ass "a" (Times (Var "a") (Var "a"))))))
            (Seq (Seq (ForV "a" Skip)
                 (Seq (PrintToChannel (Times (Var "x") (Var "x")) "stdOut")
                      (PrintToChannel (Times (Var "x") (Var "a")) "stdOut")))
                      (ForC 2 (If (Leq (Val 0) (Times (Var "x") (Var "x")))
                                  (Ass "x" (Times (Var "a") (Var "x")))
                                  (ReadFromChannel "z" "lowIn1"))))),
          (3,         ForV "a"
                           (ForC 1
                            (Seq (ForV "x"
                                       (Ass "z" (Times (Var "a") (Var "x"))))
                                 (If (Leq (Val 0) (Times (Var "x") (Var "a")))
                                     (SpawnThread 2)
                                     (PrintToChannel (Times (Var "x") (Var "x")) "stdOut")))))]


-- this one appears to be secure, but cannot be proven so
aSecureGeneratedProgram :: Program Gr
aSecureGeneratedProgram = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList [(1,ForC 1 (If CTrue (Seq (SpawnThread 3) (SpawnThread 2)) (Seq (PrintToChannel (Val 42) "stdOut") (Ass "z" (Val 1))))),(2,Seq (Seq (ForC 2 (PrintToChannel (Val 0) "stdOut")) (Seq (ReadFromChannel "a" "lowIn1") Skip)) (Seq (Seq Skip Skip) (ForV "a" (ReadFromChannel "y" "lowIn1")))),(3,If CFalse (Seq (Seq (ReadFromChannel "a" "stdIn") (ReadFromChannel "b" "stdIn")) (If (Leq (Val 0) (Times (Var "b") (Var "b"))) Skip Skip)) (If CFalse (If CFalse (ReadFromChannel "c" "stdIn") (Ass "y" (Val 0))) (If CFalse (Ass "a" (Val (-1))) (ReadFromChannel "y" "lowIn1"))))]


clientServerKeyExampleSimple ::  Program Gr
clientServerKeyExampleSimple = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (setup,
           Skip                                                             `Seq`
           Ass "privKey" (Val 42)                                           `Seq`
           SpawnThread server                                               `Seq`
           ForC 3 (
             ReadFromChannel "msg" "stdIn"                                  `Seq`
             SpawnThread client
           )
          ),
          (server,
           Skip
          ),
          (client,
           Skip                                                             `Seq`
           Ass "msg_enc" (Val 0)                                            `Seq`  -- not (Var "msg") `Plus` (Var "privKey")), since we do not declassify or anything here
           PrintToChannel (Var "msg_enc") "stdOut"
          )
         ]
        setup  = 1
        server = 2
        client = 3


clientServerKeyExample ::  Program Gr
clientServerKeyExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (setup,
           Skip                                                             `Seq`
           Ass    "privKey" (Val 7)                                         `Seq`
           ReadFromChannel "privKeyRndSeed" "stdIn"                         `Seq`
           ForV "privKeyRndSeed" (
             Ass "privKey" ((Var "privKey") `Plus` (Val 3))
           )                                                                `Seq`  -- "initialization of the private key ... and [its] runtime may depend on HIGH information."
           SpawnThread server                                               `Seq`
           ForC 3 (
             ReadFromChannel "msg" "stdIn"                                  `Seq`
             SpawnThread client
           )
          ),
          (server,
           Skip
          ),
          (client,
           Skip                                                             `Seq`
           ForV "privKey" (
             Skip
           )                                                                `Seq`  -- "encryption .. happen before the send operation and [its] runtime may depend on HIGH information."
           Ass "msg_enc" (Val 0)                                            `Seq`  -- "due to ideal encryption no explicit and implicit information flow occurs between the secret message and its encryption.
           PrintToChannel (Var "msg_enc") "stdOut"
          )
         ]
        setup  = 1
        server = 2
        client = 3


clientSetupKeyExample ::  Program Gr
clientSetupKeyExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (setup,
           Skip                                                             `Seq`
           ReadFromChannel "secretBit" "stdIn"                              `Seq`
           Ass    "privKey" (Val 0)                                         `Seq`
           ReadFromChannel "privKeyRndSeed" "stdIn"                         `Seq`  --
           ForV "privKeyRndSeed" (
             Ass "privKey" ((Var "privKey") `Plus` (Val 3))
           )                                                                `Seq`  -- "initialization of the private key ... and [its] runtime may depend on HIGH information."
           SpawnThread server                                               `Seq`
           ForC 3 (
             ReadFromChannel "msg1" "lowIn1"                                 `Seq`
             ReadFromChannel "msg2" "lowIn2"                                 `Seq`
             If ((Var "secretBit") `Leq` (Val 0))
                 (Ass "msg" (Var "msg1"))
                 (Ass "msg" (Var "msg2"))                                   `Seq`
             SpawnThread client
           )
          ),
          (server,
           Skip
          ),
          (client,
           Skip                                                             `Seq`
           ForV "privKey" (
             Skip
           )                                                                `Seq`  -- "encryption .. happen before the send operation and [its] runtime may depend on HIGH information."
           Ass "msg_enc" (Val 0)                                            `Seq`  -- "due to ideal encryption no explicit and implicit information flow occurs between the secret message and its encryption.
           PrintToChannel (Var "msg_enc") "stdOut"
          )
         ]
        setup  = 1
        server = 2
        client = 3

singleThreadedDelay :: Program Gr
singleThreadedDelay = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           PrintToChannel (Val 42) "stdOut"                                 `Seq`
           ReadFromChannel "h" "stdIn"                                      `Seq`
           ForV "h" (
             Skip
           )                                                                `Seq`
           PrintToChannel (Val 17) "stdOut"
          )
         ]


-- similiar to http://dx.doi.org/10.1109/csf.2012.15
environmentTotalAssumption1 :: Program Gr
environmentTotalAssumption1 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ForC 100 (
              ReadFromChannel "h" stdIn                                     `Seq`
              PrintToChannel (Val 42) stdOut
           )
          )
         ]
environmentTotalAssumption2 :: Program Gr
environmentTotalAssumption2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ReadFromChannel "h" stdIn                                        `Seq`
           Ass "bit" (Val 1)                                                `Seq`
           ForC 16 (
              If (Leq ((Var "h") `Times` (Var "bit")) (Val 0))
                (PrintToChannel (Val 1) highOut1)
                (PrintToChannel (Val 1) highOut2)
           )
          )
         ]

simple :: Program Gr
simple = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass "x" (Var "a")                                                `Seq`
           If (Leq (Var "x") (Val 0))
              (Ass "z" (Val 1))
              (Ass "z" (Val 0))
          )
         ]
simple2 :: Program Gr
simple2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass "x" (Var "a")                                                `Seq`
           If (Leq (Var "x") (Val 0))
              (Skip)
              (Skip)                                                        `Seq`
           Ass "z" (Val 0)
          )

         ]

simple3 :: Program Gr
simple3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass "tmp" ((Var "z") `Plus` (Val 1))                             `Seq`
           Ass "x" (Var "a")                                                `Seq`
           If (Leq (Var "x") (Val 0))
              (Skip)
              (Skip)                                                        `Seq`
           Ass "z" (Var "tmp")
          )

         ]

twoLoops :: Program Gr
twoLoops = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           ForC 5 Skip                                                      `Seq`
           ForC 5 Skip                                                      `Seq`
           Ass "z" (Var "tmp")
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
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = defaultObservabilityMap tcfg
   }
  where staticThreadOf n 
         | n `elem` [1..8] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 5
        tcfg = mkGraph (genLNodes 1 8) $
                        [(1,2,NoOp), (2,3,NoOp), (3,8,Guard True CTrue), (8,4,NoOp), (4,5, Guard True CTrue)]
                    ++  [(3,6,Guard False CTrue), (6,2, NoOp), (4,7,Guard False CTrue), (7,8,NoOp)]

forIf :: Program Gr
forIf = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                                                             `Seq`
           Ass "x" (Val 42)                                                 `Seq`
           ForC 5 (
              If (Leq (Var "x") (Val 0)) Skip Skip
           )                                                                `Seq`
           Skip
          )
         ]


minimalClassificationVstimingClassificationDomPathsCounterExampleSimon:: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExampleSimon = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel "h" "stdIn"   `Seq`
           SpawnThread 2                 `Seq`
           ForV "h" (Ass "h" ((Var "h") `Plus` (Val (-1)))) `Seq`
           PrintToChannel (Val 42) "stdOut"
          ),
          (2, Skip
          )
          ]


minimalClassificationVstimingClassificationDomPathsCounterExampleMartin:: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExampleMartin = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel "h" "stdIn"   `Seq`
           SpawnThread 2                 `Seq`
           Ass "h2" (Var "h")            `Seq`
           PrintToChannel (Val 42) "stdOut"
          ),
          (2, Skip                       `Seq`
              PrintToChannel (Val 17) "stdOut"
          )
          ]



minimalClassificationVstimingClassificationDomPathsCounterExample :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample = p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram code
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
                     (If (Leq (Val 0) (Times (Var "z") (Var "z")))
                         Skip
                         (ReadFromChannel "z" "stdIn"))
             )
          ),
          (3, Skip `Seq`
              ReadFromChannel "z" "lowIn1"
          )
          ]


minimalClassificationVstimingClassificationDomPathsCounterExample2 :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample2 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, (Seq (Seq (If CFalse (Seq (SpawnThread 3) (PrintToChannel (Val 1) "stdOut")) (If CFalse (ReadFromChannel "c" "lowIn1") (SpawnThread 2))) (If CFalse (If CTrue (Ass "a" (Val (-1))) (Ass "y" (Val 17))) (ForC 1 (PrintToChannel (Val 42) "stdOut")))) (ForC 1 (Seq (If CFalse (ReadFromChannel "c" "lowIn1") (ReadFromChannel "b" "lowIn1")) (If CFalse (ReadFromChannel "x" "lowIn1") (Ass "z" (Val 0)))))) ),
          (2, (Seq (Seq (Seq (ForC 1 (Ass "y" (Val (-1)))) (Seq (ReadFromChannel "b" "lowIn1") (Ass "b" (Times (Var "y") (Var "y"))))) (Seq (If (Leq (Val 0) (Times (Var "y") (Var "y"))) Skip (Ass "c" (Times (Var "y") (Var "b")))) (Seq (ReadFromChannel "x" "stdIn") (ReadFromChannel "b" "stdIn")))) (ForV "x" (ForV "b" (Seq (Ass "x" ((Var "x") `Plus` (Val (-1)))) (If (Leq (Val 0) (Times (Var "y") (Var "x"))) (Ass "a" (Times (Var "x") (Var "b"))) (ReadFromChannel "a" "stdIn")))))) ),
          (3,(ForC 2 (Seq (Seq (Seq (PrintToChannel (Val 17) "stdOut") (Ass "b" (Val 42))) (ForC 2 (PrintToChannel (Times (Var "b") (Var "b")) "stdOut"))) (Seq (Seq (PrintToChannel (Times (Var "b") (Var "b")) "stdOut") (PrintToChannel (Times (Var "b") (Var "b")) "stdOut")) (Seq (PrintToChannel (Times (Var "b") (Var "b")) "stdOut") (Ass "y" (Times (Var "b") (Var "b"))))))))
          ]



minimalClassificationVstimingClassificationDomPathsCounterExample2Essential :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample2Essential = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, Skip                             `Seq`
              Ass "x" (Val 1)                  `Seq`
              If CTrue
                (SpawnThread 2)
                (SpawnThread 3)                `Seq`
              ReadFromChannel "x" "lowIn1"
          ),
          (2, Skip                             `Seq`
              ReadFromChannel "h" "stdIn"      `Seq`
              If (Leq (Var "h") (Val 0))
                 (Skip `Seq` Skip)
                 (Skip)                        `Seq`
              Ass "x" (Val 42)
          ),
          (3, Skip                             `Seq`
              PrintToChannel (Var "x") "stdOut"
          )
          ]


-- counter example 3 and 4 are essential the same as minimalClassificationVstimingClassificationDomPathsCounterExampleEssential
minimalClassificationVstimingClassificationDomPathsCounterExample3 :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(Seq (Seq (ForC 2 (Seq (SpawnThread 3) (SpawnThread 2))) (Seq (If CTrue (ReadFromChannel "z" "lowIn1") (PrintToChannel (Val (-1)) "stdOut")) (ForC 1 (Ass "x" (Val 1))))) (ForC 2 (Seq (ForC 1 Skip) (Seq (ReadFromChannel "b" "lowIn1") (ReadFromChannel "x" "lowIn1")))))),
         (2,(Seq (Seq (Seq (Seq Skip (ReadFromChannel "x" "lowIn1")) (ForV "x" Skip)) (If (Leq (Val 0) (Times (Var "x") (Var "x"))) (Seq (PrintToChannel (Times (Var "x") (Var "x")) "stdOut") (PrintToChannel (Times (Var "x") (Var "x")) "stdOut")) (ForC 2 (ReadFromChannel "x" "lowIn1")))) (ForV "x" (Seq (Seq (PrintToChannel (Times (Var "x") (Var "x")) "stdOut") (ReadFromChannel "z" "lowIn1")) (Seq (ReadFromChannel "z" "lowIn1") (PrintToChannel (Times (Var "x") (Var "z")) "stdOut")))))),
         (3,(Seq (Seq (Seq (Seq (Ass "b" (Val 17)) (ReadFromChannel "b" "lowIn1")) (ForC 2 (Ass "y" (Times (Var "b") (Var "b"))))) (Seq (Seq (Ass "c" (Times (Var "y") (Var "y"))) (Ass "b" (Times (Var "y") (Var "y")))) (ForC 1 (Ass "b" (Times (Var "y") (Var "y")))))) (ForC 1 (Seq (Seq (ReadFromChannel "a" "stdIn") (ReadFromChannel "c" "stdIn")) (If (Leq (Val 0) (Times (Var "y") (Var "y"))) (ReadFromChannel "b" "stdIn") (Ass "y" (Times (Var "b") (Var "c"))))))))
         ]

minimalClassificationVstimingClassificationDomPathsCounterExample4 :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExample4 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(If CFalse (ForC 2 (Seq (Seq Skip (ReadFromChannel "b" "lowIn1")) (ForC 2 (SpawnThread 2)))) (If CFalse (Seq (Seq (SpawnThread 3) (ReadFromChannel "z" "lowIn1")) (Seq (ReadFromChannel "x" "lowIn1") (ReadFromChannel "y" "lowIn1"))) (If CFalse (Seq (Ass "a" (Val 1)) (ReadFromChannel "x" "lowIn1")) (Seq (PrintToChannel (Val 17) "stdOut") (ReadFromChannel "a" "stdIn"))))) ),
          (2,(ForV "b" (Seq (Ass "b" ((Var "b") `Plus` (Val (-1)))) (Seq (ForC 2 (Seq (ReadFromChannel "a" "stdIn") (Ass "c" (Times (Var "b") (Var "a"))))) (If (Leq (Val 0) (Times (Var "c") (Var "b"))) (ForC 1 (ReadFromChannel "y" "stdIn")) (Seq Skip (Ass "x" (Times (Var "b") (Var "c")))))))) ),
          (3,(ForC 2 (If CFalse (Seq (Seq Skip (PrintToChannel (Val 1) "stdOut")) (Seq Skip Skip)) (Seq (Seq Skip (PrintToChannel (Val (-1)) "stdOut")) (Seq (ReadFromChannel "c" "lowIn1") (Ass "x" (Times (Var "c") (Var "c"))))))))
         ]


minimalClassificationVstimingClassificationDomPathsCounterExampleEssential :: Program Gr
minimalClassificationVstimingClassificationDomPathsCounterExampleEssential = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, Skip                             `Seq`
              Ass "x" (Val 0)                  `Seq`
              SpawnThread 2                    `Seq`
              ReadFromChannel "h" "stdIn"      `Seq`
              If (Leq (Var "h") (Val 0))
                 (Skip `Seq` Skip)
                 (Skip)                        `Seq`
              Ass "x" (Val 1)
          ),
          (2, Skip                             `Seq`
              ReadFromChannel "x" "lowIn1"
          )
          ]


-- This was spurioulsy reported as a counterExample to allSound [ isSecureTimingClassificationDomPaths, isSecureTimingClassification, isSecureTimingClassificationSimple, isSecureMinimalClassification, giffhornLSOD ] in some test run: probably just bad luck in sampling executions ¯\__(ツ)__/¯
notReallyUnsound :: Program Gr
notReallyUnsound = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(Seq (Seq (Seq (Seq Skip (Ass "z" (Val 0))) (ForV "z" Skip)) (Seq (Seq (SpawnThread 2) (PrintToChannel (Times (Var "z") (Var "z")) "stdOut")) (If (Leq (Val 0) (Times (Var "z") (Var "z"))) (ReadFromChannel "c" "lowIn1") (ReadFromChannel "b" "stdIn")))) (Seq (ForC 2 (Seq (PrintToChannel (Times (Var "z") (Var "z")) "stdOut") Skip)) (ForC 2 (Seq (SpawnThread 3) Skip))))),
          (2,(Seq (ForC 2 (ForV "z" (ForC 2 (Ass "y" (Times (Var "z") (Var "z")))))) (If (Leq (Val 0) (Times (Var "z") (Var "z"))) (Seq (ForC 1 (PrintToChannel (Times (Var "z") (Var "z")) "stdOut")) (ForC 2 (ReadFromChannel "x" "lowIn1"))) (ForV "z" (If (Leq (Val 0) (Times (Var "z") (Var "z"))) (Ass "x" (Times (Var "z") (Var "z"))) (ReadFromChannel "x" "lowIn1")))))),
          (3,(If (Leq (Val 0) (Times (Var "z") (Var "z"))) (ForV "z" (If (Leq (Val 0) (Times (Var "z") (Var "z"))) (Seq (PrintToChannel (Times (Var "z") (Var "z")) "stdOut") (Ass "a" (Times (Var "z") (Var "z")))) (Seq (PrintToChannel (Times (Var "z") (Var "z")) "stdOut") (Ass "a" (Times (Var "z") (Var "z")))))) (ForV "z" (ForC 2 (Seq Skip (Ass "a" (Times (Var "z") (Var "z"))))))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(If CFalse (If CFalse (If CFalse (Seq (PrintToChannel (Val 42) "stdOut") Skip) (Seq (PrintToChannel (Val 42) "stdOut") (PrintToChannel (Val (-1)) "stdOut"))) (Seq (If CTrue (SpawnThread 2) (Ass "x" (Val 0))) (ForC 1 (PrintToChannel (Val 17) "stdOut")))) (Seq (ForC 1 (If CFalse (PrintToChannel (Val 17) "stdOut") (SpawnThread 3))) (If CTrue (Seq Skip (PrintToChannel (Val 0) "stdOut")) (ForC 2 Skip))))),
          (2,(ForC 2 (Seq (If CFalse (If CFalse (Ass "x" (Val 42)) (ReadFromChannel "c" "stdIn")) (Seq Skip (PrintToChannel (Val 1) "stdOut"))) (Seq (Seq (Ass "x" (Val 0)) (ReadFromChannel "b" "lowIn1")) (ForC 2 (Ass "c" (Times (Var "x") (Var "b")))))))),
          (3,(Seq (If CFalse (If CFalse (Seq (Ass "a" (Val 17)) Skip) (Seq (Ass "z" (Val 17)) (PrintToChannel (Times (Var "z") (Var "z")) "stdOut"))) (ForC 1 (Seq (PrintToChannel (Val 1) "stdOut") Skip))) (If CFalse (Seq (Seq Skip Skip) (Seq (Ass "c" (Val 42)) (PrintToChannel (Times (Var "c") (Var "c")) "stdOut"))) (Seq (ForC 2 (PrintToChannel (Val 17) "stdOut")) (Seq (Ass "y" (Val 0)) (ReadFromChannel "y" "stdIn"))))))
          ]


-- see notReallyUnsound
notReallyUnsound3 :: Program Gr
notReallyUnsound3 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, (Seq (ForC 1 (SpawnThread 2)) (If CTrue (ReadFromChannel "y" "lowIn1") (ReadFromChannel "c" "stdIn")))),
          (2, (Seq (Seq (Ass "a" (Val 0)) (PrintToChannel (Times (Var "a") (Var "a")) "stdOut")) (Seq (PrintToChannel (Times (Var "a") (Var "a")) "stdOut") (PrintToChannel (Times (Var "a") (Var "a")) "stdOut"))))
         ]

-- see notReallyUnsound
notReallyUnsound4 :: Program Gr
notReallyUnsound4 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(Seq (Seq (Ass "y" (Val 1)) (SpawnThread 3)) (If (Leq (Val 0) (Times (Var "y") (Var "y"))) (ReadFromChannel "y" "lowIn1") (Ass "y" (Times (Var "y") (Var "y")))))),
          (3,(If (Leq (Val 0) (Times (Var "y") (Var "y"))) (Seq (Ass "c" (Times (Var "y") (Var "y"))) (ReadFromChannel "c" "lowIn1")) (Seq (PrintToChannel (Times (Var "y") (Var "y")) "stdOut") (ReadFromChannel "b" "lowIn1"))))
         ]

-- see notReallyUnsound
notReallyUnsound5 :: Program Gr
notReallyUnsound5 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(Seq (Seq (SpawnThread 2) (Ass "c" (Val 1))) (Seq (Ass "c" (Times (Var "c") (Var "c"))) (PrintToChannel (Times (Var "c") (Var "c")) "stdOut")))),
          (2,(Seq (Seq (Ass "y" (Val (-1))) (Ass "a" (Times (Var "y") (Var "y")))) (Seq (ReadFromChannel "b" "lowIn1") (ReadFromChannel "x" "stdIn"))) )
         ]

-- see notReallyUnsound
notReallyUnsound6 :: Program Gr
notReallyUnsound6 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(Seq (Seq (SpawnThread 3) (SpawnThread 2)) (If CFalse (Ass "a" (Val 1)) (PrintToChannel (Val 0) "stdOut")))),
           (2,(If CFalse (If CFalse (Ass "c" (Val 1)) Skip) (Seq (PrintToChannel (Val (-1)) "stdOut") Skip))),
           (3,(ForC 1 (Seq Skip Skip)))
         ]

-- see notReallyUnsound
notReallyUnsound7 :: Program Gr
notReallyUnsound7 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(Seq (Seq (SpawnThread 2) (SpawnThread 3)) (If CTrue (PrintToChannel (Val (-1)) "stdOut") (ReadFromChannel "a" "stdIn")))),
          (2,(Seq (If CTrue (ReadFromChannel "y" "lowIn1") (ReadFromChannel "c" "lowIn1")) (ForC 2 (ReadFromChannel "a" "stdIn")))),
          (3,(If CTrue (Seq Skip (ReadFromChannel "y" "lowIn1")) (ForC 2 (ReadFromChannel "x" "lowIn1"))))
         ]

-- see notReallyUnsound
notReallyUnsound8 :: Program Gr
notReallyUnsound8 = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,(Seq (Seq (PrintToChannel (Val 0) "stdOut") (Ass "x" (Val 42))) (Seq (SpawnThread 2) (ReadFromChannel "x" "lowIn1")))),
          (2,(Seq (Seq (PrintToChannel (Times (Var "x") (Var "x")) "stdOut") (SpawnThread 3)) (ForV "x" (ReadFromChannel "b" "lowIn1")))),
          (3,(ForC 1 (If (Leq (Val 0) (Times (Var "x") (Var "x"))) (Ass "x" (Times (Var "x") (Var "x"))) (Ass "z" (Times (Var "x") (Var "x"))))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, (Seq (Seq Skip (PrintToChannel (Val 0) "stdOut")) (Seq (SpawnThread 2) (PrintToChannel (Val 1) "stdOut")))),
          (2, (Seq (Seq (PrintToChannel (Val 1) "stdOut") (SpawnThread 3)) (Seq (ReadFromChannel "y" "lowIn1") (ReadFromChannel "b" "lowIn1")))),
          (3, (If CFalse (Seq (ReadFromChannel "x" "stdIn") (Ass "z" (Times (Var "x") (Var "x")))) (Seq (PrintToChannel (Val (-1)) "stdOut") (PrintToChannel (Val (-1)) "stdOut"))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, (Seq (Seq (SpawnThread 3) (ReadFromChannel "c" "stdIn")) (ForC 1 (ReadFromChannel "a" "lowIn1"))) ),
          (3, (Seq (Seq (Ass "z" (Val (-1))) (ReadFromChannel "b" "lowIn1")) (Seq (PrintToChannel (Times (Var "b") (Var "z")) "stdOut") (ReadFromChannel "b" "lowIn1"))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, (Seq (Seq (SpawnThread 3) (SpawnThread 2)) (ForC 2 (ReadFromChannel "c" "lowIn1")))),
          (2, (ForC 2 (Seq (PrintToChannel (Val 1) "stdOut") (ReadFromChannel "x" "stdIn")))),
          (3, (Seq (ForC 1 (ReadFromChannel "c" "stdIn")) (ForC 2 (Ass "y" (Times (Var "c") (Var "c"))))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, (ForC 2 (Seq (ReadFromChannel "z" "lowIn1") (SpawnThread 2)))),
          (2, (Seq (Seq (PrintToChannel (Times (Var "z") (Var "z")) "stdOut") (PrintToChannel (Times (Var "z") (Var "z")) "stdOut")) (Seq Skip (SpawnThread 3)))),
          (3, (Seq (If (Leq (Val 0) (Times (Var "z") (Var "z")))
                      (PrintToChannel (Times (Var "z") (Var "z")) "stdOut")
                      (Ass "x" (Times (Var "z") (Var "z")))) (Seq (ReadFromChannel "a" "stdIn") (ReadFromChannel "x" "stdIn")))
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
  where p = compileAllToProgram code
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
  where p = compileAllToProgram code
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
            (1,(Seq (Seq (PrintToChannel (Val 42) "stdOut") (Ass "z" (Val 42))) (Seq (SpawnThread 3) (PrintToChannel (Times (Var "z") (Var "z")) "stdOut")))),
            (2,(If (Leq (Val 0) (Times (Var "z") (Var "z"))) (Seq (PrintToChannel (Times (Var "z") (Var "z")) "stdOut") (Ass "b" (Times (Var "z") (Var "z")))) (If (Leq (Val 0) (Times (Var "z") (Var "z"))) (ReadFromChannel "a" "lowIn1") Skip))),
            (3,(Seq (Seq (SpawnThread 2) (ReadFromChannel "c" "stdIn")) (Seq (Ass "c" (Times (Var "z") (Var "z"))) (ReadFromChannel "x" "lowIn1"))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
            (1,(Seq (Seq (Ass "a" (Val 17)) (SpawnThread 2)) (ForV "a" (Ass "z" (Times (Var "a") (Var "a")))))),
            (2,(Seq (ForV "a" (SpawnThread 3)) (If (Leq (Val 0) (Times (Var "a") (Var "a"))) (PrintToChannel (Times (Var "a") (Var "a")) "stdOut") (Ass "b" (Times (Var "a") (Var "a")))))),
            (3,(If (Leq (Val 0) (Times (Var "a") (Var "a"))) (Seq Skip (PrintToChannel (Times (Var "a") (Var "a")) "stdOut")) (ForC 1 (Ass "a" (Times (Var "a") (Var "a"))))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
            (1,(Seq (If CTrue Skip (ReadFromChannel "a" "lowIn1")) (Seq (PrintToChannel (Val 42) "stdOut") (SpawnThread 2)))),
            (2,(ForC 2 (Seq (ReadFromChannel "c" "lowIn1") (SpawnThread 3))) ),
            (3,(ForV "c" (If (Leq (Val 0) (Times (Var "c") (Var "c"))) (PrintToChannel (Times (Var "c") (Var "c")) "stdOut") (ReadFromChannel "a" "stdIn"))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
            (1, (Seq (Seq (SpawnThread 2) (PrintToChannel (Val 0) "stdOut")) (Seq (PrintToChannel (Val 0) "stdOut") (ReadFromChannel "b" "lowIn1")))),
            (2, (ForC 2 (Seq (ReadFromChannel "x" "lowIn1") (ReadFromChannel "x" "lowIn1"))))
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
  where p = compileAllToProgram code
        code = Map.fromList $ [
            (1,(Seq (Seq (Ass "y" (Val 17)) (Ass "a" (Times (Var "y") (Var "y")))) (ForC 2 (SpawnThread 3)))),
            (2,(ForC 1 (Seq (ReadFromChannel "c" "stdIn") (ReadFromChannel "c" "stdIn")))),
            (3,(ForV "y" (Seq (PrintToChannel (Times (Var "y") (Var "y")) "stdOut") (SpawnThread 2))))
         ]







controlDepExample :: Program Gr
controlDepExample = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1, (ForC 1
                 (If CFalse (Seq (PrintToChannel (Val 0) "stdOut") (PrintToChannel (Val 1) "stdOut"))
                            (ForC 1 (ReadFromChannel "c" "lowIn1"))
                 )
              ) `Seq`
              (Ass "x" (Val 0))
          )
         ]


simpleBlocking :: Program Gr
simpleBlocking =  p { observability = defaultObservabilityMap (tcfg p) } 
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                            `Seq`
           SpawnThread 2                   `Seq`
           SpawnThread 3
          ),
          (2, Skip `Seq`
              ReadFromChannel "z" stdIn    `Seq`
              PrintToChannel (Val 2) stdOut
          ),
          (3, Skip `Seq`
              ReadFromChannel "z" stdIn2   `Seq`
              PrintToChannel (Val 1) stdOut
          )
         ]



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
              $(withName 'directFlow),
              $(withName 'directFlowThread),
              $(withName 'noDirectFlowThread),
              $(withName 'indirectFlow),
              $(withName 'orderConflict),
              $(withName 'dubiousOrderConflict),
              $(withName 'cdomIsBroken),
              $(withName 'cdomIsBroken'),
              $(withName 'cdomIsBroken2),
              $(withName 'noninterferingSchedulers),
              $(withName 'timingDependenceExample),
              $(withName 'figure5left),
              $(withName 'figure5right),
              $(withName 'figure5right'),
              $(withName 'figure5right''),
              $(withName 'ijisLSODistkaputt),
              $(withName 'minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD),
              $(withName 'minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD2),
              $(withName 'minimalClassificationIsLessPreciseThanSimonClassification),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExampleMartin),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExampleSimon),
              $(withName 'timingSecureButNotCombinedTimingSecure),
              $(withName 'timingSecureButNotCombinedTimingSecureGenerated),
              $(withName 'someGeneratedProgram),
              $(withName 'anotherGeneratedProgram),
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
              $(withName 'forIf)
            ] ++
            precisionCounterExamples ++
            []

-- These are counter-Examples to the claim that minimalClassification (i.e.: the old version, not the "atUses" version)
-- is strictly more precise than timingClassification.
precisionCounterExamples = [
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample2),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample3),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample4),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExampleEssential),
              $(withName 'minimalClassificationVstimingClassificationDomPathsCounterExample2Essential)
            ]


failingCdomIsCdom' = [
              $(withName 'example8),
              $(withName 'threadSpawn1),
              $(withName 'cdomIsBroken),
              $(withName 'cdomIsBroken'),
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


failingNticd = [
              $(withName 'exampleNticd),
              $(withName 'exampleNticd2SmnF5)
            ]

failingNtscd = [
              $(withName 'exampleNtscd),
              $(withName 'exampleNtscd2)
            ]

failingSnmF3F5 = [
              $(withName 'exampleNticd2SmnF5),
              $(withName 'exampleSmnF5)
            ]


interestingDodWod :: [(String, Gr () ())]
interestingDodWod = [
              $(withName 'wodDodInteresting1),
              $(withName 'wodDodInteresting2),
              $(withName 'dodSuperFastCounterExample),
              $(withName 'dodSuperFastCounterExample2),
              $(withName 'dodSuperFastCounterExample3),
              $(withName 'dodSuperFastCounterExample4),
              $(withName 'dodSuperFastCounterExample5),
              $(withName 'dodSuperFastCounterExample6)
            ]
