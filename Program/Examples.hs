{-# LANGUAGE TemplateHaskell #-}
module Program.Examples where


import Program
import Program.For
import Control.Monad.Gen

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

defaultInput  = Map.fromList [ (stdIn, cycle [ 1, 2]), (lowIn1, cycle [1,2,3,4]), (lowIn2, cycle [4,3,2,1]) ]
defaultInput' = Map.fromList [ (stdIn, cycle [-1,-2]), (lowIn1, cycle [1,2,3,4]), (lowIn2, cycle [4,3,2,1]) ]


defaultChannelObservability channel
 | channel == stdIn     = High
 | channel == lowIn1 = Low
 | channel == lowIn2 = Low
 | channel == stdOut = Low
 | channel == highOut1 = High
 | channel == highOut2 = High
 | otherwise = error $ "unknown channel: " ++ channel


defaultObservabilityMap :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification
defaultObservabilityMap gr = \n -> obsmap ! n where
 obsmap = Map.fromList $ [ (n, defaultObservability gr n) | n <- nodes gr ]
 defaultObservability gr n
   | levels == [] = Nothing
   | otherwise    = Just $ (∐) levels
  where levels = [ level | (n',e) <- lsuc gr n, Just level <- [obs (n',e)]]
        obs (n',Print _ channel) = Just $ defaultChannelObservability channel
        obs (n',Read  _ channel) = Just $ defaultChannelObservability channel
        obs _                    = Nothing


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
                   ++  [(7,8,true),(8,9,nop),(9,7,nop),(7,10,false),(10,11,Assign "x" (Var "x")),(11,12,nop)]



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
         | n `elem` ([1..7] ++ [10]) = 1
         | n `elem` ([8..9])         = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 8
        exitOf 1 = 10
        exitOf 2 = 9
        tcfg = mkGraph (genLNodes 1 10)  $
                       [(1,2,Assign "x" (Val 42)), (2,3,Read "h" stdIn),(3,4,Guard True (Leq (Var "h") (Var "h"))),(3,5,Guard False (Leq (Var "h") (Var "h"))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(7,8,Spawn),(7,10,Print (Var "x") stdOut),(8,9,Print (Var "x") stdOut)]


{-          1
   Read h   2 -----spawn-- 8
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
         | n `elem` ([1..7] ++ [10]) = 1
         | n `elem` ([8..9])         = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 8
        exitOf 1 = 10
        exitOf 2 = 9
        tcfg = mkGraph (genLNodes 1 10)  $
                       [(1,2,Assign "x" (Val 42)), (2,3,Read "h" stdIn),(3,4,Guard True (Leq (Var "h") (Var "h"))),(3,5,Guard False (Leq (Var "h") (Var "h"))),(4,6,nop),(5,6,nop),(6,7,nop)]
                   ++  [(2,8,Spawn),(7,10,Print (Var "x") stdOut),(8,9,Print (Var "x") stdOut)]






{-       1
         2 Read h
    ---  3----true --> 4
  f|     ^              5 if h
  a|     |            6   7
  l|     |              8  ----spawn--->  9 print l
  s|     | -------------                 10
  e|
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
                       [(1,2,Assign "x" (Val 42)), (2,3,Read "h" stdIn),(3,4,true),(3,11,false),(11,12,Print (Var "x") stdOut),
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
        \   /tmp = 100
          5
          |
          6 -----spawn ------------------>   201
          |                                   |   tmp2 = 100
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
                        (4,5,Assign "tmp" (Val 100)),
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

                        (201,202, Assign "tmp2" (Val 100)),

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
        \   /tmp = 100
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
                        (4,5,Assign "tmp" (Val 100)),
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



figure5left :: Program Gr
figure5left = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram code
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
        code = Map.fromList $ [
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
              $(withName 'figure5left),
              $(withName 'figure5right),
              $(withName 'figure5right'),
              $(withName 'figure5right''),
              $(withName 'ijisLSODistkaputt),
              $(withName 'minimalClassificationIsLessPreciseThanGiffhornLSODandRLSOD),
              $(withName 'timingSecureButNotCombinedTimingSecure),
              $(withName 'timingSecureButNotCombinedTimingSecureGenerated),
              $(withName 'someGeneratedProgram),
              $(withName 'anotherGeneratedProgram),
              $(withName 'aSecureGeneratedProgram),
              $(withName 'clientServerKeyExample),
              $(withName 'clientServerKeyExampleSimple),
              $(withName 'singleThreadedDelay)
            ]
