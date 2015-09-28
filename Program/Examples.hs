module Program.Examples where


import Program

import Program.For
import Control.Monad.Gen

import IRLSOD

import Unicode

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode


defaultInput  = Map.fromList [ (stdIn, cycle [ 1, 2]) ]
defaultInput' = Map.fromList [ (stdIn, cycle [-1,-2]) ]

defaultChannelClassification channel
 | channel == stdIn  = High
 | channel == stdOut = Low
 | otherwise = error $ "unknown channel: " ++ channel

defaultClassification :: Graph gr => gr CFGNode CFGEdge -> Node -> SecurityLattice
defaultClassification gr n = (∐) (fmap cl (lsuc gr n))
  where cl (n',Print _ channel) = defaultChannelClassification channel
        cl (n',Read  _ channel) = defaultChannelClassification channel
        cl _                    =  Undefined


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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
    clInit = defaultClassification tcfg
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
        exitOf 4 = 7
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
    clInit = defaultClassification tcfg
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
joachim2 = p { clInit = defaultClassification (tcfg p) }
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
          (2, Ass "l" (Val 0)),
          (3, Ass "l" (Val 1)),
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
joachim3 = p { clInit = defaultClassification (tcfg p) }
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
noFlow = p { clInit = defaultClassification (tcfg p) }
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
directFlow = p { clInit = defaultClassification (tcfg p) }
  where p = compileAllToProgram code
        code = Map.fromList $ [
          (1,
           Skip                          `Seq`
           ReadFromChannel "h" stdIn     `Seq`
           PrintToChannel  (Var "h")  stdOut
          )
         ]

directFlowThread :: Program Gr
directFlowThread = p { clInit = defaultClassification (tcfg p) }
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
noDirectFlowThread = p { clInit = defaultClassification (tcfg p) }
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
indirectFlow = p { clInit = defaultClassification (tcfg p) }
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
orderConflict = p { clInit = defaultClassification (tcfg p) }
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
dubiousOrderConflict = p { clInit = defaultClassification (tcfg p) }
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
cdomIsBroken = p { clInit = defaultClassification (tcfg p) }
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
cdomIsBroken' ist ein Beispiel für unsounde, bei der "timingClassification"-Analyse berechnete clt-Informationen,
wenn man cdomChef (statt: cdomMohrEtAl) verwendet.

> showCounterExamplesPniFor cdomIsBroken' defaultInput defaultInput'
i  = fromList [("stdIn",[1,2,1,2,1])] ...     i' = fromList [("stdIn",[-1,-2,-1,-2,-1])] ... 
-----------------
p  = 57 % 64 ≃ 0.890625                                  p' = 2015 % 2048 ≃ 0.98388671875
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
p  = 7 % 64 ≃ 0.109375                                  p' = 33 % 2048 ≃ 0.01611328125
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
cdomIsBroken' = p { clInit = defaultClassification (tcfg p) }
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
cdomIsBroken2 = p { clInit = defaultClassification (tcfg p) }
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
