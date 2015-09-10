module Program.Examples where


import Program
import IRLSOD

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode


{-    1
      2-------
      7       3
    8       4   5
    9         6
      10
      11
      12
-}
example1 :: Program Gr
example1 = Program {
    tcfg = mkGraph (genLNodes 1 12) $ 
                        [(1,2,nop),(2,3,spawn),(3,4,false),(3,5,true),(4,6,Print unused stdOut),(5,6,nop)]
                    ++  [(2,7,nop),(7,8,true),(8,9,nop),(9,10,nop),(10,11,true),(10,7,false),(11,12,nopuse)],
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf
   }
  where staticThreadOf n 
         | n `elem` [1,2,7,8,9,10,11,12] = 1 
         | n `elem` [3,4,5,6] = 2
         | otherwise = error "uknown node"
        entryOf 1 = 1
        entryOf 2 = 3
        exitOf 1 = 12
        exitOf 2 = 6



{-    1
      2
    3   4
      5
      6
    7
    8
      9
      10
-}
example2 :: Program Gr
example2 = Program {
    tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,nop),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,nopuse),(6,7,nop)]
                   ++  [(7,8,true),(8,9,nop),(9,7,nop),(7,10,false),(10,11,nopuse),(11,12,nop)],
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf
   }
  where staticThreadOf n 
         | n `elem` [1..12] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 12



{-    1
      2
    3   4
      5
      6
    7
    8
      9
      10
-}
example2' :: Program Gr
example2' = Program {
    tcfg = mkGraph (genLNodes 1 12)  $
                       [(1,2,nop),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,nopuse),(6,7,nop)]
                   ++  [(7,8,nop),(8,9,nop),(9,10,nop),(10,7,false),(10,11,true),(11,12,nopuse)],
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf
   }
  where staticThreadOf n 
         | n `elem` [1..12] = 1 
         | otherwise = error "uknown node"
        entryOf 1 = 1
        exitOf 1 = 12

{-
     1
     2 -----   3
     5         4
     6
     7
-}
example3 :: Program Gr
example3 = Program {
    tcfg = mkGraph (genLNodes 1 7)  $
                       [(1,2,nop),(2,3,spawn),(3,4,Assign "x" (Val 17))]
                   ++  [(2,5,nop),(5,6,Assign "x" (Val 4)),(6,7,Print "x" stdOut)],
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList [1,2],
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf
   }
  where staticThreadOf n
         | n `elem` [1,2,5,6,7] = 1
         | n `elem` [3,4]      = 2
         | otherwise = error "unknown node"
        entryOf 1 = 1
        entryOf 2 = 3
        exitOf 1 = 7
        exitOf 2 = 4


-- entry :: CFGNode
-- entry = 1

-- exit :: CFGNode
-- exit = 12

-- graph :: Gr CFGNode CFGEdge
-- graph = 


-- graph' :: Gr CFGNode CFGEdge
-- graph' = mkGraph (genLNodes entry exit) $  
