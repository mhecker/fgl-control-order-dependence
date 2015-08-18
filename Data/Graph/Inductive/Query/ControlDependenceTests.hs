module Data.Graph.Inductive.Query.ControlDependenceTests where


import Data.Graph.Inductive.Query.ControlDependence

import IRLSOD

import System.Process

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.PatriciaTree

import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Dot

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

entry :: CFGNode
entry = 1

exit :: CFGNode
exit = 10

graph :: Gr CFGNode CFGEdge
graph = mkGraph (genLNodes entry exit)  $   [(1,2,nop),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,nop)]
                                        ++  [(6,7,true),(7,8,nop),(8,6,nop),(6,9,false),(9,10,nop)]


graph' :: Gr CFGNode CFGEdge
graph' = mkGraph (genLNodes entry exit) $   [(1,2,nop),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,nop)]
                                        ++  [(6,7,nop),(7,8,nop),(8,9,nop),(9,6,false),(9,10,true)]



-- | generate list of labeled nodes
genLNodes :: (Enum a) => a -> Int -> [LNode a]
genLNodes q i = take i (zip [1..] [q..])


test = do
  let dot = showDot (fglToDot graph')
  writeFile "file.dot" dot
  system "dot -Tpng -ofile.png file.dot"
  system "display file.png"
