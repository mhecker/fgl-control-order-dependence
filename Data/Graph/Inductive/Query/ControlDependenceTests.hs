module Data.Graph.Inductive.Query.ControlDependenceTests where


import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.Dataflow


import IRLSOD

import System.Process

import Data.Set
import Data.Map as Map

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
exit = 12

graph :: Gr CFGNode CFGEdge
graph = mkGraph (genLNodes entry exit)  $   [(1,2,nop),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,nopuse),(6,7,nop)]
                                        ++  [(7,8,true),(8,9,nop),(9,7,nop),(7,10,false),(10,11,nopuse),(11,12,nop)]


graph' :: Gr CFGNode CFGEdge
graph' = mkGraph (genLNodes entry exit) $   [(1,2,nop),(2,3,true),(2,4,false),(3,5,nop),(4,5,nop),(5,6,nopuse),(6,7,nop)]
                                        ++  [(7,8,nop),(8,9,nop),(9,10,nop),(10,7,false),(10,11,true),(11,12,nopuse)]



-- | generate list of labeled nodes
genLNodes :: (Enum a) => a -> Int -> [LNode a]
genLNodes q i = take i (zip [1..] [q..])


initialConfiguration :: Configuration
initialConfiguration = ([entry], Map.empty, Map.fromList [(defaultChannel, cycle [1..5])])


run :: Gr CFGNode CFGEdge -> Int -> (ControlState,GlobalState)
run graph n = (ns,σ)
  where (ns, σ, i) = iterate (myhead. (step graph)) initialConfiguration !! n
                     -- head $ step graph initialConfiguration
        myhead (x:xs) = x
        myhead _ = error "rofl"


test graph = do
  let dot = showDot (fglToDot graph)
  writeFile "file.dot" dot
  system "dot -Tpng -ofile.png file.dot"
  system "display file.png"



