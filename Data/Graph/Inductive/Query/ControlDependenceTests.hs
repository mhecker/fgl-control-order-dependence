module Data.Graph.Inductive.Query.ControlDependenceTests where


import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.Dataflow


import IRLSOD
import ExecutionTree

import System.Process

import Data.Set
import Data.Map as Map

import Data.Tree (Tree(..))
import qualified Data.Tree as Tree


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





{-    1
      2-------
      7       3
    8       4   5
    9         6
      10
      11
      12
-}

spawnGraph :: Gr CFGNode CFGEdge
spawnGraph = mkGraph (genLNodes entry exit) $   [(1,2,nop),(2,3,spawn),(3,4,false),(3,5,true),(4,6,nop),(5,6,nop)]
                                            ++  [(2,7,nop),(7,8,true),(8,9,nop),(9,10,nop),(10,11,true),(10,7,false),(11,12,nopuse)]


conflictGraph :: Gr CFGNode CFGEdge
conflictGraph = mkGraph (genLNodes entry exit) $   [(1,2,nop),(2,3,spawn),(3,4,Assign "x" (Val 17))]
                                               ++  [(2,7,nop),(7,8,Assign "x" (Val 4)),(8,12,nop)]


-- | generate list of labeled nodes
genLNodes :: (Enum a) => a -> Int -> [LNode a]
genLNodes q i = take i (zip [1..] [q..])


initialConfiguration :: Configuration
initialConfiguration = ([entry], Map.empty, Map.fromList [(defaultChannel, cycle [1..5])])

initialConfigurationTree :: ConfigurationTree
initialConfigurationTree = (Node (entry,Spawn) [], Map.empty, Map.fromList [(defaultChannel, cycle [1..5])])



showAllFinalStates graph = sequence_ $ fmap (\(t,sigma) -> sequence_ [ putStrLn "-----------------",  putStrLn $ Tree.drawTree $ fmap show $t, putStrLn $ show $ sigma, putStrLn "-----------------" ])  $ allFinalStates graph

allFinalStates :: Gr CFGNode CFGEdge -> [(ControlStateTree,GlobalState)]
allFinalStates graph = iter [] [initialConfigurationTree]
  where iter finals []    = fmap hide finals
        iter finals confs = iter (newfinals++finals) $ concat $ fmap (treeStep graph) confs
          where newfinals = [conf | conf <- confs, treeStep graph conf == []] 

run :: Gr CFGNode CFGEdge -> Int -> (ControlState,GlobalState)
run graph n = (ns,σ)
  where (ns, σ, i) = iterate (head. (step graph)) initialConfiguration !! n


showRunTree graph n = putStrLn $ Tree.drawTree $ fmap show t
  where (t,σ,i) = runTree graph n 

runTree :: Gr CFGNode CFGEdge -> Int -> (ControlStateTree,GlobalState,Input)
runTree graph n = iterate (head. (treeStep graph)) initialConfigurationTree !! n


test graph = do
  let dot = showDot (fglToDot graph)
  writeFile "file.dot" dot
  system "dot -Tpng -ofile.png file.dot"
  system "display file.png"



first (a,b,c) = a
