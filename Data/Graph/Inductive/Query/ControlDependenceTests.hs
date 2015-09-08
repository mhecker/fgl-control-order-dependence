module Data.Graph.Inductive.Query.ControlDependenceTests where


import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.Dataflow


import IRLSOD
import PNI
import ExecutionTree

import System.Process

import Data.Set
import Data.Map as Map

import Data.Tree (Tree(..))
import qualified Data.Tree as Tree

import Control.Monad(forM_)

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
                                               ++  [(2,7,nop),(7,8,Assign "x" (Val 4)),(8,12,Print "x" stdOut)]


-- | generate list of labeled nodes
genLNodes :: (Enum a) => a -> Int -> [LNode a]
genLNodes q i = take i (zip [1..] [q..])


initialConfiguration :: Configuration
initialConfiguration = ([entry], Map.empty, Map.fromList [(stdIn, cycle [1..5])])

initialConfigurationTree :: ConfigurationTree
initialConfigurationTree = (Node (entry,Spawn) [], Map.empty, Map.fromList [(stdIn, cycle [1..5])])


showAllFinalStates graph = do
  forM_ (allFinalStates graph) (\(ns,sigma) -> do
     putStrLn "-----------------"
     putStrLn $ show $ ns
     putStrLn $ show $ sigma
     putStrLn "-----------------"
   )

allFinalStates :: Gr CFGNode CFGEdge -> [(ControlState,GlobalState)]
allFinalStates graph = iter [] [initialConfiguration]
  where iter finals []    = fmap hide finals
        iter finals confs = iter (newfinals++finals) $ concat $ fmap (step graph) confs
          where newfinals = [conf | conf <- confs, step graph conf == []]


showAllFinishedTraces graph = do
  forM_ (allFinishedTraces graph) (\trace -> do
     putStrLn "-----------------"
     forM_ trace (\(ns,σ) -> do
        putStrLn $ show ns
        putStrLn $ show σ
        putStrLn $ ""
       )
    )


showAllFinishedEventTraces graph = do
  forM_ (allFinishedEventTraces graph) (\trace -> do
     putStrLn "-----------------"
     forM_ trace (\((ns,σ,i),(n,e),(ns',σ',i')) -> do
        putStrLn $ show ns
        putStrLn $ show σ
        putStr   $ "---"
        putStr   $ show (n,e)
        putStrLn $ "-->"
        putStrLn $ ""
       )
    )

allOutcomes :: Gr CFGNode CFGEdge -> [(Rational,GlobalState)]
allOutcomes graph = [ (prob graph trace, σ trace) | trace <- allFinishedEventTraces graph ]
  where σ trace = last $ [ σ | (_,_,(_,σ,_)) <- trace]

allFinishedEventTraces :: Gr CFGNode CFGEdge -> [FullTrace]
allFinishedEventTraces graph = fmap reverse $ iter [] [[(initialConfiguration, e, c')] | (e,c') <- eventStep graph initialConfiguration]
  where iter :: [FullTrace] -> [FullTrace] -> [FullTrace]
        iter finished []     = finished
        iter finished traces = iter (newfinished++finished) $ concat $ fmap (\((c,e,c'):cs) -> fmap (appendStep (c,e,c') cs) (eventStep graph c') ) traces
          where newfinished = [ trace | trace@((c,e,c'):cs) <- traces, eventStep graph c' == []]
                appendStep (c,e,c') cs ((n,e'),c'')  = (c',(n,e'),c''):(c,e,c'):cs


allFinishedTraces :: Gr CFGNode CFGEdge -> [[(ControlState,GlobalState)]]
allFinishedTraces graph = fmap reverse $ iter [] [[initialConfiguration]]
  where iter finished []     = fmap (fmap hide) finished
        iter finished traces = iter (newfinished++finished) $ concat $ fmap (\(c:cs) -> fmap (:(c:cs)) (step graph c)) traces
          where newfinished = [ trace | trace@(c:cs) <- traces, step graph c == []]


showAllFinalTreeStates graph = do
  forM_ (allFinalTreeStates graph) (\(t,sigma) -> do
     putStrLn "-----------------"
     putStrLn $ Tree.drawTree $ fmap show $t
     putStrLn $ show $ sigma
     putStrLn "-----------------"
   )

allFinalTreeStates :: Gr CFGNode CFGEdge -> [(ControlStateTree,GlobalState)]
allFinalTreeStates graph = iter [] [initialConfigurationTree]
  where iter finals []    = fmap hide finals
        iter finals confs = iter (newfinals++finals) $ concat $ fmap (treeStep graph) confs
          where newfinals = [conf | conf <- confs, treeStep graph conf == []] 

run :: Gr CFGNode CFGEdge -> Int -> (ControlState,GlobalState)
run graph n = (ns,σ)
  where (ns, σ, i) = iterate (head. (step graph)) initialConfiguration !! n


runAll :: Gr CFGNode CFGEdge -> Int -> [(ControlState,GlobalState)]
runAll graph n = fmap hide $ (iterate (concat . (fmap (step graph))) [initialConfiguration]) !! n



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
