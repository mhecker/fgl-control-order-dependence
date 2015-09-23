{-# LANGUAGE NamedFieldPuns #-}

module ExecutionTree where
import IRLSOD
import Program

import Data.Tree (Tree(..))
import qualified Data.Tree as Tree

import Data.List (partition)


import Control.Monad(forM_)

import Data.Map (Map)
import qualified Data.Map as Map



import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph

-- Knoten (n,e) steht für einen Kontrollzustand n, in den über e gelangt wurde
type ExecutionTree = Tree  (CFGNode,CFGEdge)

type ControlStateTree  = ExecutionTree
type ConfigurationTree = (ControlStateTree,GlobalState,Input)


treeStep :: Graph gr => gr CFGNode CFGEdge -> ConfigurationTree-> [ConfigurationTree]
treeStep graph (Node (n,e0) [],σ,i)
    | ([],[])           <- (successors,spawn) = []
    | [((n',e),σ', i')] <- successors = [(Node (n,e0) $ [Node (n',e) [] ] ++ [ Node (n',e) [] | (n',e) <- spawn], σ', i')]
    | []                <- successors = [(Node (n,e0) $                      [ Node (n',e) [] | (n',e) <- spawn], σ , i )]
    | otherwise = error "nichtdeterministisches Programm"
  where (spawn,normal) = partition (\(n', e) -> case e of { Spawn -> True ; _ -> False }) $ lsuc graph n
        successors     = concat $ fmap (\(n',e) -> fmap (\(σ',i') -> ((n',e),σ',i')) (stepFor e (σ,i)) ) normal
treeStep graph (Node  (n,e0) ts,σ,i) =  [ (Node (n,e0) (fmap (\(t,_,_) -> t) ts'), σ', i') | (ts',(_,σ', i')) <- chooseOne (treeStep graph) [ (t,σ,i) | t <- ts]]
  where chooseOne :: (a -> [a]) -> [a] -> [([a],a)]
        chooseOne f [] = []
        chooseOne f (a:as) = [(a':as,a') | a' <- f a] ++ [ (a:others,b') | (others,b') <- chooseOne f as]


initialConfigurationTree :: Graph gr => Program gr -> Input ->  ConfigurationTree
initialConfigurationTree (Program { mainThread, entryOf }) input = (Node (entryOf mainThread,Spawn) [], Map.empty, input)


showAllFinalTreeStates program input = do
  forM_ (allFinalTreeStates program input) (\(t,sigma) -> do
     putStrLn "-----------------"
     putStrLn $ Tree.drawTree $ fmap show $t
     putStrLn $ show $ sigma
     putStrLn "-----------------"
   )

allFinalTreeStates :: Graph gr => Program gr -> Input -> [(ControlStateTree,GlobalState)]
allFinalTreeStates program@(Program { tcfg }) input = iter [] [initialConfigurationTree program input ]
  where iter finals []    = fmap hide finals
        iter finals confs = iter (newfinals++finals) $ concat $ fmap (treeStep tcfg) confs
          where newfinals = [conf | conf <- confs, treeStep tcfg conf == []] 
