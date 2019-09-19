{-# LANGUAGE NamedFieldPuns #-}

module ExecutionTree where
import IRLSOD
import Program

import Data.Tree (Tree(..))
import qualified Data.Tree as Tree

import Data.List (partition)

import Data.Util

import Control.Monad(forM_)

import Data.Map (Map)
import qualified Data.Map as Map



import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph

-- Knoten (n,e) steht für einen Kontrollzustand n, in den über e gelangt wurde
type ExecutionTree = Tree  (CFGNode,CFGEdge, ThreadLocalState)

type ControlStateTree  = ExecutionTree
type ConfigurationTree = (ControlStateTree,GlobalState,Input)


treeStep :: Graph gr => gr CFGNode CFGEdge -> ConfigurationTree-> [ConfigurationTree]
treeStep graph (Node (n,e0,tlσ) [], globalσ, i)
    | ([],[])                       <- (successors,spawn) = []
    | [((n',e),globalσ', tlσ', i')] <- successors = [(Node (n,e0,tlσ) $ [Node (n',e, tlσ') [] ] ++ [ Node (n',e, Map.empty) [] | (n',e) <- spawn], globalσ', i')]
    | []                            <- successors = [(Node (n,e0,tlσ) $                            [ Node (n',e, Map.empty) [] | (n',e) <- spawn], globalσ , i )]
    | otherwise = error "nichtdeterministisches Programm"
  where (spawn,normal) = partition (\(n', e) -> case e of { Spawn -> True ; _ -> False }) $ lsuc graph n
        successors     = concat $ fmap (\(n',e) -> fmap (\(globalσ',tlσ', i') -> ((n',e),globalσ',tlσ',i')) (stepFor e (globalσ,tlσ,i)) ) normal
treeStep graph (Node  (n,e0,tlσ) ts,σ,i) =  [ (Node (n,e0,tlσ) (fmap (\(t,_,_) -> t) ts'), σ', i') | (ts',(_,σ', i')) <- chooseOne (treeStep graph) [ (t,σ,i) | t <- ts]]
  where chooseOne :: (a -> [a]) -> [a] -> [([a],a)]
        chooseOne f [] = []
        chooseOne f (a:as) = [(a':as,a') | a' <- f a] ++ [ (a:others,b') | (others,b') <- chooseOne f as]


initialConfigurationTree :: Graph gr => Program gr -> Input ->  ConfigurationTree
initialConfigurationTree (Program { mainThread, entryOf, procedureOf }) input = (Node (entryOf (procedureOf mainThread), Spawn, Map.empty) [], GlobalState Map.empty Map.empty, input)


showAllFinalTreeStates program input = do
  forM_ (allFinalTreeStates program input) (\(t,sigma) -> do
     putStrLn "-----------------"
     putStrLn $ Tree.drawTree $ fmap show $ t
     putStrLn $ show $ sigma
     putStrLn "-----------------"
   )

allFinalTreeStates :: Graph gr => Program gr -> Input -> [(ControlStateTree,GlobalState)]
allFinalTreeStates program@(Program { tcfg }) input = iter [] [initialConfigurationTree program input ]
  where hide (a,b,c)      = (a,b)
        iter finals []    = fmap hide finals
        iter finals confs = iter (newfinals++finals) $ concat $ fmap (treeStep tcfg) confs
          where newfinals = [conf | conf <- confs, treeStep tcfg conf == []] 
