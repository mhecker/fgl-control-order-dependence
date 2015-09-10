{-# LANGUAGE NamedFieldPuns #-}
module Program where

import Data.Graph.Inductive.Graph

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode

import IRLSOD

type StaticThread = Integer

data Program gr = Program {
    tcfg :: gr CFGNode CFGEdge,
    staticThreadOf :: Node -> StaticThread,
    staticThreads  :: Set StaticThread,
    mainThread :: StaticThread,
    entryOf :: StaticThread -> Node,
    exitOf  :: StaticThread -> Node
}

-- | generate list of labeled nodes
genLNodes :: (Enum a) => a -> Int -> [LNode a]
genLNodes q i = take i (zip [1..] [q..])

vars :: Graph gr => Program gr -> Set Var
vars (Program { tcfg }) = Set.unions [ def tcfg n ∪ use tcfg n | n <- nodes tcfg]





