{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.TimingDependence where

import Data.Maybe(fromJust)

import Data.List(foldl')

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import IRLSOD
import Program

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.TransClos


timingDependenceGraphP :: DynGraph gr => Program gr -> gr CFGNode ()
timingDependenceGraphP p@(Program { tcfg }) =
    timingDependenceGraph tcfg 
    -- foldr mergeTwoGraphs empty [ timingDependenceGraph (nfilter (\node -> staticThreadOf node == thread) tcfg)
    --                                                    (exitOf thread)
    --                            | thread <- Set.toList staticThreads ]

timingDependenceGraph :: DynGraph gr => gr a CFGEdge -> gr a ()
timingDependenceGraph graph = mkGraph (labNodes graph) [ (n,n',()) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = timingDependence graph 

timingDependence :: DynGraph gr => gr a CFGEdge -> Map Node (Set Node)
timingDependence graph = Map.fromList $
    [ (n, Set.fromList [ m | (n',n'') <- [ (n',n'') | (n',e')   <- lsuc graph n, e'  /= Spawn,
                                                      (n'',e'') <- lsuc graph n, e'' /= Spawn,
                                                      n' /= n''],
--                              m <- postDom ! n,
                              m  <-    (suc trnsclos n'),
                              m `elem` (suc trnsclos n'')
                       ]
      )
     | n <- nodes graph
    ]
    where -- postDom = Map.fromList $ dom (grev graph) exit
          trnsclos = trc graph
