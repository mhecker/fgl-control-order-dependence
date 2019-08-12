{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.TimingDependence where

import Data.Maybe(fromJust)

import Data.List(foldl')

import Unicode((∊),(⊔), (∐))
import Util(invert'')

                
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
import Data.Graph.Inductive.Query.DFS (dfs)

import Data.Graph.Inductive.Query.PureTimingDependence (timingDependenceViaTwoFinger)


timingDependenceOldGraphP :: DynGraph gr => Program gr -> gr CFGNode ()
timingDependenceOldGraphP p@(Program { tcfg }) =
    timingDependenceOldGraph tcfg 
    -- foldr mergeTwoGraphs empty [ timingDependenceGraph (nfilter (\node -> staticThreadOf node == thread) tcfg)
    --                                                    (exitOf thread)
    --                            | thread <- Set.toList staticThreads ]

timingDependenceOldGraph :: DynGraph gr => gr a CFGEdge -> gr a ()
timingDependenceOldGraph graph = mkGraph (labNodes graph) [ (n,n',()) | (n,n's) <- Map.toList dependencies, n' <- Set.toList n's]
  where dependencies = timingDependenceOld graph 

timingDependenceOld :: DynGraph gr => gr a CFGEdge -> Map Node (Set Node)
timingDependenceOld graph = Map.fromList $
    [ (n, Set.fromList [ m | (n',n'') <- [ (n',n'') | (n',e')   <- lsuc graph n, e'  /= Spawn,
                                                      (n'',e'') <- lsuc graph n, e'' /= Spawn,
                                                      n' /= n''],
--                              m <- postDom ! n,
                              m  <-    (suc trnsclos n'),
                              m ∊ (suc trnsclos n'')
                       ]
      )
     | n <- nodes graph
    ]
    where -- postDom = Map.fromList $ dom (grev graph) exit
          trnsclos = trc graph



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
timingDependence graph =
       td
     ⊔ (∐) [ Map.fromList [ (n, ms) ] | (m,m',Spawn) <- labEdges graph, let ms = Set.fromList $ dfs [m'] graph, n <- Set.toList $ Map.findWithDefault Set.empty m td']
    where td = Map.mapWithKey Set.delete $ timingDependenceViaTwoFinger graphNoSpawn
          td' = invert'' td
          graphNoSpawn = efilter (not . isSpawn) graph
            where isSpawn (n,m,Spawn) = True
                  isSpawn _           = False
