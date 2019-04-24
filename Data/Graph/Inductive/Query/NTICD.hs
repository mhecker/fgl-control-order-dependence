{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
#define PDOMUSESDF
module Data.Graph.Inductive.Query.NTICD where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS (scc, dfs)
import Data.Graph.Inductive.Query.Dominators (dom)

import Util (the)
import Unicode

import Data.Graph.Inductive.Util (delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominance ( sinkPathsFor, inSinkPathFor,  maximalPathsFor, inPathFor, sinkdomOf, mdomOf, mdomOfLfp, sinkdomOfGfp, domOfGfp,  sinkdomsOf, mdomsOf)




ntscdViaMDom g = Map.fromList [ (n, Set.fromList [m | nl <- suc g n,  m <- Set.toList $ mdom ! nl, (∃) (suc g n) (\nr -> not $ m ∈ mdom ! nr), m /= n]) | n <- nodes g]
  where mdom = mdomOfLfp g


nticdViaSinkDom g = Map.fromList [ (n, Set.fromList [m | nl <- suc g n,  m <- Set.toList $ sinkdom ! nl, (∃) (suc g n) (\nr -> not $ m ∈ sinkdom ! nr), m /= n]) | n <- nodes g]
  where sinkdom = sinkdomOfGfp g





{- The definition of nticd -}
nticdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
nticdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph, nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inPath` (nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inPath` (nl,path))
                                         ]
                       )
                     | ni <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inPath = inSinkPathFor graph




{- The definition of ntscd -}
ntscdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntscdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (maximalPaths ! nk) (\path ->       nj `inPath` (nk,path)),
                                                (∃) (maximalPaths ! nl) (\path -> not $ nj `inPath` (nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.


ntindDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntindDef g = Map.fromList [ (n, onPathBetween (suc g n) (Set.toList $ sinkdoms ! n) ∖ (Set.insert n $ sinkdoms ! n)) | n <- nodes g ]
  where sinkdoms = sinkdomsOf g
        onPathBetween ss ts = fwd
          where g' = foldr (flip delSuccessorEdges) g ts
                fwd = Set.fromList $  dfs ss g'

ntsndDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntsndDef g = Map.fromList [ (n, onPathBetween (suc g n) (Set.toList $ mdoms ! n) ∖ (Set.insert n $ mdoms ! n)) | n <- nodes g ]
  where mdoms = mdomsOf g
        onPathBetween ss ts = fwd
          where g' = foldr (flip delSuccessorEdges) g ts
                fwd = Set.fromList $  dfs ss g'

