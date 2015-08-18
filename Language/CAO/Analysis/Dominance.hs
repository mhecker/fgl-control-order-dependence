{-  CAO Compiler
    Copyright (C) 2014 Cryptography and Information Security Group, HASLab - INESC TEC and Universidade do Minho

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>. -}

{-# LANGUAGE PatternGuards #-}

{- |
Module      :  $Header$
Description :  Graph dominance algorithm.
Copyright   :  (C) 2014 Cryptography and Information Security Group, HASLab - INESC TEC and Universidade do Minho
License     :  GPL

Maintainer  :  Paulo Silva <paufil@di.uminho.pt>
Stability   :  experimental
Portability :  non-portable

Graph dominance algorithm.
-}

module Language.CAO.Analysis.Dominance 
    ( genDomTree
    , predecessors
    , successors
    , domFront
    , invertMap
    ) where
    
import Data.Graph
import Data.List hiding ( intersect )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


--------------------------------------------------------------------------------
{- DOMINATOR TREE -}
-- pag 13

-- for all nodes, b /* initialize the dominators array */
-- doms[b] <- Undefined
-- doms[start node] <- start node
-- Changed <- true
-- while (Changed)
--    Changed <- false
--    for all nodes, b, in reverse postorder (except start node)
--      new idom <- first (processed) predecessor of b /* (pick one) */
--      for all other predecessors, p, of b
--        if doms[p] /= Undefined /* i.e., if doms[p] already calculated */
--          new idom <- intersect(p, new idom)
--      if doms[b] /= new idom
--        doms[b] <- new idom
--        Changed <- true
--

genDomTree :: Graph -> Map Vertex Vertex
genDomTree g = let
        (ns, ss) = partition withPreds (vertices g)
        initSelf = foldl' (\m n -> Map.insert n n m) Map.empty ss
    in genDomTree' ns initSelf
    where 
    -- Fixpoint: this could be improved to avoid using equality
    genDomTree' :: [Vertex] -> Map Vertex Vertex -> Map Vertex Vertex
    genDomTree' ns doms = let
            doms' = foldl' (upDomTree g) doms ns
        in if doms' == doms then doms else genDomTree' ns doms'

    withPreds :: Vertex -> Bool
    withPreds = not . null . predecessors g

upDomTree :: Graph -> Map Vertex Vertex -> Vertex -> Map Vertex Vertex
upDomTree g doms b = Map.alter alterNewIdiom b doms
    where 
    alterNewIdiom :: Maybe Vertex -> Maybe Vertex
    alterNewIdiom = const $ Just $ getNewIdiom $ predecessors g b

    getNewIdiom :: [Vertex] -> Vertex
    getNewIdiom (p:ps) = foldl' fNewIdiom p ps
    getNewIdiom _      = error $ "<Language.CAO.Analysis.Dominance>.\
        \<updDomTree>: no predecessors!"

    fNewIdiom :: Vertex -> Vertex -> Vertex
    fNewIdiom ni p = if Map.member p doms then intersect p ni doms else ni

predecessors :: Graph -> Vertex -> [Vertex]
predecessors g v = [ a | (a, b) <- edges g, b == v]

successors :: Graph -> Vertex -> [Vertex]
successors   g v = [ b | (a, b) <- edges g, a == v]

--function intersect(b1, b2) returns node 
--	finger1 <- b1
--	finger2 <- b2 
--	while (finger1 /= finger2)
--		while (finger1 < finger2) 
--			finger1 = doms[finger1]
--		while (finger2 < finger1) 
--			finger2 = doms[finger2]
--	return finger1

intersect :: Vertex -> Vertex -> Map Vertex Vertex -> Vertex
intersect v1 v2 doms
    = maximum [ f1 | f1 <- follow v1 , f1 `elem` follow v2 ]
    where 
    follow :: Vertex -> [Vertex]
    follow v = case Map.lookup v doms of
        Just v' | v > v' -> v : follow v'
        _                -> [v]

--------------------------------------------------------------------------------
---- Dominance Frontier --------------------------------------------------------

--for all nodes, b
--  if the number of predecessors of b >= 2
--    for all predecessors, p, of b
--      runner <- p
--      while runner /= doms[b]
--        add b to runner's dominance frontier set
--        runner = doms[runner]

domFront :: Graph -> Map Vertex (Set Vertex)
domFront g = foldl' (nodeDomFront g doms) Map.empty $ vertices g 
    where 
    doms :: Map Vertex Vertex
    doms = genDomTree g


nodeDomFront :: Graph
             -> Map Vertex Vertex
             -> Map Vertex (Set Vertex)
             -> Vertex
             -> Map Vertex (Set Vertex)
nodeDomFront g doms df b = let
        preds = predecessors g b
    in case preds of
        _:_:_ -> foldl' addDoms df preds
        _     -> df
    where 
    addDoms :: Map Vertex (Set Vertex)
            -> Vertex
            -> Map Vertex (Set Vertex)
    addDoms df' = foldl' addDom df' . follow
        
    addDom :: Map Vertex (Set Vertex)
           -> Vertex
           -> Map Vertex (Set Vertex)
    addDom = flip (Map.alter dfSet)

    dfSet :: Maybe (Set Vertex) -> Maybe (Set Vertex)
    dfSet Nothing  = Just $ Set.singleton b
    dfSet (Just s) = Just $ Set.insert b s
        
    follow :: Vertex -> [Vertex] 
    follow r = case Map.lookup r doms of
        Just d | d /= r -> r : follow d
        _               -> [r]

--------------------------------------------------------------------------------
invertMap :: Map Vertex Vertex -> Map Vertex [Vertex]
invertMap domTree = Map.foldrWithKey aux (Map.map (const []) domTree) domTree
    where
    aux :: Vertex -> Vertex -> Map Vertex [Vertex] -> Map Vertex [Vertex]
    aux k v m = if k == v 
        then m
        else let newVal = k : Map.findWithDefault [] v m
             in  Map.insert v newVal m

