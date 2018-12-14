{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert
module Data.Graph.Inductive.Query.LCA where

-- import Data.Ord (comparing)
-- import Data.Maybe(fromJust)
-- import Control.Monad (liftM, foldM, forM, forM_)

-- import Control.Monad.ST
-- import Data.STRef

-- import Data.Functor.Identity (runIdentity)
-- import qualified Control.Monad.Logic as Logic
-- import Data.List(foldl', intersect,foldr1, partition)

-- import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
-- import Data.Graph.Inductive.Query.Dominators (dom, iDom)
-- import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

-- import Algebra.Lattice
-- import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List
-- import Data.List ((\\), nub, sortBy, groupBy)


-- import IRLSOD
-- import Program

-- import Util(the, invert', invert'', foldM1, reachableFrom, treeDfs, toSet, fromSet)
import Util(toSet, fromSet, foldM1)
import Unicode


import Data.Graph.Inductive
-- import Data.Graph.Inductive.Query.TransClos
-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Query.Dependence
-- import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs)

import Debug.Trace
import Control.Exception.Base (assert)





lca imdom n m = let result = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m]) in assert (result == lcaSlow imdom n m) result
          where 
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    -- | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                    --            Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  assert (not $ n ∈ ms) $ 
                                  caseN
                  where caseN = case imdom ! n of
                                  Nothing ->                 lcaDownLin ms ns m
                                  Just n' -> if n' ∈ ns then lcaDownLin ms ns m  else lcaDown' (m, ms) (n', Set.insert n' ns)
                lcaDownLin ms ns m = assert (not $ m ∈ ns) $ lcaDown'' m ms
                  where lcaDown'' m ms = case imdom ! m of
                                        Nothing -> Nothing
                                        Just m' -> if m' ∈ ns then Just m' else
                                                   if m' ∈ ms then Nothing else lcaDown'' m' (Set.insert m' ms)


lcaSingleNodeSinks imdom nxs n m = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m])
          where
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    -- | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                    --            Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  assert (not $ n ∈ ms) $ 
                                  caseN
                  where caseN = case imdom ! n of
                                  Nothing -> lcaDownLin ns m
                                  Just n' -> lcaDown' (m, ms) (n', Set.insert n' ns)
                lcaDownLin ns m = assert (not $ m ∈ ns) $ lcaDown'' m
                  where lcaDown'' m = case imdom ! m of
                                        Nothing -> Nothing
                                        Just m' -> if m' ∈ ns then Just m' else lcaDown'' m'



lcaSlow :: Map Node (Maybe Node) -> Node -> Node -> Maybe Node
lcaSlow idom n m = lca' (n, Set.fromList [n]) (m, Set.fromList [m])
  where lca' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
        lca' (n,ns) (m,ms)
          | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                     Just m
          | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                     Just n
          | otherwise = -- traceShow ((n,ns), (m,ms)) $
                       case Set.toList $ ((toSet (idom ! n)) ∖ ns ) of
                         []   -> case Set.toList $ ((toSet (idom ! m)) ∖ ms ) of
                                   []   -> Nothing
                                   [m'] -> lca' (m', Set.insert m' ms) (n, ns)
                         [n'] -> lca' (m, ms) (n', Set.insert n' ns)




lcaRMyCDForNode dom (n, nada) (m, relevant) = assert (Set.null nada) $ lca' relevant [n] [m]
           where lca' :: Set Node -> [Node] -> [Node] -> (Node, Set Node)
                 lca' relevant ns@(n:_) ms@(m:_)
                    | mInNs = (m, relevant ∪ (Set.fromList ms) ∪ (Set.fromList beforeM))
                    | nInMs = (n, relevant ∪ (Set.fromList ns) ∪ (Set.fromList beforeN))
                    | otherwise = case dom ! n of
                                     Nothing -> case dom ! m of
                                                  Nothing -> error "is no tree"
                                                  Just m' -> lca' relevant (m':ms) ns
                                     Just n' -> lca' relevant ms (n':ns)
                   where mInNs = not $ List.null $ foundM
                         (afterM, foundM) = break (== m) ns
                         (mm:beforeM) = foundM

                         nInMs = not $ List.null $ foundN
                         (afterN, foundN) = break (== n) ms
                         (nn:beforeN) = foundN




lcaTimdomOfTwoFinger imdom (n, sn, ns) (m, sm, ms) = lca' imdom (n, sn, ns) (m, sm, ms)
          where 
                lca' :: Map Node (Maybe (Node, Integer)) -> (Node, Integer, Map Node (Set Integer)) -> (Node, Integer, Map Node (Set Integer)) -> Maybe (Node, Integer, Map Node (Set Integer))
                lca' c (n, sn, ns) (m, sm, ms)
                    | sn > sm = lca' c (m, sm, ms) (n, sn, ns)
                    | n ∈ Map.keysSet ms ∧ (      sn ∈ (ms ! n)) = -- traceShow ("A", (n,sn,ns), (m,sm,ms)) $
                                                           Just (n, sn, Map.fromList [(n, Set.fromList [sn])])
                    | n ∈ Map.keysSet ms ∧ (not $ sn ∈ (ms ! n)) = -- traceShow ("B", (n,sn,ns), (m,sm,ms)) $
                                  if   (∃) (ns ! n) (\sn' -> (∃) (Map.findWithDefault (Set.empty) n ms) (\sm' -> sm' < sn'))
                                     ∧ (∃) (ns ! n) (\sn' -> (∃) (Map.findWithDefault (Set.empty) n ms) (\sm' -> sm' > sn')) then Nothing else
                                  case Set.toList $ (Set.map fst $ toSet $ (c ! n)) of
                                     []  -> Nothing
                                     [_] -> let Just (n',sn') = c ! n
                                            in lca' c (m, sm, ms) (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns)
                    | otherwise = -- traceShow ("C", (n,sn,ns), (m,sm,ms)) $
                                  case Set.toList $ (Set.map fst $ toSet $ (c ! n)) of
                                     []  -> Nothing
                                     [_] -> let Just (n',sn') = c ! n
                                            in if n' ∈ Map.keysSet ns ∧ (Set.size (ms ! m) > 1) ∧ (not $ n' ∈ Map.keysSet ms) then Nothing else
                                               lca' c (m, sm, ms) (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns)

lcaRKnownM :: Map Node (Maybe Node) -> Node -> [Node] -> (Node, [Node])
lcaRKnownM dom c successors = case dom ! c of
                     Nothing -> assert (successors == []) $
                                (c, [c])
                     Just z  -> assert (successors /= []) $ 
                                (z, foldr relevant successors successors)
                       where relevant :: Node -> [Node] -> [Node]
                             relevant n ns
                               | n == z = ns
                               | otherwise = relevant n' (n':ns)
                                   where Just n' = dom ! n

