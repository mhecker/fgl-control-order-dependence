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
import Util(toSet, fromSet)
import Unicode


import Data.Graph.Inductive
-- import Data.Graph.Inductive.Query.TransClos
-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Query.Dependence
-- import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs)

-- import Debug.Trace
import Control.Exception.Base (assert)





lca imdom n m = let result = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m]) in assert (result == lcaSlow imdom n m) result
          where 
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  caseN
                  where caseN = case imdom ! n of
                                  Nothing ->                 lcaDownLin ms ns m
                                  Just n' -> if n' ∈ ns then lcaDownLin ms ns m  else lcaDown' (m, ms) (n', Set.insert n' ns)
                lcaDownLin ms ns m = assert (not $ m ∈ ns) $ lcaDown'' m ms
                  where lcaDown'' m ms = case imdom ! m of
                                        Nothing -> Nothing
                                        Just m' -> if m' ∈ ns then Just m' else
                                                   if m' ∈ ms then Nothing else lcaDown'' m' (Set.insert m' ms)


lcaUniqueExitNode imdom nx n m = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m])
          where
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  caseN
                  where caseN = case imdom ! n of
                                  Nothing -> assert (n == nx) $
                                             lcaDownLin ns m
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



lcaMyWodFastPDomForIterationStrategy dom n m = lca' (n, Set.fromList [n]) (m, Set.fromList [m])
           where lca' :: (Node,Set Node) -> (Node, Set Node) -> Node
                 lca' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case dom ! n of
                                     Nothing -> case dom ! m of
                                                Nothing -> error "is no tree"
                                                Just m' -> lca' ( m', Set.insert m' ms) (n, ns)
                                     Just n' -> lca' (m, ms) (n', Set.insert n' ns)



lcaTimdomOfTwoFinger imdom (n, sn, forbiddenNs) (m, sm, forbiddenMs) = lca' imdom (n, sn, Map.fromList [(n,sn)], forbiddenNs) (m, sm, Map.fromList [(m,sm)], forbiddenMs)
          where 
                lca' :: Map Node (Maybe (Node, Integer)) -> (Node, Integer, Map Node Integer, Set Node) -> (Node, Integer, Map Node Integer, Set Node ) -> Maybe (Node, Integer, Set Node)
                lca' c (n, sn, ns, forbiddenNs) (m, sm, ms, forbiddenMs)
                    | m ∈ Map.keysSet ns ∧ ((ns ! m) == sm) = -- traceShow ((n,sn,ns,forbiddenNs), (m,sm,ms,forbiddenMs)) $
                                                           assert (ms ! m == sm) $
                                                           let left  = Set.fromList [ v | (v,s) <- Map.assocs ns, s <= sm ]
                                                               right = Map.keysSet ms
                                                           in
                                                           assert (left ∩ right == Set.fromList [m]) $
                                                           Just (m, sm, left ∪ right)
                    | n ∈ Map.keysSet ms ∧ ((ms ! n) == sn) = -- traceShow ((n,sn,ns,forbiddenNs), (m,sm,ms,forbiddenMs)) $
                                                           assert (ns ! n == sn) $
                                                           let left  = Set.fromList [ v | (v,s) <- Map.assocs ms, s <= sn ]
                                                               right = Map.keysSet ns
                                                           in
                                                           assert (left ∩ right == Set.fromList [n]) $
                                                           Just (n, sn, left ∪ right)
                    | otherwise = -- traceShow ((n,sn,ns,forbiddenNs), (m,sm,ms,forbiddenMs)) $
                                  case Set.toList $ (Set.map fst $ toSet $ (c ! n)) ∖ (Map.keysSet ns ∪ forbiddenNs) of
                                     []   -> case Set.toList $ (Set.map fst $ toSet (c ! m)) ∖ (Map.keysSet ms ∪ forbiddenMs) of
                                                []   -> Nothing
                                                [_] -> let Just (m',sm') = c ! m
                                                       in lca' c ( m', sm + sm', Map.insert m' (sm+sm') ms, forbiddenMs) (n, sn, ns, forbiddenNs)
                                     [_] -> let Just (n',sn') = c ! n
                                            in lca' c (m, sm, ms, forbiddenMs) (n', sn + sn', Map.insert n' (sn+sn') ns, forbiddenNs)

lcaRKnownM :: Map Node (Maybe Node) -> Node -> [Node] -> (Node, Set Node)
lcaRKnownM dom c successors = case dom ! c of
                     Nothing -> assert (successors == []) $
                                (c, Set.fromList [c])
                     Just z  -> assert (successors /= []) $ 
                                (z, foldr relevant (Set.fromList successors) successors)
                       where relevant :: Node -> Set Node -> Set Node
                             relevant n ns
                               | n == z = ns
                               | otherwise = relevant n' (Set.insert n' ns)
                                   where Just n' = dom ! n

