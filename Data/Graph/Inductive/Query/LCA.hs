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





lcaRofldomOfTwoFinger7 :: Map Node (Maybe Node) -> Node -> Node -> Maybe Node
lcaRofldomOfTwoFinger7 rofldom n m = let result = lca' (n, Set.fromList [n]) (m, Set.fromList [m]) in assert (result == lca rofldom n m) $ result
         where
                lca' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lca' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((toSet (rofldom ! n)) ∖ ns ) of
                                     []   -> case Set.toList $ ((toSet (rofldom ! m)) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> lca' ( m', Set.insert m' ms) (n, ns)
                                     [n'] -> lca' (m, ms) (n', Set.insert n' ns)



lcaImdomOfTwoFinger6 imdom n m = let result = lca' imdom (n, Set.fromList [n]) (m, Set.fromList [m]) in assert (result == lca (fmap fromSet imdom) n m) $ result
          where
                lca' c (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((c ! n) ∖ ns ) of
                                     []   -> case Set.toList $ ((c ! m) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> lca' c ( m', Set.insert m' ms) (n, ns)
                                                _    -> error "more than one successor in imdom" 
                                     [n'] -> lca' c (m, ms) (n', Set.insert n' ns)
                                     _    -> error "more than one successor in imdom" 

lcaImdomOfTwoFinger7 imdom n m = let result = lca' (n, Set.fromList [n]) (m, Set.fromList [m]) in assert (result == lca imdom n m) $ result
          where 
                lca' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lca' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((toSet (imdom ! n)) ∖ ns ) of
                                     []   -> case Set.toList $ ((toSet (imdom ! m)) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> lca' ( m', Set.insert m' ms) (n, ns)
                                     [n'] -> lca' (m, ms) (n', Set.insert n' ns)



lcaIsinkdomOfTwoFinger8Down imdom n m = let result = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m]) in assert (result == lca imdom n m) $ result
          where
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ ((toSet (imdom ! n)) ∖ ns ) of
                                     []   -> case Set.toList $ ((toSet (imdom ! m)) ∖ ms ) of
                                                []   -> Nothing
                                                [m'] -> lcaDown' (m', Set.insert m' ms) (n, ns)
                                     [n'] -> lcaDown' (m, ms) (n', Set.insert n' ns)




lcaIsinkdomOfTwoFinger8DownFixedTraversalForOrder imdom n m = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m])
          where 
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  caseM
                  where caseM = case imdom ! m of
                                  Nothing ->                 caseN
                                  Just m' -> if m' ∈ ms then caseN   else lcaDown' (n, ns) (m', Set.insert m' ms)
                        caseN = case imdom ! n of
                                  Nothing ->                 Nothing
                                  Just n' -> if n' ∈ ns then Nothing else lcaDown' (n', Set.insert n' ns) (m, ms)


lcaIsinkdomOfTwoFinger8DownUniqueExitNode imdom nx n m = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m])
          where
                lcaDown' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lcaDown' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  caseM
                  where caseM = case imdom ! m of
                                  Nothing -> assert (m == nx) $
                                             lcaDownLin ms n
                                  Just m' -> lcaDown' (m', Set.insert m' ms) (n, ns)
                lcaDownLin ms n = assert (not $ n ∈ ms) $ lcaDown'' n
                  where lcaDown'' n = case imdom ! n of
                                        Nothing -> Nothing
                                        Just n' -> if n' ∈ ms then Just n' else lcaDown'' n'



lca :: Map Node (Maybe Node) -> Node -> Node -> Maybe Node
lca idom n m = lca' (n, n, Set.fromList [n]) (m, m, Set.fromList [m])
  where lca' :: (Node, Node,Set Node) -> (Node, Node, Set Node) -> Maybe Node
        lca' (n0,n,ns) (m0,m,ms)
          | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                     Just m
          | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                     Just n
          | otherwise = -- traceShow ((n,ns), (m,ms)) $
                       case Set.toList $ ((toSet (idom ! n)) ∖ ns ) of
                         []   -> case Set.toList $ ((toSet (idom ! m)) ∖ ms ) of
                                   []   -> Nothing
                                   [m'] -> lca' (m0, m', Set.insert m' ms) (n0, n, ns)
                         [n'] -> lca' (m0, m, ms) (n0, n', Set.insert n' ns)



lcaMyDom dom n m = let result = lca' (n, Set.fromList [n]) (m, Set.fromList [m]) in assert (result == lca (fmap fromSet dom) n m) $ result
          where lca' :: (Node,Set Node) -> (Node, Set Node) -> Maybe Node
                lca' (n,ns) (m,ms)
                    | m ∈ ns = -- traceShow ((n,ns), (m,ms)) $
                               Just m
                    | n ∈ ms = -- traceShow ((n,ns), (m,ms)) $
                               Just n
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  case Set.toList $ (dom ! n) ∖ ns of
                                     []   -> case Set.toList $ (dom ! m) ∖ ms of
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



lcaRKnown :: Map Node (Set Node) -> Node -> [Node] -> (Node, Set Node)
lcaRKnown dom c successors = case Set.toList $ dom ! c of
                     []  -> assert (successors == []) $
                                (c, Set.fromList [c])
                     [z] -> assert (successors /= []) $ 
                                (z, foldr relevant (Set.fromList successors) successors)
                       where relevant :: Node -> Set Node -> Set Node
                             relevant n ns
                               | n == z = ns
                               | otherwise = relevant n' (Set.insert n' ns)
                                   where [n'] = Set.toList $ dom ! n
                     _   -> error "no tree"

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
