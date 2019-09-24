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




lcaTimdomOfTwoFingerOld imdom (n, sn, ns) (m, sm, ms) = lca' imdom (n, sn, ns) (m, sm, ms)
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


lcaTimdomOfTwoFinger idom (n, sn, ns) (m, sm, ms) = assert (result == lcaTimdomOfTwoFingerOld idom (n, sn, ns) (m, sm, ms)) result
          where result = lca' (n, sn, ns) (m, sm, ms)
                lca' :: (Node, Integer, Map Node (Set Integer)) -> (Node, Integer, Map Node (Set Integer)) -> Maybe (Node, Integer, Map Node (Set Integer))
                lca' (n, sn, ns) (m, sm, ms)
                    | sn > sm = lca' (m, sm, ms) (n, sn, ns)
                    | n ∈ Map.keysSet ms ∧ (      sn ∈ (ms ! n)) = -- traceShow ("A", (n,sn,ns), (m,sm,ms)) $
                                                           Just (n, sn, Map.fromList [(n, Set.fromList [sn])])
                    | n ∈ Map.keysSet ms ∧ (not $ sn ∈ (ms ! n)) = -- traceShow ("B", (n,sn,ns), (m,sm,ms)) $
                                  if   (∃) (ns ! n) (\sn' -> (∃) (ms ! n) (\sm' -> sm' < sn'))
                                     ∧ (∃) (ns ! n) (\sn' -> (∃) (ms ! n) (\sm' -> sm' > sn')) then Nothing else
                                  case idom ! n of
                                     Nothing       -> Nothing
                                     Just (n',sn') -> lca' (m, sm, ms) (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns)
                    | otherwise = -- traceShow ("C", (n,sn,ns), (m,sm,ms)) $
                                  case idom ! n of
                                     Nothing       -> Nothing
                                     Just (n',sn') ->
                                               if n' ∈ Map.keysSet ns ∧ (Set.size (ms ! m) > 1) ∧ (not $ n' ∈ Map.keysSet ms) then Nothing else
                                               lca' (m, sm, ms) (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns)


lcaTimdomOfTwoFingerFast idom (n, sn, ns) (m, sm, ms) =
              require ((∀) (Map.elems $ Map.filter (/= Nothing) $ idom) (\(Just (_,k)) -> k > 0))
            $ assert (result == lcaTimdomOfTwoFinger idom (n, sn, ns) (m, sm, ms))
            $ assert (ns == Map.fromList [(n, Set.fromList [sn])])
            $ assert (ms == Map.fromList [(m, Set.fromList [sm])])
            $ result
          where result = lca' (n, sn, ns) (m, sm, ms)
                lca' :: (Node, Integer, Map Node (Set Integer)) -> (Node, Integer, Map Node (Set Integer)) -> Maybe (Node, Integer, Map Node (Set Integer))
                lca' pin@(n, sn, ns) pim@(m, sm, ms)
                    | sn > sm = lca' (m, sm, ms) (n, sn, ns)
                    | n ∈ Map.keysSet ms ∧ (      sn ∈ (ms ! n)) = -- traceShow ("A", (n,sn,ns), (m,sm,ms)) $
                                                           Just (n, sn, Map.fromList [(n, Set.fromList [sn])])
                    | n ∈ Map.keysSet ms ∧ (not $ sn ∈ (ms ! n)) = -- traceShow ("B", (n,sn,ns), (m,sm,ms)) $
                                  if   Set.findMax (ns ! n) > Set.findMin (ms ! n)
                                     ∧ Set.findMin (ns ! n) < Set.findMax (ms ! n) then Nothing else
                                  case idom ! n of
                                     Nothing       -> Nothing
                                     Just (n',sn') -> lca' (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns) (m, sm, ms)
                    | otherwise = -- traceShow ("C", (n,sn,ns), (m,sm,ms)) $
                                  case idom ! n of
                                     Nothing       -> Nothing
                                     Just (n',sn') ->
                                               if n' ∈ Map.keysSet ns ∧ (Set.size (ms ! m) > 1) ∧ (not $ n' ∈ Map.keysSet ms) then Nothing else
                                                      lca' (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns) (m, sm, ms)



lcaTimdomOfTwoFingerFastCost' idom (n, sn, ns, ns0, cost) (m, sm, ms, ms0, _) = 
              id
            $ traceShow cost
            $ assert (ns == Map.fromList [(n, Set.fromList [sn])])
            $ assert (ms == Map.fromList [(m, Set.fromList [sm])])
            $ result
          where traceShow _ x = x
                result = lcaDown' (n, sn, ns, ns0) (m, sm, ms, ms0)
                lcaDown' :: (Node, Integer, Map Node (Set Integer), Set Node) -> (Node, Integer, Map Node (Set Integer), Set Node) -> Maybe (Node, Integer, Map Node (Set Integer), Set Node, Map Node Integer)
                lcaDown' pin@(n, sn, ns, ns0) pim@(m, sm, ms, ms0)
                    | m ∈ Map.keysSet ns ∧ (      sm ∈ (ns ! m)) = traceShow ("A", (n,sn,ns), (m,sm,ms)) $
                                                           Just (m, sm, Map.fromList [(m, Set.fromList [sm])], ns0 ∪ ms0, cost)
                    | m ∈ Map.keysSet ns ∧ (not $ sm ∈ (ns ! m)) = traceShow ("B", (n,sn,ns), (m,sm,ms)) $
                                  assert (sm == Set.findMin (ms ! m)) $
                                  let sm' = Set.findMin (ns ! m) in
                                  if (sm < sm') then
                                    Just (m, sm', Map.fromList [(m, Set.fromList [sm'])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm' - sm ) ms0) cost)
                                  else
                                    Just (m, sm , Map.fromList [(m, Set.fromList [sm ])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm  - sm') ns0) cost)
                    | otherwise = traceShow ((n,ns), (m,ms)) $
                                  assert (not $ n ∈ Map.keysSet ms) $ 
                                  caseN
                  where caseN = case idom ! n of
                                 Nothing ->                                    lcaDownLin ms ns ms0 ns0 sm m
                                 Just (n', sn') -> if n' ∈ Map.keysSet ns then lcaDownLin ms ns ms0 ns0 sm m else lcaDown' (m, sm, ms, ms0) (n', sn + sn',Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns, ns0)
                lcaDownLin ms ns ms0 ns0 sm m = assert (not $ m ∈ Map.keysSet ns) $ lcaDown'' m sm ms
                  where lcaDown'' m s ms = case idom ! m of
                                        Nothing -> Nothing
                                        Just (m', s') ->
                                          let m = m'
                                              sm = s + s'
                                          in if m ∈ Map.keysSet ns  ∧ (      sm ∈ (ns ! m)) then Just (m, sm, Map.fromList [(m, Set.fromList [sm])], ns0 ∪ ms0, cost) else
                                             if m ∈ Map.keysSet ns  ∧ (not $ sm ∈ (ns ! m)) then 
                                                 let sm' = Set.findMin (ns ! m) in
                                                 if (sm < sm') then
                                                   Just (m, sm', Map.fromList [(m, Set.fromList [sm'])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm' - sm ) ms0) cost)
                                                 else
                                                   Just (m, sm , Map.fromList [(m, Set.fromList [sm ])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm  - sm') ns0) cost) else
                                             if m ∈ Map.keysSet ms then Nothing else lcaDown'' m sm (Map.insertWith (∪) m (Set.fromList [sm]) ms)

lcaTimdomOfTwoFingerFastCost idom (n, sn, ns, ns0, cost) (m, sm, ms, ms0, _) = 
              id
            -- $ traceShow cost
            $ assert (ns == Map.fromList [(n, Set.fromList [sn])])
            $ assert (ms == Map.fromList [(m, Set.fromList [sm])])
            $ assert (result'  == lcaTimdomOfTwoFingerFastCost' idom (n, sn, ns, ns0, cost) (m, sm, ms, ms0, undefined))
            $ (if result'' == result''' then id else traceShow ((n, sn), (m, sm), result, result'', result''', idom))
            $ assert (result'' == result''') 
            $ result'
          where -- traceShow _ x = x
                result = lcaDown' (n, sn, Map.fromList [(n, sn)], ns0) (m, sm, Map.fromList [(m, sm)], ms0)
                result' = case result of
                    Nothing -> Nothing
                    Just (a, sa, as, nodes, cost) -> Just (a, sa, fmap Set.singleton as, nodes, cost)
                (result'', result''') = case result of
                    Nothing -> (Nothing, Nothing)
                    Just (a, sa, as, nodes, cost') ->
                      let sn' = sn + cost' ! n0 - cost ! n0
                            where n0 = Set.findMin ns0
                          sm' = sm + cost' ! m0 - cost ! m0
                            where m0 = Set.findMin ms0
                      in (Just (a, sa, fmap Set.singleton as), lcaTimdomOfTwoFingerFast idom (n, sn', Map.fromList [(n, Set.fromList [sn'])]) (m, sm', Map.fromList [(m, Set.fromList [sm'])]))
                lcaDown' :: (Node, Integer, Map Node Integer, Set Node) -> (Node, Integer, Map Node Integer, Set Node) -> Maybe (Node, Integer, Map Node Integer, Set Node, Map Node Integer)
                lcaDown' pin@(n, sn, ns, ns0) pim@(m, sm, ms, ms0)
                    | m ∈ Map.keysSet ns ∧ (      sm == ns ! m) = --traceShow ("A", (n,sn,ns), (m,sm,ms)) $
                                                           Just (m, sm, Map.fromList [(m, sm)], ns0 ∪ ms0, cost)
                    | m ∈ Map.keysSet ns ∧ (not $ sm == ns ! m) = -- traceShow ("B", (n,sn,ns), (m,sm,ms)) $
                                  assert (sm == ms ! m) $
                                  let sm' = ns ! m in
                                  if (sm < sm') then
                                    Just (m, sm', Map.fromList [(m, sm')], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm' - sm ) ms0) cost)
                                  else
                                    Just (m, sm , Map.fromList [(m, sm )], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm  - sm') ns0) cost)
                    | otherwise = -- traceShow ((n,ns), (m,ms)) $
                                  assert (not $ n ∈ Map.keysSet ms) $ 
                                  caseN
                  where caseN = case idom ! n of
                                 Nothing ->                                    lcaDownLin ms ns ms0 ns0 sm m
                                 Just (n', sn') -> if n' ∈ Map.keysSet ns then lcaDownLin ms ns ms0 ns0 sm m else lcaDown' (m, sm, ms, ms0) (n', sn + sn',Map.insert n' (sn+sn') ns, ns0)
                lcaDownLin ms ns ms0 ns0 sm m = assert (not $ m ∈ Map.keysSet ns) $ lcaDown'' m sm ms
                  where lcaDown'' m s ms = case idom ! m of
                                        Nothing -> Nothing
                                        Just (m', s') ->
                                          let m = m'
                                              sm = s + s'
                                          in if m ∈ Map.keysSet ns  ∧ (      sm == ns ! m) then Just (m, sm, Map.fromList [(m, sm)], ns0 ∪ ms0, cost) else
                                             if m ∈ Map.keysSet ns  ∧ (not $ sm == ns ! m) then 
                                                 let sm' = ns ! m in
                                                 if (sm < sm') then
                                                   Just (m, sm', Map.fromList [(m, sm')], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm' - sm ) ms0) cost)
                                                 else
                                                   Just (m, sm , Map.fromList [(m, sm )], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm  - sm') ns0) cost) else
                                             if m ∈ Map.keysSet ms then Nothing else lcaDown'' m sm (Map.insert m sm ms)

-- lcaTimdomOfTwoFingerFastCost idom (n, sn, ns, ns0, cost) (m, sm, ms, ms0, _) =
--               id
--             $ traceShow cost
--             $ assert (ns == Map.fromList [(n, Set.fromList [sn])])
--             $ assert (ms == Map.fromList [(m, Set.fromList [sm])])
--             $ result
--           where result = lca' (n, sn, ns, ns0) (m, sm, ms, ms0)
--                 lca' :: (Node, Integer, Map Node (Set Integer), Set Node) -> (Node, Integer, Map Node (Set Integer), Set Node) -> Maybe (Node, Integer, Map Node (Set Integer), Set Node, Map Node Integer)
--                 lca' pin@(n, sn, ns, ns0) pim@(m, sm, ms, ms0)
--                     | n ∈ Map.keysSet ms ∧ (      sn ∈ (ms ! n)) = traceShow ("A ", (n,sn,ns), (m,sm,ms)) $
--                                                            Just (n, sn, Map.fromList [(n, Set.fromList [sn])], ns0 ∪ ms0, cost)
--                     | n ∈ Map.keysSet ms ∧ (not $ sn ∈ (ms ! n)) = traceShow ("B ", (n,sn,ns), (m,sm,ms)) $
--                                   assert (sn == Set.findMin (ns ! n)) $
--                                   let sn' = Set.findMin (ms ! n) in
--                                   if (sn < sn') then
--                                     Just (n, sn', Map.fromList [(n, Set.fromList [sn'])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sn' - sn ) ns0) cost)
--                                   else
--                                     Just (n, sn , Map.fromList [(n, Set.fromList [sn ])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sn  - sn') ms0) cost)
--                     | m ∈ Map.keysSet ns ∧ (      sm ∈ (ns ! m)) = traceShow ("AA", (n,sn,ns), (m,sm,ms)) $
--                                                            Just (m, sm, Map.fromList [(m, Set.fromList [sm])], ns0 ∪ ms0, cost)
--                     | n ∈ Map.keysSet ms ∧ (not $ sm ∈ (ns ! m)) = traceShow ("BB", (n,sn,ns), (m,sm,ms)) $
--                                   assert (sm == Set.findMin (ms ! m)) $
--                                   let sm' = Set.findMin (ns ! m) in
--                                   if (sm < sm') then
--                                     Just (m, sm', Map.fromList [(m, Set.fromList [sm'])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm' - sm ) ms0) cost)
--                                   else
--                                     Just (m, sm , Map.fromList [(m, Set.fromList [sm ])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sm  - sm') ns0) cost)
--                     | otherwise = traceShow ("C", (n,sn,ns), (m,sm,ms)) $
--                                   case idom ! n of
--                                      Nothing       -> case idom ! m of
--                                        Nothing -> Nothing
--                                        Just (m', sm') ->
--                                                if m' ∈ Map.keysSet ms ∧ (Set.size (ns ! n) > 1) ∧ (not $ m' ∈ Map.keysSet ns) then Nothing else
--                                                       lca' (n, sn, ns, ns0) (m', sm + sm', Map.insertWith (∪) m' (Set.fromList [sm+sm']) ms, ms0)
--                                      Just (n',sn') ->
--                                                if n' ∈ Map.keysSet ns ∧ (Set.size (ms ! m) > 1) ∧ (not $ n' ∈ Map.keysSet ms) then Nothing else
--                                                       lca' (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns, ns0) (m, sm, ms, ms0)

-- lcaTimdomOfTwoFingerFastCost idom (n, sn, ns, ns0, cost) (m, sm, ms, ms0, _) =
--               id
--             $ traceShow cost
--             $ assert (ns == Map.fromList [(n, Set.fromList [sn])])
--             $ assert (ms == Map.fromList [(m, Set.fromList [sm])])
--             $ result
--           where result = lca' (n, sn, ns, ns0) (m, sm, ms, ms0)
--                 lca' :: (Node, Integer, Map Node (Set Integer), Set Node) -> (Node, Integer, Map Node (Set Integer), Set Node) -> Maybe (Node, Integer, Map Node (Set Integer), Set Node, Map Node Integer)
--                 lca' pin@(n, sn, ns, ns0) pim@(m, sm, ms, ms0)
--                     | sn > sm = lca' (m, sm, ms, ms0) (n, sn, ns, ns0)
--                     | n ∈ Map.keysSet ms ∧ (      sn ∈ (ms ! n)) = traceShow ("A", (n,sn,ns), (m,sm,ms)) $
--                                                            Just (n, sn, Map.fromList [(n, Set.fromList [sn])], ns0 ∪ ms0, cost)
--                     | n ∈ Map.keysSet ms ∧ (not $ sn ∈ (ms ! n)) = traceShow ("B", (n,sn,ns), (m,sm,ms)) $
--                                   -- if   Set.findMax (ns ! n) > Set.findMin (ms ! n)
--                                   --    ∧ Set.findMin (ns ! n) < Set.findMax (ms ! n) then Nothing else
--                                   -- case idom ! n of
--                                   --    Nothing       -> Nothing
--                                   --    Just (n',sn') -> lca' (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns) (m, sm, ms)
--                                   assert (sn == Set.findMin (ns ! n)) $
--                                   let sn' = Set.findMin (ms ! n) in
--                                   if (sn < sn') then
--                                     Just (n, sn', Map.fromList [(n, Set.fromList [sn'])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sn' - sn ) ns0) cost)
--                                   else
--                                     Just (n, sn , Map.fromList [(n, Set.fromList [sn ])], ns0 ∪ ms0, Map.unionWith (+) (Map.fromSet (const $ sn  - sn') ms0) cost)
--                     | otherwise = traceShow ("C", (n,sn,ns), (m,sm,ms)) $
--                                   case idom ! n of
--                                      Nothing       -> case idom ! m of
--                                        Nothing -> Nothing
--                                        Just (m', sm') ->
--                                                if m' ∈ Map.keysSet ms ∧ (Set.size (ns ! n) > 1) ∧ (not $ m' ∈ Map.keysSet ns) then Nothing else
--                                                       lca' (n, sn, ns, ns0) (m', sm + sm', Map.insertWith (∪) m' (Set.fromList [sm+sm']) ms, ms0)
--                                      Just (n',sn') ->
--                                                if n' ∈ Map.keysSet ns ∧ (Set.size (ms ! m) > 1) ∧ (not $ n' ∈ Map.keysSet ms) then Nothing else
--                                                       lca' (n', sn + sn', Map.insertWith (∪) n' (Set.fromList [sn+sn']) ns, ns0) (m, sm, ms, ms0)

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

