{-# LANGUAGE NamedFieldPuns #-}
module Program.CDom where

import Util

import Algebra.Lattice

import Unicode
import Data.Bool.Unicode

import Program
import Program.MultiThread
import Program.MHP (mhpSetFor)
import IRLSOD

-- import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode

import Data.Tree
import Data.List(nub,intersect,(\\))


import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Query.DFS

import Data.Graph.Inductive.PatriciaTree




-- mhpFor :: DynGraph gr => Program gr -> Map (Node,Node) Bool

-- domTree ::   Map Node Node
-- domTree  = Map.fromList $ 


idomChef  :: DynGraph gr => Program gr ->  Map (Node,Node) Node
idomChef p@(Program {tcfg, entryOf, procedureOf, mainThread} ) = Map.fromList
    [ ((n,n'), lca n n')   | n <- nodes tcfg, n' <- nodes tcfg ]
  where dom :: Map Node Node
        dom = Map.fromList $ iDom tcfg (entryOf $ procedureOf $ mainThread)

        lca :: Node -> Node -> Node
        lca n n' = c
          where (c,_) = last $ takeWhile (\(a,b) -> a==b) $ zip (pathToRoot n)
                                                                (pathToRoot n')
                pathToRoot node
                  | node `Map.member` dom = pathToRoot (dom ! node) ++ [node]
                  | otherwise             = [node]




-- -- chopTreeChef p = \n n' ->  {c | c <- cs}:
-- --             n'
-- --            /
-- --           ..
-- --           /
-- --          c
-- --          /
-- --         ..
-- --         /
-- --        n
-- --
-- chopTreeChef :: :: DynGraph gr => Program gr ->  Map (Node,Node) (Set Node)
-- chopTreeChef p@(Program {tcfg, entryOf, mainThread} ) = Map.fromList
--     [ ((n,n'), lca n n')   | n <- nodes tcfg, n' <- nodes tcfg ]
--   where dom :: Map Node Node
--         dom = Map.fromList $ iDom tcfg (entryOf mainThread)

idomMohrEtAl :: DynGraph gr => Program gr ->  Map (Node,Node) Node
idomMohrEtAl p@(Program {tcfg, entryOf, procedureOf, mainThread} ) = Map.fromList
    [ ((n,n'), leastValidFrom $ lca n n')   | n <- nodes tcfg, n' <- nodes tcfg ]
  where dom :: Map Node Node
        dom = Map.fromList $ iDom tcfg (entryOf $ procedureOf $ mainThread)

        inMulti = isInMultiThread p
        inCycleSet = notInCycleSet tcfg  -- TODO: ggf auf zyklen innerhalb von threads einschränken?!?!?
        inCycle = not . (`Set.member` inCycleSet)

        leastValidFrom :: Node -> Node
        leastValidFrom c
          | (inMulti ! c) ∨ (inCycle c) = leastValidFrom (dom ! c)
          | otherwise                   = c


        lca :: Node -> Node -> Node
        lca n n' = c
          where (c,_) = last $ takeWhile (\(a,b) -> a==b) $ zip (pathToRoot n)
                                                                (pathToRoot n')
                pathToRoot node
                  | node `Map.member` dom = pathToRoot (dom ! node) ++ [node]
                  | otherwise             = [node]


idomMohrEtAlNoCycleTest :: DynGraph gr => Program gr ->  Map (Node,Node) Node
idomMohrEtAlNoCycleTest p@(Program {tcfg, entryOf, procedureOf, mainThread} ) = Map.fromList
    [ ((n,n'), leastValidFrom $ lca n n')   | n <- nodes tcfg, n' <- nodes tcfg ]
  where dom :: Map Node Node
        dom = Map.fromList $ iDom tcfg (entryOf $ procedureOf $ mainThread)

        inMulti = isInMultiThread p

        leastValidFrom :: Node -> Node
        leastValidFrom c
          | (inMulti ! c)               = leastValidFrom (dom ! c)
          | otherwise                   = c


        lca :: Node -> Node -> Node
        lca n n' = c
          where (c,_) = last $ takeWhile (\(a,b) -> a==b) $ zip (pathToRoot n)
                                                                (pathToRoot n')
                pathToRoot node
                  | node `Map.member` dom = pathToRoot (dom ! node) ++ [node]
                  | otherwise             = [node]


idomBischof :: DynGraph gr => Program gr ->  Map (Node,Node) Node
idomBischof p@(Program {tcfg, entryOf, procedureOf, mainThread} ) = Map.fromList
    [ ((n,n'), leastValidFrom n n' $ lca n n')   | n <- nodes tcfg, n' <- nodes tcfg ]
  where dom :: Map Node Node
        dom = Map.fromList $ iDom tcfg (entryOf $ procedureOf $ mainThread)

        mhp = mhpSetFor p
        mhps = Map.fromList [ (n, Set.fromList [ m | (n',m) <- Set.toList mhp, n' == n]) | n <- nodes tcfg ]

        leastValidFrom :: Node -> Node -> Node -> Node
        leastValidFrom n n' c
          | (n ∈ mhps ! c) ∨ (n' ∈ mhps ! c) = leastValidFrom n n' (dom ! c)
          | otherwise                   = c


        lca :: Node -> Node -> Node
        lca n n' = c
          where (c,_) = last $ takeWhile (\(a,b) -> a==b) $ zip (pathToRoot n)
                                                                (pathToRoot n')
                pathToRoot node
                  | node `Map.member` dom = pathToRoot (dom ! node) ++ [node]
                  | otherwise             = [node]


domPathBetween dom dominated dominator
    | dominated  == dominator = [dominated]
    | otherwise               = domPathBetween dom dominated' dominator ++ [dominated]
  where Just dominated' = Map.lookup dominated dom



-- idomToTree idom = the (\_ -> True) $ dff' tree'
--    where nodes = nub [ (n,()) | ((a,b),c) <- Map.assocs idom,  n <- [ a, b, c] ]
--          tree :: Gr () ()
--          tree =  mkGraph nodes
--                          (nub [ (c,n,()) | ((a,b),c) <- Map.assocs idom, n  <- [ a,b]])
--          tree' = trc tree

idomToTree idom = trrAcyclic tree
   where nodes = nub [ (n,n) | ((a,b),c) <- Map.assocs idom,  n <- [ a, b, c] ]
         tree :: Gr Int ()
         tree =  mkGraph nodes
                         (nub [ (c,n,()) | ((a,b),c) <- Map.assocs idom, n  <- [ a,b]])


chop graph =
  let trnsclos = trc graph in \s t ->
      (Set.fromList $ suc trnsclos s)
    ∩ (Set.fromList $ pre trnsclos t)

-- inclChop graph s t
--     | tFound    = bwd
--     | otherwise = []
--   where forward []     found tFound = (tFound, found)
--         forward (n:ns) found tFound = forward  ((successors \\ found) ++ ns ) (n:found) (tFound || n == t || t ∊ successors )
--            where successors = suc graph n

--         backward []     found = found
--         backward (n:ns) found = backward       (((predecessors \\ found) `intersect` fwd ) ++ ns) (n:found)
--            where predecessors = pre graph n

--         (tFound, fwd) = forward  [s] [] False
--         bwd           = backward [t] []


-- exclChop graph s t
--     | tFound    = bwd
--     | otherwise = []
--   where forward []     found tFound = (tFound, found)
--         forward (n:ns) found tFound = forward  (((successors \\ found) \\ [t]) ++ ns ) (n:found) (tFound || n == t || t ∊ successors )
--            where successors = suc graph n 

--         backward []     found = found
--         backward (n:ns) found = backward       ((((predecessors \\ found) \\ [s]) `intersect` fwd ) ++ ns) (n:found)
--            where predecessors = pre graph n

--         (tFound, fwd) = forward  [s] [] False
--         bwd           = backward [t] []


exclChop graph s t
    | tFound    = bwd
    | otherwise = Set.empty
  where forward ns found tFound 
            | Set.null ns = (tFound, found)
            | otherwise   = forward ((Set.delete t new) ∪ ns') (new ∪ found) (tFound || n == t || t ∈ successors )
          where (n,ns') = Set.deleteFindMin ns
                new = (successors ∖ found)
                successors = Set.fromList $ suc graph n

        backward ns found 
            | Set.null ns = found
            | otherwise   = backward ((Set.delete s new) ∪ ns') (new ∪ found)
          where (n,ns') = Set.deleteFindMin ns
                new = (predecessors ∖ found) ∩ fwd
                predecessors = Set.fromList $ pre graph n

        (tFound, fwd) = forward  (Set.fromList [s]) (Set.fromList [s]) False
        bwd           = backward (Set.fromList [t]) (Set.fromList [t])


inclChop graph s t
    | tFound    = bwd
    | otherwise = Set.empty
  where
        forward ns found tFound 
            | Set.null ns = (tFound, found)
            | otherwise   = forward (new ∪ ns') (new ∪ found) (tFound || n == t || t ∈ successors )
          where (n,ns') = Set.deleteFindMin ns
                new = (successors ∖ found)
                successors = Set.fromList $ suc graph n

        backward ns found 
            | Set.null ns = found
            | otherwise   = backward (new ∪ ns') (new ∪ found)
          where (n,ns') = Set.deleteFindMin ns
                new = (predecessors ∖ found) ∩ fwd
                predecessors = Set.fromList $ pre graph n

        (tFound, fwd) = forward  (Set.fromList [s]) (Set.fromList [s]) False
        bwd           = backward (Set.fromList [t]) (Set.fromList [t])




simulChop gr =
    (㎲⊒) (  Map.fromList [ ((n,m),if n==m then Set.fromList [n] else Set.empty) | n <- nodes gr, m <- nodes gr])
          (\ch ->
             ch
           ⊔ Map.fromList [ ((n,m),  (∐) [ if (Set.null $ ch ! (n', m)) then Set.empty else ch ! (n',m) ⊔  ch ! (n,n)   | n' <- suc gr n]) | n <- nodes gr, m <- nodes gr ]
          )



-- simulChop graph = forward (nodes
--   where forward 
--   case (nodes grap) of [] -> Map.empty
--        (n:ns)             -> forward (

