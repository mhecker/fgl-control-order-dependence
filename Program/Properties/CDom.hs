{-# LANGUAGE NamedFieldPuns #-}
module Program.Properties.CDom where

-- import Algebra.Lattice

import Unicode
import Data.Bool.Unicode

import Program
-- import Program.MultiThread
-- import Program.CDom
import Execution
import ExecutionTree


import IRLSOD

-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Graph


import Data.List (takeWhile, dropWhile)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Util
-- import Data.Set.Unicode

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Query.Dominators



cdomIsDomViolations :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsDomViolations p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          e <- θ,
          let hb = someHappensBeforeAll e,
          (not (occurencesOf e n == [] ∨  c `hb` n))
          ∨
          (not (occurencesOf e m == [] ∨  c `hb` m))
    ]
  where cdom = cd p



cdomIsCdomViolations :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsCdomViolations p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          e <- θ,
          not $
          (∀) (occurencesOf e n) (\(i,n) ->
          (∀) (occurencesOf e m) (\(j,m) ->
          (∃) (occurencesOf e c) (\(k,c) -> k <= i
                                         && k <= j)))
    ]
  where cdom = cd p

cdomIsCdomViolations' :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsCdomViolations' p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          e <- θ,
          not $
          (∀) (occurencesOf e n) (\(i,n) ->
          (∀) (occurencesOf e m) (\(j,m) ->
              (¬) ((∃) (occurencesOf e c) (\(k,c) -> i < k && k < j))
          ))
    ]
  where cdom = cd p


cdomIsCdomViolations'For :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> Node -> Node -> [(Node,Node,Trace)]
cdomIsCdomViolations'For p@(Program {tcfg}) θ cd n m =
    [ (n,m, toTrace e) |
          let  c = cdom ! (n,m),
          e <- θ,
          not $
          (∀) (occurencesOf e n) (\(i,n) ->
          (∀) (occurencesOf e m) (\(j,m) ->
              (¬) ((∃) (occurencesOf e c) (\(k,c) -> i < k && k < j))
          ))
    ]
  where cdom = cd p


cdomIsBeforeViolations :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsBeforeViolations p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          e <- θ,
          let  c  = cdom ! (n,m),
          let  hb = happensBefore e,
          (not (occurencesOf e n == [] ∨  c `hb` n))
          ∨
          (not (occurencesOf e m == [] ∨  c `hb` m))
    ]
  where cdom = cd p


occurencesOf e n = [ (i,n') | (i,(_,(n',_),_)) <- e', n' == n]
  where e' = zip [1..] e

someHappensBeforeAll :: ExecutionTrace -> Node -> Node -> Bool
someHappensBeforeAll e n m =
          ((∃) (take 1 $ occurencesOf e n) (\(i,n) ->
           (∀) (         occurencesOf e m) (\(j,m) -> i <= j)))

happensBefore :: ExecutionTrace -> Node -> Node -> Bool
happensBefore e n m =
          ((∃) (take 1 $ occurencesOf e n) (\(i,n) ->
           (∃) (         occurencesOf e m) (\(j,m) -> i <= j)))


cdomIsTreeDomViolations :: DynGraph gr => Program gr -> [ExecutionTree] -> (Program gr -> Map (Node,Node) Node) -> [(Node,Node,ExecutionTree)]
cdomIsTreeDomViolations p@(Program {tcfg}) θ cd =
    [ (n,m, t) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          t <- θ,
          let tpaths = Set.fromList $ paths t,
          (not $ (∀) tpaths (c `allOrderedBeforeAll` n)) ∨
          (not $ (∀) tpaths (c `allOrderedBeforeAll` m))
    ]
  where cdom = cd p
        allOrderedBeforeAll c n path =
              (c == n ∧ length [ n' | n' <- ns, n == n'] == 1)
            ∨ (not $ (c ∈ dropWhile (/=n) ns))
          where ns = [ n' | (n',e) <- path ] 
