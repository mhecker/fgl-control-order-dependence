{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert

{- http://perso.ecp.fr/~lechenetjc/control/download.html -}
{- https://doi.org/10.1007/978-3-319-89363-1_12 -}
{- Léchenet JC., Kosmatov N., Le Gall P. (2018) Fast Computation of Arbitrary Control Dependencies.  -}

module Data.Graph.Inductive.Query.FCACD where

import Data.Ord (comparing)
import Data.Maybe(fromJust)
import Control.Monad (liftM, foldM, forM, forM_)

import Control.Monad.ST
import Data.STRef

import Data.Functor.Identity (runIdentity)
import qualified Control.Monad.Logic as Logic
import Data.List(foldl', intersect,foldr1, partition)

import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph.Inductive.Query.Dominators (dom, iDom)
import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)


import qualified Data.Sequence as Seq
import Data.Sequence (Seq(..), ViewL(..), (|>))

import qualified Data.Foldable as Foldable
import IRLSOD
import Program

import Util(the, invert', invert'', foldM1, reachableFrom, treeDfs, toSet, fromSet, reachableFromTree, fromIdom)
import Unicode


import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Basic hiding (postorder)
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.DFS (scc, condensation, topsort, dfs, reachable)

import Debug.Trace
import Control.Exception.Base (assert)



propagate :: Graph gr => gr a b -> Set Node -> Map Node Node -> Node -> Node -> (Set Node, Map Node Node)
propagate g w obs0 u v = 
    let worklist0   = Set.fromList [u]
        candidates0 = Set.empty
        result = loop obs0 worklist0 candidates0
    in -- traceShow (w, obs0, "++++", u, v, "*****", result) $
       result
  where loop obs worklist candidates
            | Set.null worklist = (candidates, obs)
            | otherwise         = let (obs'', worklist'', candidates'') = loop2 pred_todo0 obs worklist' candidates
                                  in loop obs'' worklist'' candidates''
          where (n, worklist') = Set.deleteFindMin worklist
                pred_todo0 = Set.fromList $ pre g n
                
                loop2 pred_todo obs worklist candidates
                    | Set.null pred_todo = (obs, worklist, candidates)
                    | not $ u0 ∈  w      = let (obs', worklist', candidates') = 
                                                 if Map.member u0 obs then
                                                   if not $ (obs ! u0) == v then
                                                     (Map.insert u0 v obs, Set.insert u0 worklist, if (length $ suc g u0) > 1 then Set.insert u0 candidates else candidates)
                                                   else
                                                     (                obs,               worklist,                                                               candidates)
                                                 else
                                                     (Map.insert u0 v obs, Set.insert u0 worklist,                                                               candidates)
                                           in -- traceShow (u0, Map.lookup u0 obs, candidates') $
                                              loop2 pred_todo' obs' worklist' candidates'
                    | otherwise          =    loop2 pred_todo' obs  worklist  candidates
                  where (u0, pred_todo') = Set.deleteFindMin pred_todo


confirm :: Graph gr => gr a b -> Map Node Node -> Node -> Node -> Bool
confirm g obs u u_obs =
    let result0 = False in
    let succ0 = Set.fromList $ suc g u in
    loop succ0 result0
  where loop succ result
            | Set.null succ                                   = result
            | Map.member v obs   ∧   (not $ u_obs == obs ! v) = loop succ' True
            | otherwise                                       = loop succ' result
          where (v, succ') = Set.deleteFindMin succ

main :: Graph gr => gr a b -> Set Node -> (Set Node, Map Node Node)
main g v' = 
      let w0 = v'
          obs0 = Map.fromList [ (n,n) | n <- Set.toList v' ]
          worklist0 = v'
      in loop w0 obs0 worklist0
  where loop w obs worklist
            | Set.null worklist = -- traceShow (w, obs, worklist) $
                                  (w, obs)
            | otherwise         = -- traceShow (w, obs, worklist, "*****", u, candidates, new_nodes, obs') $
                                  loop (w ∪ new_nodes)   (Map.union (Map.fromSet id new_nodes) obs')   (worklist' ∪ new_nodes)
          where (u, worklist') = Set.deleteFindMin worklist
                (candidates, obs') =  propagate g w obs u u
                new_nodes = Set.filter (\v ->  confirm g obs' v u) candidates

wdSlice :: Graph gr => gr a b -> Set Node -> Set Node
wdSlice g = fst . (main g)

wccSlice :: Graph gr => gr a b -> Set Node -> Set Node
wccSlice g v' = w ∩ fromV'
  where (w,_) = main g v'
        fromV' = (Set.fromList $ [ n | m <- Set.toList v', n <- reachable m g ])
