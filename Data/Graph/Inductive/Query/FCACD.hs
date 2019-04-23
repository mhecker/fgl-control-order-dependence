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


import Data.Graph.Inductive.Query.NTICD (nticdSlice)

import Debug.Trace
import Control.Exception.Base (assert)



propagate :: Map Node (Set Node) -> Map Node [Node] -> Set Node -> Map Node Node -> Node -> Node -> (Set Node, Map Node Node)
propagate pres sucs w obs0 u v = 
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
                pred_todo0 = pres ! n
                
                loop2 pred_todo obs worklist candidates
                    | Set.null pred_todo = (obs, worklist, candidates)
                    | not $ u0 ∈  w      = let (obs', worklist', candidates') = 
                                                 if Map.member u0 obs then
                                                   if not $ (obs ! u0) == v then
                                                     (Map.insert u0 v obs, Set.insert u0 worklist, if isCond $ sucs ! u0 then Set.insert u0 candidates      else candidates)
                                                   else
                                                     (                obs,               worklist,                                                               candidates)
                                                 else
                                                     (Map.insert u0 v obs, Set.insert u0 worklist,                                                               candidates)
                                           in -- traceShow (u0, Map.lookup u0 obs, candidates') $
                                              loop2 pred_todo' obs' worklist' candidates'
                    | otherwise          =    loop2 pred_todo' obs  worklist  candidates
                  where (u0, pred_todo') = Set.deleteFindMin pred_todo
        isCond []  = False
        isCond [_] = False
        isCond _   = True
    


confirm :: Map Node [Node] -> Map Node Node -> Node -> Node -> Bool
confirm sucs obs u u_obs =
    let result0 = False in
    let succ0 = Set.fromList $ sucs ! u in
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
  where pres = Map.fromList [ (n, Set.fromList $ pre g n) | n <- nodes g]
        sucs = Map.fromList [ (n,                suc g n) | n <- nodes g]
        loop w obs worklist
            | Set.null worklist = -- traceShow (w, obs, worklist) $
                                  (w, obs)
            | otherwise         = -- traceShow (w, obs, worklist, "*****", u, candidates, new_nodes, obs') $
                                  loop (w ∪ new_nodes)   (Map.union (Map.fromSet id new_nodes) obs')   (worklist' ∪ new_nodes)
          where (u, worklist') = Set.deleteFindMin worklist
                (candidates, obs') =  propagate pres sucs w obs u u
                new_nodes = Set.filter (\v ->  confirm sucs obs' v u) candidates

wdSlice :: Graph gr => gr a b -> Set Node -> Set Node
wdSlice g = fst . (main g)

wccSlice :: Graph gr => gr a b -> Set Node -> Set Node
wccSlice g v' = w ∩ fromV'
  where (w,_) = main g v'
        fromV' = Set.fromList $ dfs (Set.toList v') g
        -- fromV' = (Set.fromList $ [ n | m <- Set.toList v', n <- reachable m g ])


nticdMyWodViaWDSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodViaWDSlice graph = \ms -> let wd = wdSlice graph ms
                                    in nticd wd
  where nticd = nticdSlice graph




data Reachability  = Unreachable | Reached Node | Phi (Set Node) deriving (Show, Eq)
instance JoinSemiLattice Reachability where
  Unreachable   `join` x           = x
  x             `join` Unreachable = x

  Reached x `join` Reached y
    | x == y    = Reached x
    | otherwise = Phi (Set.fromList [x,y])


  Reached x `join` Phi ys = Phi (Set.insert x ys)
  Phi xs `join` Reached y = Phi (Set.insert y xs)

  Phi xs `join` Phi ys = Phi (xs ∪ ys)

instance BoundedJoinSemiLattice Reachability where
  bottom = Unreachable


braunF :: Graph gr => gr a b -> Set Node -> Map Node (Set Node) -> Map Node (Set Node)
braunF g ms0 phi = Map.fromList [ (n, Set.fromList [n])                | n <- Set.toList ms0 ]
                 ⊔ Map.fromList [ (n, phi ! n'        )                | n <- nodes g, not $ n ∈ ms0, [n'] <- [suc g n] ]
                 ⊔ Map.fromList [ (n, (∐) [ phi ! n' | n' <- succs])  | n <- nodes g, not $ n ∈ ms0, let succs = suc g n, length succs > 1 ]

braunLfp g ms0 = (㎲⊒) (Map.fromList [(n, Set.empty) | n <- nodes g]) (braunF g ms0)



braunF2 :: Graph gr => gr a b -> Set Node -> Map Node (Set Node) -> Map Node (Set Node)
braunF2 g ms0 phi = Map.fromList [ (n, Set.fromList [n])                              | n <- Set.toList ms0 ]
                  ⊔ Map.fromList [ (n, Set.insert n $ (∐) [ phi ! n' | n' <- succs, let rs = reachable n' g, (∃) ms0 (\m -> m `elem` rs)])  | n <- nodes g, not $ n ∈ ms0, let succs = suc g n]

braunLfp2 g ms0 = (㎲⊒) (Map.fromList [(n, Set.empty) | n <- nodes g]) (braunF2 g ms0)


braunEq :: Graph gr => gr a b -> Set Node -> Map Node Reachability
braunEq g ms0    =  Map.fromList [ (n, Reached n)                      | n <- Set.toList ms0 ]
                  ⊔ Map.fromList [ (n, Reached n')                     | n <- nodes g, not $ n ∈ ms0, [n'] <- [suc g n] ]
                  ⊔ Map.fromList [ (n, Phi (Set.fromList succs))       | n <- nodes g, not $ n ∈ ms0, let succs = suc g n, length succs > 1 ]
                  ⊔ Map.fromList [ (n, Unreachable)                    | n <- nodes g, not $ n ∈ ms0, []   <- [suc g n]]



solvePhiEquationSystem :: Set Node -> Map Node Reachability -> Map Node Reachability
solvePhiEquationSystem ms0 s = if (s == s') then s else solvePhiEquationSystem ms0 s'
          where s' =             Map.fromList [ (n, Reached n)                      | n <- Set.toList ms0 ]
                    `Map.union`  Map.fromList [ (n, nonTrivialAt n $ case rn of
                                              Unreachable -> Unreachable
                                              Reached n'  -> s `at` n' 
                                              Phi ns      -> (∐) [ s `at` n' | n' <- Set.toList ns]
                                        )
                                      | (n, rn) <- Map.assocs s ]
                at s n' = case s ! n' of
                            Unreachable -> Unreachable
                            Reached n'' -> Reached n''
                            _           -> Reached n'
                nonTrivialAt _ Unreachable = Unreachable
                nonTrivialAt n (Reached n')
                  | n == n' = Unreachable
                  | otherwise = Reached n'
                nonTrivialAt n (Phi ns') = case Set.toList $ Set.delete n ns' of
                    []   -> error "Unreachable"
                    [n'] -> Reached n'
                    _    -> Phi ns'
                -- nontrivialAt n (Phi ns) = if      Set.null ns' then
                --                             Unreachable
                --                           else if Set.size (Set.delete n ns') > 1 then
                --                             Phi ns
                --                           else 
                --   where ns' = Set.filter (\n' -> s ! n /= Unreachable) ns

braunSlice g ms = ms ∪ Set.fromList [ n | (n, r) <- Map.assocs $ solvePhiEquationSystem ms $ braunEq g ms, isPhi r]
  where isPhi (Phi _) = True
        isPhi _       = False



wodTEILSliceViaBraunF2 :: forall gr a b. DynGraph gr => gr a b -> Set Node -> Set Node
wodTEILSliceViaBraunF2 g ms0 =  (㎲⊒) Set.empty f
  where 
        f ms = -- traceShow ms $ 
               ms0
             ∪ Set.fromList [ n |  n <- nodes g, (length $ nub $ [ braun2 ! x ∩ ms | x <- suc g n, not $ Set.null $  braun2 ! x ∩ ms ]) > 1]
          where braun2 = braunLfp2 g ms
