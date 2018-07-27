{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert
module Data.Graph.Inductive.Query.InfiniteDelay where

-- import Data.Ord (comparing)
import Data.Maybe(fromJust)
import Control.Monad (liftM, foldM, forM, forM_)

import System.Random
import Control.Monad.Random


-- import Control.Monad.ST
-- import Data.STRef

-- import Data.Functor.Identity (runIdentity)
-- import qualified Control.Monad.Logic as Logic
import Data.List(foldl', intersect,foldr1, partition, isPrefixOf)

import Data.Maybe (isNothing, maybeToList)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
-- import Data.Graph.Inductive.Query.DFS (reachable)
-- import Data.Graph.Inductive.Query.Dominators (dom, iDom)
-- import Data.Graph.Inductive.Query.ControlDependence (controlDependence)

import Data.Graph.Inductive.Query.BalancedSCC (samplePathsFor)




-- import Algebra.Lattice
-- import qualified Algebra.PartialOrd as PartialOrd

import qualified Data.List as List

import Data.List ((\\), nub, sortBy, groupBy)

import Util
import Unicode



-- import Data.Graph.Inductive.Query.TransClos
-- import Data.Graph.Inductive.Basic hiding (postorder)
-- import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.DFS (reachable)

import Data.Graph.Inductive.Query.NTICD
-- import Data.Graph.Inductive.Query.LCA


import Debug.Trace
import Control.Exception.Base (assert)


inSameBranch g = \start n m -> {-(m `elem` reachable n g) ∧ -} (n `elem` reachable start g   ∧   m `elem` reachable start g)  ∧  (
        -- let pns = Set.fromList [ p | (p,ns) <- Map.assocs nticd, p `elem` reachable start g, n ∈ ns ]
        --     pms = Set.fromList [ p | (p,ns) <- Map.assocs nticd, p `elem` reachable start g, m ∈ ns ]
        -- in pns == pms  ∧  (not $ Set.null pms) ∧  (∀) pms (\p ->  (∃) (suc g p) (\x -> n ∈ sinkdom ! x  ∧  m ∈ sinkdom ! x))
        (∃) (Map.assocs nticd) (\(p,ns) -> p `elem` reachable start g   ∧    m ∈ ns   ∧         n ∈ ns  ∧  (∃) (suc g p) (\x -> n ∈ sinkdom ! x  ∧  m ∈ sinkdom ! x))
      -- ∨ (∀) (Map.assocs nticd) (\(p,ns) -> (not $ m ∈ ns)  ∧  (not $ n ∈ ns))
      ∨ (Set.fromList [n,m] ⊆ reachableFrom sinkdom (Set.fromList [start]) (Set.empty))
    )
  where nticd = nticdF3 g
        sinkdom = sinkdomOfGfp g

delayedInfinitely g = \trace m -> case trace of
    []        -> False
    (start:_) -> (not $ m `elem` trace) ∧ (∃) (trace) (\n ->  insame start n m)
  where insame = inSameBranch g


sampleLoopPathsFor :: (Eq b, Graph gr)             => Int -> Integer ->  gr a b ->   [[LEdge b]]
sampleLoopPathsFor seed k g = fmap reverse $ evalRand (sampleLoopPaths k g) (mkStdGen seed)

sampleLoopPaths :: (MonadRandom m, Graph gr, Eq b) =>        Integer -> gr a b -> m [[LEdge b]]
sampleLoopPaths         k g
  | null (nodes g) = return []
  | otherwise      = sampleSome [] 0
     where 
        sample :: MonadRandom m => [t] -> m t
        sample xs = do
          i <- getRandomR (1, length xs)
          return $ xs !! (i-1)
        sampleSome sampled i
          | i >= k            = return $ sampled
          | otherwise         = do
              n0 <- sample $ nodes g
              newTrace <- sampleTrace n0 []
              sampleSome (newTrace:sampled) (i+1)
        sampleTrace n trace
          | looped              = return trace
          | finished            = return []
          | otherwise = do
               (m,e) <- sample successors
               sampleTrace m ((n,m,e):trace)
         where finished   = null successors
               successors = lsuc g n
               looped     = n `elem` (fmap (\(n,_,_) -> n) trace)


data Input = Input { startNode :: Node, choice :: Map Node Node } deriving (Show, Eq, Ord)
data Trace = Finite [(Node,Node)] | Looping [(Node, Node)] [(Node,Node)] deriving (Show, Eq, Ord)

runInput :: Graph gr => gr a b -> Input -> Trace
runInput graph (Input { startNode, choice}) = 
       require  ((∀) (Map.assocs choice) (\(n,m) -> m `elem` suc graph n))
       require  ((∀) (nodes graph)       (\n -> ((length $ suc graph n) > 1)   →   Map.member n choice))
     $ require  ( startNode `elem` nodes graph)
     $ run startNode (Set.fromList [startNode]) []
  where run n seen trace
            | succs == [] = Finite  (reverse trace)
            | n' ∈ seen   = Looping prefix loop 
            | otherwise   = run n' (Set.insert n' seen) ((n,n') : trace) 
          where succs = suc graph n
                n' = case succs of
                       []   -> undefined
                       [n'] -> n'
                       _    -> choice ! n

                (prefix, loop) = span (\(n,m) -> n /= n') $ reverse ((n,n') : trace)

observable :: Set Node -> Trace -> Trace
observable s (Finite trace)        = Finite $ obs s trace
observable s (Looping prefix loop)
    | loop' == [] = Finite   prefix'
    | otherwise   = Looping  prefix' loop'
  where prefix' = obs s prefix
        loop'   = obs s loop


obs s =  filter (\(n, m) -> n ∈ s)

isTracePrefixOf (Finite trace) (Finite  trace')      = List.isPrefixOf trace trace'
isTracePrefixOf (Finite trace) (Looping prefix loop) =
      require (noLoop prefix) 
    $ List.isPrefixOf trace (prefix ++ loop)
isTracePrefixOf (Looping prefix loop) (Looping prefix' loop') =
      require (noLoop prefix )
    $ require (noLoop prefix')
    $ prefix == prefix'   ∧  loop ==  loop'

isTracePrefixOf (Looping prefix loop) (Finite trace) = False

noLoop l = nub l == l

infinitelyDelays :: Graph gr => gr a b -> Input -> Set Node -> Set Trace
infinitelyDelays graph input@(Input { startNode, choice }) s =
    case trace of
      Finite _    -> Set.fromList [traceObs]
      Looping _ _ -> case traceObs of
                       Looping _ _   -> Set.fromList [traceObs]
                       Finite prefix -> Set.fromList [
                                            trace'Obs
                                          | choice' <- allChoices graph choice0 (condNodes ∖ s),
                                            let trace' = runInput graph (Input { startNode = startNode , choice = choice' }),
                                            let trace'Obs = observable s trace',
                                            isTracePrefixOf traceObs trace'Obs
                                        ]
  where condNodes = Set.fromList [ c | c <- nodes graph, let succs = suc graph c, length succs  > 1]
        trace = runInput graph input
        traceObs = observable s trace
        choice0 = restrict choice s



allChoices :: Graph gr => gr a b  -> Map Node Node -> Set Node -> [Map Node Node]
allChoices graph choice conds
    | Set.null conds = [choice]
    | otherwise = do
                    n' <- suc graph n
                    allChoices graph (Map.insert n n' choice) conds'
  where (n, conds') = Set.deleteFindMin conds



sampleChoicesFor ::                              (Graph gr) => Int -> Integer ->  gr a b ->  [Map Node Node]
sampleChoicesFor seed k g = evalRand (sampleChoices k g) (mkStdGen seed)

sampleChoices :: forall m gr a b. (MonadRandom m, Graph gr) =>        Integer -> gr a b -> m [Map Node Node]
sampleChoices         k g = sampleSome [] 0
     where
        condNodes = Set.fromList [ c | c <- nodes g, let succs = suc g c, length succs  > 1]
        sample :: MonadRandom m => [t] -> m t
        sample xs = do
          i <- getRandomR (1, length xs)
          
          return $ xs !! (i-1)
        sampleSome :: [Map Node Node] -> Integer -> m [Map Node Node]
        sampleSome sampled i
          | i >= k    = return $ sampled
          | otherwise = do
              choice <- sampleChoice Map.empty condNodes
              sampleSome (choice:sampled) (i+1)
        sampleChoice :: Map Node Node -> Set Node -> m (Map Node Node)
        sampleChoice choice condNodes
          | Set.null condNodes = return choice
          | otherwise = do
               n' <- sample successors
               sampleChoice (Map.insert n n' choice) condNodes'
         where successors = suc g n
               (n, condNodes') = Set.deleteFindMin condNodes
