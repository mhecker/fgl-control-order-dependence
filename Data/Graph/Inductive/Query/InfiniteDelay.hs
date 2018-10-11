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
import Data.List(foldl', intersect,foldr1, partition, isPrefixOf, stripPrefix)

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
      ∨ (Set.fromList [n,m] ⊆ reachableFrom sinkdom (Set.fromList [start]))
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
data TraceWith a = Finite [(Node, Maybe Node, a)] | Looping [(Node, Maybe Node, a)] [(Node, Maybe Node, a)] deriving (Show, Eq, Ord)
type Trace = TraceWith ()


runInput :: Graph gr => gr a b -> Input -> Trace
runInput graph = \(Input { startNode, choice}) ->
    let run n seen trace = case Map.lookup n choice of
                             Nothing -> case succs of
                                          []   -> Finite (reverse $ (n, Nothing, ()) : trace)
                                          [n'] -> next n'
                             Just n' -> next n'
          where succs = succsOf ! n
                next n'
                    | n' ∈ seen = Looping prefix loop
                    | otherwise = run n' (Set.insert n' seen) ((n, Just n',()) : trace)
                  where (prefix, loop) = span (\(n,m,()) -> n /= n') $ reverse ((n, Just n',()) : trace)
        trace = run startNode (Set.fromList [startNode]) []
    in require  (Map.isSubmapOfBy (\succs n -> n ∈ succs) condNodes choice)
     $ require  (startNode `elem` nodes graph)
     $ assert   (wellformed trace)
     $ trace
  where (succsOf, condNodes0) = Map.partition (\succs -> length succs <= 1) $ Map.fromList [ (n, succs) | n <- nodes graph, let succs = suc graph n]
        condNodes = fmap Set.fromList condNodes0
        wellformed (Finite trace) = ((snd $ last trace) == Nothing) ∧ (∀) (fmap snd $ init trace) (/=Nothing)
        wellformed (Looping prefix loop) = (∀) (fmap snd prefix) (/= Nothing) ∧ (∀) (fmap snd loop) (/= Nothing)
        snd (_,b,_) = b

observable :: Eq a => Set Node -> TraceWith a -> TraceWith a
observable s (Finite trace)       = Finite   $ obs s trace
observable s (Looping prefix loop)
    | loop' == [] = Finite   prefix'
    | otherwise   = Looping  prefix' loop'
  where prefix' = obs s prefix
        loop'   = obs s loop


obs s =  filter (\(n,m,_) -> n ∈ s)

app trace trace' = ap trace trace'
  where ap (Finite   trace)       (Finite   trace'       ) =
            require ((∀) (fmap snd trace) (/=Nothing))
          $ Finite   (trace ++ trace')
        ap (Finite   trace)       (Looping  prefix' loop') =
            require ((∀) (fmap snd trace) (/=Nothing))
          $ Looping  prefix'' loop''
          where (prefix'', loop'') = case splitAtLoop [] (trace ++ prefix' ++ loop') of
                  Nothing                 -> (trace ++ prefix', loop')
                  Just (prefix'', loop'') -> (prefix'', loop'')

        ap (Looping  prefix loop) _                        = Looping prefix loop

        snd (_,m,_) = m

splitAtLoop prefix [] = Nothing
splitAtLoop prefix (x:xs)
    | startsWithX == [] = splitAtLoop (prefix++[x]) xs
    | otherwise         = Just (noX, startsWithX)
  where (noX,startsWithX) = break (==x) prefix
  

stripPostfix postfix list = case stripPrefix (reverse postfix) (reverse list) of
  Nothing -> list
  Just stripped -> reverse stripped

isTracePrefixOf (Finite trace)   (Finite   trace')       = List.isPrefixOf trace trace'
isTracePrefixOf (Finite trace)   (Looping prefix loop) =
      require (noLoop prefix) 
    $ List.isPrefixOf trace (prefix ++ (cycle loop))
isTracePrefixOf (Looping prefix loop) (Looping prefix' loop') =
      require (noLoop prefix )
    $ require (noLoop prefix')
    $ prefix == prefix'   ∧  loop ==  loop'
isTracePrefixOf (Looping prefix loop) _ = False

noLoop l = nub l == l


infinitelyDelays :: Graph gr => gr a b ->  Set Node -> Input -> Set Trace
infinitelyDelays graph s = \input@(Input { startNode, choice }) ->
    let trace = run input
        traceObs = observable s trace
    in case trace of
      Finite _ -> Set.fromList [traceObs]
      Looping prefix loop ->  Set.fromList [ traceObs `app` trace'Obs
                                           | choice' <- allChoices graph choice0 allowedToChange,
                                             startNode' <- fmap fst loop,
                                             let trace' = run (Input { startNode = startNode' , choice = choice' }),
                                             let trace'Obs = observable s trace'
                                        ]
        where 
              choice0 = restrict choice s
  where condNodes = Set.fromList [ c | c <- nodes graph, let succs = suc graph c, length succs  > 1]
        allowedToChange = condNodes ∖ s
        fst (n,_,_) = n
        run = runInput graph


isAscending continuations =
    (∀) continuations (\continuation ->  (∀) continuations (\continuation' ->
         continuation  `isTracePrefixOf` continuation'
       ∨ continuation' `isTracePrefixOf` continuation
    ))


isLowEquivalent g s input input' = isLowEquivalentFor (infinitelyDelays g s) (runInput g) (observable s) input

isLowEquivalentFor infinitelyDelays runInput observable input  = \input' ->
    let trace'    = runInput input' 
        trace'Obs = observable trace'
        continuations' = infinitelyDelays input'
        ascending' = isAscending continuations'
    in   (traceObs == trace'Obs)
       ∨ ( ascending   ∧   ascending'   ∧ (not $ Set.null $ continuations ∩ continuations'))
  where trace     = runInput input
        traceObs  = observable trace
        continuations  = infinitelyDelays input
        ascending  = isAscending continuations


timed :: Trace -> TraceWith Integer
timed (Finite   trace)         = Finite   [(n, m, i) | ((n,m,()), i) <- zip trace  [0..]]
timed (Looping prefix loop)    = Looping  [(n, m, i) | ((n,m,()), i) <- zip prefix [0..]] [(n, m, i) | ((n,m,()), i) <- zip loop [(List.genericLength prefix)..]]



-- isLowTimingEquivalent g s input input' = isLowEquivalentFor (infinitelyDelays g s) (runInput g) (observable s) input

isLowTimingEquivalent g s input = \input' ->
    let trace'  = run input'
    in (∀) s (\n -> 
        let  traceObs  = observable (Set.fromList [n]) $ timed $ trace
             trace'Obs = observable (Set.fromList [n]) $ timed $ trace'
            
        in   traceObs  `isTracePrefixOf` trace'Obs
           ∨ trace'Obs `isTracePrefixOf` traceObs
       )
  where run = runInput g 
        trace   = run input



isLowEquivalentTimed g s input = \input' ->
    let trace'  = run input'
        trace'Obs = observable s $ timed $ trace'
    in  traceObs  == trace'Obs
  where run = runInput g
        trace   = run input
        traceObs  = observable s $ timed $ trace

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
