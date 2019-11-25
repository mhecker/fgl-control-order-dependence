{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
#define SKIP_INDEPENDENT_NODES_M
module MicroArchitecturalDependence where

import qualified Data.List as List

import Data.Bits (xor, (.&.), shiftL, shiftR, complement)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap


import Algebra.Lattice(JoinSemiLattice(..), BoundedJoinSemiLattice(..))

import Debug.Trace (traceShow)
import Control.Exception.Base (assert)


import Control.Monad.State
import Control.Monad.List


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic (grev)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.DFS (dfs, rdfs, topsort)
import Data.Graph.Inductive.Query.TransClos (trc)

import Unicode
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
import IRLSOD (CFGNode, CFGEdge(..), GlobalState(..), globalEmpty, ThreadLocalState, Var(..), isGlobal, Array(..), arrayIndex, isArrayIndex, arrayMaxIndex, arrayEmpty, ArrayVal, Val, BoolFunction(..), VarFunction(..), Name(..), useE, defE, useEFor, useBFor, useB, useV, use, def, SimpleShow (..), stepFor)
import qualified IRLSOD as IRLSOD (Input)

import Program (Program(..))
import Program.Generator (toCodeSimple)
import Program.For (compileAllToProgram, For(..), subCommands)

import Data.Graph.Inductive.Util (mergeTwoGraphs, isTransitive, fromSuccMap, delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominance (mdomOfLfp, sinkdomOfGfp, sinkdomsOf, isinkdomOfTwoFinger8)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (isinkDFTwoFinger)
import Data.Graph.Inductive.Query.Slices.PostDominance (wodTEILSliceViaISinkDom)

import           Data.Graph.Inductive.Query.InfiniteDelay (TraceWith (..), Trace)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (Input(..))


type ConcreteSemantic a = CFGEdge -> a -> Maybe a

type AbstractSemantic a e = CFGEdge -> a -> [(e,a)]

type AbstractLeq a = (a -> a -> Bool)

type NormalState = (GlobalState,ThreadLocalState, ())

type TimeState = Integer

type TimeCost = Integer

type AbstractMicroArchitecturalGraphNode = Node

data MergedMicroState a a'  = Unmerged a | Merged a' deriving (Eq, Ord, Show)

instance (SimpleShow a, SimpleShow a') => SimpleShow (MergedMicroState a a') where
  simpleShow (Unmerged a) = simpleShow a
  simpleShow (Merged a')  = simpleShow a'

data MicroArchitecturalAbstraction a a' e = MicroArchitecturalAbstraction {
    muIsDependent :: forall gr. DynGraph gr =>
         gr CFGNode CFGEdge
      -> Set AbstractMicroArchitecturalGraphNode
      -> Map AbstractMicroArchitecturalGraphNode (Maybe AbstractMicroArchitecturalGraphNode)
      -> AbstractMicroArchitecturalGraphNode
      -> Node
      -> MergedMicroState a a'
      -> Bool,
    muMerge :: Bool,
    muGraph'For :: forall gr. DynGraph gr => gr CFGNode CFGEdge -> CsGraph a e -> Node -> [gr (Node, MergedMicroState a a' ) e],
    muInitialState :: a,
    muStepFor :: AbstractSemantic a e,
    muLeq :: Maybe (MergeMode a),
    muCostsFor :: CsGraph a e -> Map (Node, Node, CFGEdge) (Set TimeCost)
  }


stateSetsSlow :: (Graph gr, Ord s, Ord e) => AbstractSemantic s e -> gr CFGNode CFGEdge -> s -> Node -> (Set (Node, s), Set ((Node, s), e, (Node, s)))
stateSetsSlow step g  σ0 n0 = (㎲⊒) (Set.fromList [(n0,σ0)], Set.fromList []) f
  where f (cs, es) = (cs ∪ Set.fromList [  (n', σ') | (n, σ, e', n', σ') <- next ],
                      es ∪ Set.fromList [ ((n,  σ ), e', (n', σ')) | (n, σ, e', n', σ') <- next ]
                     )
          where next = [ (n, σ, e', n', σ')  | (n,σ) <- Set.toList cs, (n',e) <- lsuc g n, (e',σ') <- step e σ]


type CsGraph s e =  (IntMap (Set s), IntMap (Set (s, e, (Node, s))))

data MergeMode s = AbstractLeq (AbstractLeq s) | JoinNode (s -> s -> s) (s -> s -> Bool)

stateSets :: forall gr s e. (Graph gr, Ord s, Show s, Show e, Ord e) => AbstractSemantic s e -> Maybe (MergeMode s) -> gr CFGNode CFGEdge -> s -> Node -> CsGraph s e
stateSets step (Just (AbstractLeq leq)) g σ0 n0 = filter result
  where result = go (IntMap.fromList [(n0, Set.fromList [σ0])]) (IntMap.fromList [(n0,Set.fromList [σ0])]) (IntMap.fromList [])
        go :: IntMap (Set s) -> IntMap (Set s) -> IntMap (Set (s, e, (Node, s))) -> (IntMap (Set s), IntMap(Set (s, e, (Node, s))))
        go workset cs es
         | IntMap.null workset = (cs, es)
         | otherwise         = {- traceShow workset $ -}
                               {- traceShow "=============================" $ traceShow (Map.lookup 11 workset) $ traceShow (Map.lookup 11 cs) $ traceShow (Map.lookup 11 es) $ -}
                               go (workset'' ⊔ csNew) (cs' ⊔ csNew) (es ⊔ esNew)
             where ((n,σs), workset') = IntMap.deleteFindMin workset
                   (σ, σs') = Set.deleteFindMin σs
                   workset''
                       | Set.null σs'' =                        workset'
                       | otherwise     = IntMap.insert n σs'' $ workset'
                     where σs'' = Set.filter (\σ' -> assert (σ /= σ') $ (not $ σ' `leq` σ)) σs'
                   cs' = IntMap.adjust f n cs
                     where f    = Set.filter (\σ' ->        (σ' == σ) ∨ (not $ σ' `leq` σ))
                   next = [ (e', n', σ')  | (n',e) <- lsuc g n, (e',σ') <- step e σ]
                   
                   csNew = (∐) [ IntMap.fromList [ (n', Set.fromList [ σ' ]) ]  | (e, n', σ') <- next, not $ old n' σ' ]
                     where old n' σ' = case IntMap.lookup n' cs of
                             Nothing -> False
                             Just σs' -> σ' ∈ σs' ∨ ((∃) σs' (\σ'' -> σ' `leq` σ''))
                   esNew = IntMap.fromList [ (n, Set.fromList  [ (σ, e', (n', σ')) | (e', n', σ') <- next ] )]

        filter :: CsGraph s e -> CsGraph s e
        filter (cs, es) = (cs, IntMap.mapWithKey f es)
           where f n ess = Set.fromAscList $ [ (σ, e', (n', new n' σ')) | (σ, e', (n', σ')) <- Set.toAscList ess, (σ ∈ cs !! n) ]
                   where new n' σ' = if σ' ∈ σs' then σ' else  σ''
                           where σs' = cs !! n'
                                 σ'' = head $ [ σ'' | σ'' <- Set.toList σs', σ' `leq` σ'' ]

        (!!) = (IntMap.!)

stateSets step Nothing g σ0 n0 = result
  where result = go (IntMap.fromList [(n0, Set.fromList [σ0])]) (IntMap.fromList [(n0,Set.fromList [σ0])]) (IntMap.fromList [])
        go :: IntMap (Set s) -> IntMap (Set s) -> IntMap (Set (s, e, (Node, s))) -> (IntMap (Set s), IntMap (Set (s, e, (Node, s))))
        go workset cs es
         | IntMap.null workset = (cs, es)
         | otherwise         = go (workset'' ⊔ csNew) (cs ⊔ csNew) (es ⊔ esNew)
             where ((n,σs), workset') = IntMap.deleteFindMin workset
                   (σ, σs') = Set.deleteFindMin σs
                   workset''
                     | Set.null σs' =                       workset'
                     | otherwise    = IntMap.insert n σs' $ workset'
                   next = [ (e', n', σ')  | (n',e) <- lsuc g n, (e',σ') <- step e σ]
                   
                   csNew = (∐) [ IntMap.fromList [ (n', Set.fromList [ σ' ]) ]  | (e, n', σ') <- next, not $ old n' σ' ]
                     where old n' σ' = case IntMap.lookup n' cs of
                             Nothing -> False
                             Just σs -> σ' ∈ σs
                   esNew = IntMap.fromList [ (n, Set.fromList  [ (σ, e', (n', σ')) | (e', n', σ') <- next ] )]

stateSets step (Just (JoinNode (⊔) (⊑))) g σ0 n0 = (
           fmap Set.singleton cs,
           IntMap.fromAscList [ (n, Set.fromList [ (cs !! n, e, (n', cs !! n')) | (e, n') <- Set.toList esN ]) | (n, esN) <- IntMap.toAscList es ]
         )
  where (cs, es) = go (IntSet.singleton n0)
                      (IntMap.insert n0 σ0 $ IntMap.empty)
                      (IntMap.empty)
        go :: IntSet -> IntMap s -> IntMap (Set (e, Node)) -> (IntMap s, IntMap (Set (e, Node)))
        go workset cs es
         | IntSet.null workset = (cs, es)
         | otherwise         =
                               -- traceShow "{=======" $  traceShow (n, workset) $ traceShow cs $ traceShow new $ traceShow "====}"
                               go workset0' cs' es'
             where (n, workset0) = IntSet.deleteFindMin workset
                   σ = cs !! n

                   all = [ (e', n', σ') | (n',e) <- lsuc g n, (e',σ') <- step e σ] 
                   new = filter (\(_, n', σ') ->  case IntMap.lookup n' cs of { Nothing -> True ; Just σ'0 -> not $ σ' ⊑ σ'0 }) all

                   cs'       = foldr adjust cs       new
                     where adjust (e', n', σ')    = IntMap.insertWith (⊔) n' σ'

                   es'       = foldr insert es       all
                     where insert (e', n', σ')    = IntMap.insertWith (∪) n (Set.singleton $ (e', n'))

                   workset0' = foldr insert workset0 new
                     where insert (e', n', σ')    = IntSet.insert n'

        (!!) = (IntMap.!)


stateGraphForSets :: (Ord s, Graph gr, Ord e) => CsGraph s e -> gr (Node, s) e
stateGraphForSets (cs, es) = mkGraph nodes [(toNode ! (n, cache), toNode ! c', e) | (n, cacheEdges) <- IntMap.toList es, (cache, e, c') <- Set.toList cacheEdges ]
  where nodes = zip [0..] [ (n, cache) | (n, caches) <- IntMap.toList cs, cache <- Set.toList caches ]
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

stateGraph :: (Graph gr, Ord s, Show s, Show e, Ord e) => AbstractSemantic s e -> Maybe (MergeMode s) -> gr CFGNode CFGEdge -> s -> Node -> gr (Node, s) e
stateGraph step leq g σ0 n0 = stateGraphForSets (cs, es)
  where (cs, es) = stateSets step leq g σ0 n0


merged :: (Graph gr, Ord e, Ord id) => gr (id, s) e ->  Map id (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode)) -> gr (id, Set AbstractMicroArchitecturalGraphNode) e
merged csGraph' equivs =  mkGraph nodes' edges
  where edges =  Set.toList $ Set.fromList $ fmap f $ (labEdges csGraph')
          where f (y,y',e) = (toNode ! (n,equiv), toNode ! (n', equiv'), e)
                  where Just (n,_)  = lab csGraph' y
                        Just (n',_) = lab csGraph' y'
                        equiv  = representative $ equivs ! n  ! y
                        equiv' = representative $ equivs ! n' ! y'
        nodes = zip [0..] (Set.toList $ Set.fromList $ [ (n, representative equiv) | (n, equivN) <- Map.assocs equivs, equiv <- Map.elems equivN ])
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        representative = Set.findMin -- use the first node in a equivalence class as representative

        nodes' = fmap fromRep nodes
          where fromRep (i,(n,y)) = (i, (n, equivs ! n ! y))



mergedI :: (Graph gr, Ord e) => gr (Node, s) e ->  IntMap (IntMap IntSet) -> gr (Node, Set AbstractMicroArchitecturalGraphNode) e
mergedI csGraph' equivs =  mkGraph nodes' edges
  where edges =  Set.toList $ Set.fromList $ fmap f $ (labEdges csGraph')
          where f (y,y',e) = (toNode ! (n,equiv), toNode ! (n', equiv'), e)
                  where Just (n,_)  = lab csGraph' y
                        Just (n',_) = lab csGraph' y'
                        equiv  = representative $ equivs !! n  !! y
                        equiv' = representative $ equivs !! n' !! y'
        nodes = zip [0..] (Set.toList $ Set.fromList $ [ (n, representative equiv) | (n, equivN) <- IntMap.toAscList equivs, equiv <- IntMap.elems equivN ])
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        representative = IntSet.findMin -- use the first node in a equivalence class as representative

        nodes' = fmap fromRep nodes
          where fromRep (i,(n,y)) = (i, (n, Set.fromAscList $ IntSet.toAscList $ equivs !! n !! y))

        (!!) = (IntMap.!)





mergeFromSlow :: forall id e s gr. (Ord id, DynGraph gr, Show e, Ord e) =>
  Map id (Set AbstractMicroArchitecturalGraphNode) ->
  gr (id, s) e ->
  Map AbstractMicroArchitecturalGraphNode (Maybe AbstractMicroArchitecturalGraphNode) ->
  Set AbstractMicroArchitecturalGraphNode ->
  Map id (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
mergeFromSlow nodesToCsNodes csGraph idom roots  =  (𝝂) init f 
  where 
        f :: Map id (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
          -> Map id (Map AbstractMicroArchitecturalGraphNode (Set AbstractMicroArchitecturalGraphNode))
        f equivs = -- traceShow (Map.filter (\equivs -> (∃) equivs (not . Set.null)) $ equivs, rootOf) $
          (
              Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y' | y' <- Set.toList ys, Map.lookup y' rootOf == Just r ]) ] | y <- Set.toList ys, Just r <- [Map.lookup y rootOf ]])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
            ⊔ Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y ] ) ] |  y <- Set.toList ys])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
            ⊔ Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y' |
                                                                   let es  = Set.fromList $ fmap snd $ lsuc csGraph y ,
                                                                   y' <- Set.toList ys,
                                                                   let es' = Set.fromList $ fmap snd $ lsuc csGraph y',
                                                                   assert (es == es') True,
                                                                   (∀) es (\e ->
                                                                     (∀) (lsuc csGraph y ) (\(x,  ey ) -> if ey  /= e  then True else
                                                                     (∀) (lsuc csGraph y') (\(x', ey') -> if ey' /= e  then True else
                                                                       let Just (m, _) = lab csGraph x
                                                                           Just (m',_) = lab csGraph x'
                                                                       in assert (m == m') $ 
                                                                       (∃) (equivs ! m) (\equiv -> x ∈ equiv ∧ x' ∈ equiv)
                                                                     ))
                                                                   )
                                                ]
                                  )] | y <- Set.toList ys, not $ y ∈ roots])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
           )
        init = Map.fromList [ (n, Map.fromList [ (y, ys) | y <- Set.toList ys] ) | (n,ys) <- Map.assocs $ nodesToCsNodes]
        rootOf = Map.fromList [ (y, r) | y <- nodes csGraph, let r = maxFromTreeM idom y, r ∈ roots ]





mergeFrom ::  (DynGraph gr) =>
  gr CFGNode CFGEdge ->
  gr (Node, s) CFGEdge ->
  Map AbstractMicroArchitecturalGraphNode (Maybe AbstractMicroArchitecturalGraphNode) ->
  Set AbstractMicroArchitecturalGraphNode ->
  IntMap (IntMap IntSet)
mergeFrom graph csGraph idom roots = mergeFromForEdgeToSuccessor graph csGraph  idom roots



mergeFromForEdgeToSuccessor ::  (DynGraph gr, Show e, Ord e) =>
  gr CFGNode CFGEdge ->
  gr (Node, s) e ->
  Map AbstractMicroArchitecturalGraphNode (Maybe AbstractMicroArchitecturalGraphNode) ->
  Set AbstractMicroArchitecturalGraphNode ->
  IntMap (IntMap IntSet)
mergeFromForEdgeToSuccessor graph csGraph idom roots = assert (result == IntMap.fromAscList [ (n, IntMap.fromAscList [ (y, IntSet.fromAscList $ Set.toAscList ys) | (y, ys) <- Map.assocs yys ])  | (n, yys) <- Map.assocs $  mergeFromSlow  (Map.fromAscList [ (n, Set.fromAscList $ IntSet.toAscList $ ys) | (n, ys) <- IntMap.toAscList nodesToCsNodes]) csGraph idom roots]) result
  where result = (go orderToNodes init) ⊔ equivsNBase
          where (⊔) :: IntMap (IntMap IntSet) -> IntMap (IntMap IntSet) -> IntMap (IntMap IntSet)
                (⊔) left right = IntMap.unionWithKey f left right
                f n fromSuccessorsN  fromBaseN = IntMap.unionWithKey g fromSuccessorsN fromBaseN
                g y fromSuccessorsYs fromBaseYs = {- assert (fromBaseYs ⊆ fromSuccessorsYs) $ -} fromSuccessorsYs
        (!!) = (IntMap.!)
        (∈∈) = (IntSet.member)
        (∖∖) = (IntSet.difference)
        fromIntSet f s = IntMap.fromAscList [ (y, f y) | y <- IntSet.toAscList s]
        rootsI = IntSet.fromAscList $ Set.toAscList $ roots
        go workset fromSuccessors
           | IntMap.null workset  = fromSuccessors
           | otherwise         =
               if changed then
                 go (workset' `IntMap.union` influenced) (IntMap.insert n (fromSuccessorsN' ⊔ fromRootsN) fromSuccessors)
               else
                 go  workset'                                                                             fromSuccessors
          where ((_,n), workset') = IntMap.deleteFindMin workset
                ys = nodesToCsNodes !! n
                fromRootsN = fromRoots !! n
                fromSuccessorsN' = goSuccessors (ys ∖∖ rootsI) IntMap.empty
                  where goSuccessors ysLeft fromsucc
                           | IntSet.null ysLeft = fromsucc
                           | otherwise = assert (y ∈∈ y's) goSuccessors ysLeft' ((IntMap.fromSet (const y's) y's) `IntMap.union` fromsucc)
                          where y = IntSet.findMin ysLeft
                                es = (∐) [ Map.fromList [ (e, Set.fromList [(x,m)]) ]  | (x,e) <- lsuc csGraph y, let Just (m, _) = lab csGraph x ]

                                y's     = IntSet.insert y y's0
                                ysLeft' = IntSet.delete y ysLeft'0
                                (y's0, ysLeft'0) = IntSet.partition (\y' -> 
                                                                   (∀) (lsuc csGraph y') (\(x', e') -> (∀) (es ! e') (\(x,m) -> 
                                                                          (x  ∈∈ IntMap.findWithDefault IntSet.empty x' (fromSuccessors !! m)  ∨  (x ∈∈ (equivsNBase !! m !! x')))
                                                                   ))
                                                               )
                                                               ysLeft

                changed = assert (fromSuccessorsN ⊒ fromSuccessorsN') $
                          assert (diffSize == (fromSuccessorsN' /= fromSuccessorsN)) $ diffSize
                  where fromSuccessorsN = fromSuccessors !! n
                        diffSize = IntMap.size fromSuccessorsN /= IntMap.size fromSuccessorsN'
                                 ∨ (∃) (zip (IntMap.toAscList fromSuccessorsN) (IntMap.toAscList fromSuccessorsN')) (\((y,ys), (y', y's)) -> assert (y == y') $ IntSet.size ys /= IntSet.size y's)
                influenced = IntMap.fromList [ (nodesToOrder !! m, m) | m <- pre graph n]

        init = IntMap.mapWithKey (\n ys -> IntMap.fromSet (const ys) ys) nodesToCsNodes
        rootOf = IntMap.fromList [ (y, r) | y <- nodes csGraph, let r = maxFromTreeM idom y, r ∈ roots ]

        nodesToCsNodes = IntMap.fromList [ (n, IntSet.fromList [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

        fromRoots = IntMap.mapWithKey (\n ys -> go ys IntMap.empty) nodesToCsNodes
          where go ysLeft fromroots
                  | IntSet.null ysLeft = fromroots
                  | otherwise = let mr = IntMap.lookup y rootOf in case mr of
                        Nothing -> go ysLeft0                                          fromroots
                        Just r  -> let (y's, ysLeft') = IntSet.partition (\y' -> IntMap.lookup y' rootOf == mr) ysLeft in
                                   go ysLeft' (fromIntSet (const y's) y's `IntMap.union` fromroots)
                      where (y, ysLeft0) = IntSet.deleteFindMin ysLeft

        equivsNBase = IntMap.mapWithKey (\n ys -> fromRoots !! n ⊔ (fromIntSet IntSet.singleton $ (ys ∖∖ rootsI))) nodesToCsNodes

        order = List.reverse $ topsort graph
        nodesToOrder = IntMap.fromList $ zip order [0..]
        orderToNodes = IntMap.fromList $ zip [0..] order


csGraphSize :: CsGraph s e -> Int
csGraphSize (cs, es) = IntMap.fold (\σs k -> Set.size σs + k) 0 cs

muMergeDirectOf :: forall gr a a' e. (DynGraph gr, Ord a, Show a, Show e, Ord e) => MicroArchitecturalAbstraction a a' e -> gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
muMergeDirectOf mu@( MicroArchitecturalAbstraction { muIsDependent, muMerge, muGraph'For, muInitialState, muLeq, muStepFor, muCostsFor }) graph n0 = traceShow (csGraphSize csGraph) $ invert'' $
  Map.fromList [ (m, ns) | m <- nodes graph,
      -- m == 31,
#ifdef SKIP_INDEPENDENT_NODES_M
      mayBeCSDependent m,
#endif
      csGraph' <- (muGraph'For graph csGraph m ::  [gr (Node, MergedMicroState a a') e]),
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let y's  = [ y | (y, (n', csy)) <- labNodes csGraph', m == n' ],
      let idom' = Map.fromList $ iPDomForSinks [[y'] | y' <- y's] csGraph',
      let roots' = Set.fromList y's,
      let ns = if muMerge then
            let equivs = mergeFromForEdgeToSuccessor graph' csGraph'  idom' roots'
                csGraph'' = mergedI csGraph' equivs
                idom'' = isinkdomOfTwoFinger8 csGraph''
            in Set.fromList [ n | (y, (n,_))   <- labNodes csGraph'', n /= m, Set.null $ idom'' ! y] -- TODO: can we make this wotk with muIsDependent, too?
          else Set.fromList [ n | (y, (n,mms)) <- labNodes csGraph' , n /= m, muIsDependent graph roots' idom' y n mms]
   ]
  where csGraph@(cs, es)  = stateSets muStepFor muLeq graph muInitialState n0
#ifdef SKIP_INDEPENDENT_NODES_M
        costs = muCostsFor csGraph
        mayBeCSDependent m = (∃) (lsuc graph m) (\(n,l) -> Set.size (costs ! (m,n,l)) > 1)
#endif         


muGraphFromMergeDirectFor :: forall gr a a' e. (DynGraph gr, Ord a, Show a, Ord e, Show e) =>
  MicroArchitecturalAbstraction a a' e ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) e
muGraphFromMergeDirectFor mu graph n0 m = mergedI muGraph' equivs
    where (equivs, muGraph') = mergeDirectFromFor mu graph n0 m

mergeDirectFromFor :: forall gr a a' e. (DynGraph gr, Ord a, Show a, Ord e, Show e) =>
  MicroArchitecturalAbstraction a a' e ->
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  (IntMap (IntMap IntSet),
   gr (Node, MergedMicroState a a') e
  )
mergeDirectFromFor mu@( MicroArchitecturalAbstraction { muGraph'For, muInitialState, muLeq, muStepFor, muCostsFor }) graph n0 m = (mergeFromForEdgeToSuccessor graph' csGraph'  idom roots, csGraph')
  where   csGraph@(cs, es) = stateSets muStepFor muLeq graph muInitialState n0
          
          csGraph' = head $ muGraph'For graph csGraph m 
          graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m
          nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph', n == n' ] ) | n <- nodes graph']
          y's  = nodesToCsNodes ! m
          
          idom = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'
          roots = Set.fromList y's

