{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert

module Data.Graph.Inductive.Query.PostDominance where

import Control.Exception.Base (assert)
import Control.Monad (foldM)

import System.Random (mkStdGen, randoms)

import Data.Ord (comparing)

import Data.Maybe(fromJust, isNothing, maybeToList)
import Data.List (sortBy)
import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import qualified Data.Tree as Tree
import Data.Tree (Tree(..))

import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)
import Data.Dequeue.SimpleDequeue (SimpleDequeue)

import Data.Foldable (maximumBy)
import qualified Data.Foldable as Foldable



import Data.Graph.Inductive.Util (controlSinks, immediateOf, fromSuccMap, nextCondNode, toNextCondNode, nextRealCondNode, prevRealCondNodes, toNextRealCondNode, prevCondNodes, prevCondImmediateNodes)
import Data.Graph.Inductive


import Unicode
import Util(foldM1, the, toSet, invert''', reachableFrom, reachableFromSeenM, reachableFromM, treeDfs)
import Data.Graph.Inductive.Query.LCA(lca, lcaSingleNodeSinks)


-- Speed this up, using http://dx.doi.org/10.1137/0205007 or http://dx.doi.org/10.1137/0205007 ?!?! See http://stackoverflow.com/questions/546655/finding-all-cycles-in-graph
cyclesInScc scc@(n:_) graph = cyclesFromIn scc graph n
cyclesFrom graph n = cyclesFromIn (nodes graph) graph n
cyclesFromIn nodes graph n = cyclesFromPath [n]
    where
      cyclesFromPath path@(n:_) =      [ n':(takeWhile (/=n') path) | n' <- suc graph n, n' ∊ nodes,       n' ∊ path]
                                   ++  [ cycle                      | n' <- suc graph n, n' ∊ nodes, not $ n' ∊ path, cycle <- cyclesFromPath (n':path) ]


data SinkPath = SinkPath { prefix :: [[Node]], controlSink :: [Node] } deriving Show

data MaximalPath          = MaximalPath { mPrefix :: [[Node]],  mScc :: [Node], mEndNodes  :: [Node] } deriving Show
data MaximalPathCondensed = MaximalPathCondensed {
  mcPrefix :: [Node],   -- of Nodes in the condensed graph
  mcScc ::  Node,       --    Node  in the condensed graph
  mcEndNodes :: [Node]  -- of Nodes in the original graph
 }

sinkPathsFor :: DynGraph gr => gr a b -> Map Node [SinkPath]
sinkPathsFor graph = Map.fromList [ (n, sinkPaths n) | n <- nodes graph ]
    where
      sccs = scc graph
      sccOf m =  the (m ∊) $ sccs
      sinks = controlSinks graph     -- TODO: dont repeat scc computation
      condensed = condensation graph --       or here
--      trcCondensed = trc condensed
      sinkPaths n = [ SinkPath { prefix = fmap (fromJust . (lab condensed)) revPath, controlSink = sink } | sink <- sinks , revPath <- revPaths (nodeMap ! (sccOf n)) ( nodeMap ! sink) ]
      revPaths :: Node -> Node -> [[Node]]
      revPaths ns sink
       | ns == sink    = [[]]
       | otherwise     = fmap (ns:) [ path | ns' <- suc condensed ns, path <- revPaths ns' sink ]
      nodeMap = Map.fromList [ (ns, n) | (n, ns) <- labNodes condensed ]




maximalPathsFor :: DynGraph gr => gr a b -> Map Node [MaximalPath]
maximalPathsFor graph = maximalPathsForNodes graph [ n | p <- condNodes, n <- suc graph p ++ [p]]
    where
      condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]

maximalPathsForNodes :: DynGraph gr => gr a b -> [Node] -> Map Node [MaximalPath]
maximalPathsForNodes graph relevantNodes = Map.fromList [ (n, maximalPaths n) | n <- relevantNodes]
    where
      sccs = scc graph
      sccOf m =  the (m ∊) $ sccs
      condensed = condensation graph --       or here
      maximalPaths n = [ MaximalPath { mPrefix   = reverse $  fmap (fromJust . (lab condensed)) $ mcPrefix revPath,
                                       mScc      =                 (fromJust . (lab condensed)) (mcScc revPath),
                                       mEndNodes = reverse $ mcEndNodes revPath
                                     }
                       |  revPath <- revPaths [(nodeMap ! (sccOf n))] ]
      revPaths :: [Node] -> [MaximalPathCondensed]
      revPaths (ns:rest)
         | suc condensed ns == []   =    pathsToCycleInNs
                                      ++ pathsToSinkInNs
         | (length nsNodes ) > 1    =    pathsToCycleInNs
                                      ++ pathsToSinkInNs
                                      ++ pathsToSuccessors
         | let [n] = nsNodes in
           n ∊ suc graph n     =    [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = nsNodes } ] -- ==  pathsToCycleInNs
                                      ++ pathsToSuccessors
         | otherwise                =    pathsToSuccessors
       where
         pathsToCycleInNs  = [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = cycle } | cycle <- cyclesInScc nsNodes graph ]
         pathsToSinkInNs   = [ MaximalPathCondensed { mcPrefix = rest, mcScc = ns, mcEndNodes = sink  } | sink  <- [ [n] | n <- nsNodes, length (suc graph n) == 0] ]
         pathsToSuccessors = [ path | ns' <- suc condensed ns, path <- revPaths (ns':ns:rest)]
         nsNodes = fromJust $ lab condensed ns
      nodeMap = Map.fromList [ (ns, n) | (n, ns) <- labNodes condensed ]


inPathFor graph' doms n (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  (MaximalPath []            endScc endNodes@(end:_))
                    | n ∊ endScc  = (∀) entries (\entry -> let domsEnd = (doms ! entry) `get` end in
                                                                (entry /= end || n == entry) && n ∊ domsEnd
                                         )
                                       ∨ (n ∊ endNodes)
                    | otherwise =  False
                inPathFromEntries entries  (MaximalPath (scc:prefix)  endScc endNodes)
                    | n ∊ scc = (∀) entries (\entry ->
                                      (∀) exits (\exit -> let domsexit = (doms ! entry) `get` exit in
                                             (entry /= exit || n == entry) && n ∊ domsexit)
                                     )
                                     ∨ (n ∊ endNodes)
                    | otherwise    =  inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = fromJust $ List.lookup key assocs


inSinkPathFor graph' n (s, path) = inSinkPathFromEntries [s] path
  where 
    inSinkPathFromEntries _       (SinkPath []           controlSink) = n ∊ controlSink
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n ∊ scc = (∀) entries (\entry -> let doms = (dom graph' entry) in
                          (∀) exits (\exit -> let domsexit = doms `get` exit in
                                 (entry /= exit || n == entry) && n ∊ domsexit)
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
            exits = [ n | (n,_) <- borderEdges ]
            get assocs key = fromJust $ List.lookup key assocs



mdomOf ::  DynGraph gr => gr a b -> Map Node (Set Node)
mdomOf graph = -- trace ("Sccs: " ++ (show $ length sccs) ++ "\t\tSize: " ++ (show $ length $ nodes graph)) $
               Map.fromList [ (y, Set.fromList [ x | x <- nodes graph, x `mdom` y]) | y <- nodes graph]
  where mdom x y =  (∀) (maximalPaths ! y) (\path ->       x `inPath` (y,path))
        maximalPaths = maximalPathsForNodes graph (nodes graph)
        inPath = inPathFor graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ]
        sccs = scc graph
        sccOf m =  the (m ∊) $ sccs

sinkdomOf ::  DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOf graph = Map.fromList [ (y, Set.fromList [ x | x <- nodes graph, x `sinkdom` y]) | y <- nodes graph]
  where sinkdom x y =  (∀) (sinkPaths ! y) (\path ->       x `inPath` (y,path))
        sinkPaths = sinkPathsFor graph
        inPath = inSinkPathFor graph




onedomOf dom z = Set.fromList $ [ x | y <- Set.toList (dom ! z),
                                      x <- Set.toList (dom ! y),
                                      x ∈ dom ! z,
                                      x /= y
                 ]



domsOf graph dom = Map.fromList [ (z, Set.fromList [ x | x <- Set.toList $ onedom z,
                                                        (∀) (onedom z) (\x' -> x' ∈ dom ! x)
                                      ]
                                  )
                                | z <- nodes graph
                   ]
  where onedom = onedomOf dom

sinkdomsOf graph = domsOf graph sinkdom
  where sinkdom = sinkdomOf graph


mdomsOf graph = domsOf graph mdom
  where mdom = mdomOf graph


type DomFunctional = Map Node (Set Node) ->  Map Node (Set Node)
type DomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> DomFunctional

domOfLfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
domOfLfp graph f = (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

domOfGfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
domOfGfp graph f = (𝝂) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
             ⊔ Map.fromList [ (y, Set.fromList $ reachable y) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

domOfGfpFullTop :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
domOfGfpFullTop graph f = (𝝂) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, all) | y <- nodes graph]
          where all = Set.fromList $ nodes graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph


fSinkDom graph _ _ nextCond toNextCond = f 
  where f sinkdomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Set.fromList $ toNextCond y)               | y <- nodes graph]
                    ⊔ Map.fromList [ (y,  (∏) [ sinkdomOf ! x | x <- suc graph n ]) | y <- nodes graph, Just n <- [nextCond y]]
sinkdomOfGfp graph = domOfGfp graph fSinkDom
mdomOfLfp graph = domOfLfp graph fSinkDom



fSinkDomNaive graph _ _ nextCond toNextCond = f 
  where f sinkdomOf =
                      Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
                    ⊔ Map.fromList [ (y,  (∏) [ sinkdomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]
sinkdomNaiveGfp graph = domOfGfp graph fSinkDomNaive
mdomNaiveLfp graph = domOfLfp graph fSinkDomNaive

sinkdomNaiveGfpFullTop graph = domOfGfpFullTop graph fSinkDomNaive


fSinkDomDual graph _ reachable nextCond toNextCond = f 
  where f sinkdomOfCompl = Map.fromList [ (y, (
                             Set.fromList [ x | x <- nodes graph, x /= y]
                           ⊓ Set.fromList [ x | x <- nodes graph, not $ x ∈ ny]
                           ⊓ ((∐) [ sinkdomOfCompl ! x | Just n <- [nextCond y], x <- suc graph n ])
                           -- ⊓ ( case nextCond y of Just n  -> (∐) [  (sinkdomOfCompl! x) | x <- suc graph n ]
                           --                        Nothing -> allNodes)
                         ) ⊔ Set.fromList  [ x | x <- nodes graph, not $ x ∊ reachable y ]
                        ) | y <- nodes graph, let ny = Set.fromList $ toNextCond y]
        allNodes = Set.fromList $ nodes graph
sinkdomOfLfp graph = fmap (\s -> allNodes ∖ s) $ domOfLfp graph fSinkDomDual
  where allNodes = Set.fromList $ nodes graph

sinkdomOfisinkdomProperty :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOfisinkdomProperty graph =
          Map.fromList [ (y,
                 Set.fromList [ y ]
               ⊔ (∐) [ sinkdom ! z | z <- suc isinkdom y]
            )
          | y <- nodes graph]
  where sinkdom = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()
        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs

isinkdomOfGfp2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkdomOfGfp2 graph = -- fmap (\s -> Set.fromList [ Set.findMin s | not $ Set.null s]) $  (𝝂) init f
                               (𝝂) init f
  where base  =       Map.fromList [ (x, Set.empty )          | x <- nodes graph, (Set.size $ succs x) == 0]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1]
        init  =       base 
                    ⊔ Map.fromList [ (x, Set.fromList [ y | y <- reachable x, y ∊ joinNodes ] )
                                                              | x <- condNodes ]
        f :: Map Node (Set Node) -> Map Node (Set Node)
        f isinkdom = -- traceShow isinkdom $
                     base 
                   ⊔ Map.fromList [ (x, Set.fromList [ z | z <- Set.toList $ isinkdom ! x,
                                                           (∀) (suc graph x) (\y -> z ∊ (suc isinkdomTrc y))
                                                     ]
                                    )
                                  | x <- condNodes]
          where isinkdomTrc = trc $ (fromSuccMap $ isinkdom :: gr () ())
        condNodes = [ x | x <- nodes graph, (Set.size $ succs x) >= 1  ]
        joinNodes = [ x | x <- nodes graph, (Set.size $ preds x) >= 1  ]
        succs x     = Set.delete x $ Set.fromList $ suc graph x
        preds x     = Set.delete x $ Set.fromList $ pre graph x
        reachable x = suc trncl x
        trncl = trc graph

type Successor = (Set Node, Maybe Node)

sinkdomOfJoinUpperBound :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkdomOfJoinUpperBound  graph =
                      (fmap fromJust $ joinUpperBound graph)
                    ⊔ Map.fromList [ (x, Set.empty)           | x <- nodes graph]
                    ⊔ Map.fromList [ (x, succs x)             | x <- nodes graph, (Set.size $ succs x) == 1, not $ x ∈ sinkNodes]
                    ⊔ Map.fromList [ (x, Set.fromList [y])    | (s:sink) <- controlSinks graph, not $ null sink, (x,y) <- zip (s:sink) (sink ++ [s])]
    where succs  x    = Set.delete x $ Set.fromList $ suc graph x
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- controlSinks graph, x <- sink]

joinUpperBound :: forall gr a b. DynGraph gr => gr a b -> Map Node (Maybe (Set Node))
joinUpperBound graph = Map.delete dummyNode $ jub condNodes init
    where jub :: Set Node -> Map Node (Maybe (Set Node)) -> Map Node (Maybe (Set Node))
          jub worklist jubs 
              | Set.null worklist = jubs
              | otherwise         = if (ubX == ubX') then
                                      jub               worklist'                     jubs
                                    else
                                      jub (influenced ⊔ worklist') (Map.insert x ubX' jubs)
            where (x, worklist')  = Set.deleteFindMin worklist
                  successorsX = successors ! x
                  ubX         = jubs ! x
                  ubX'        = case foldr1 join successorsX of
                    (ns, Nothing) -> Just ns
                    _             -> Nothing

                  influenced = Set.fromList $ prevConds x

                  join :: Successor -> Successor -> Successor
                  join (ns, Nothing) (ms, Nothing) = (         ns ⊓ ms        , Nothing)
                  join (ns, Just n)  (ms, Nothing) = case jubs ! n of
                    Just ns' -> ((ns ⊔ ns') ⊓  ms, Nothing)
                    Nothing  -> (              ms, Nothing)
                  join (ns, Nothing) (ms, Just m)  = case jubs ! m of
                    Just ms' -> (       ns  ⊓ (ms ⊔ ms'), Nothing)
                    Nothing  -> (       ns              , Nothing)
                  join (ns, Just n)  (ms, Just m)  = case jubs ! m of
                    Just ms' -> case jubs ! n of
                                 Just ns' -> ( (ns ⊔ ns') ⊓ (ms ⊔ ms'), Nothing)
                                 Nothing  -> (              (ms ⊔ ms'), Nothing)
                    Nothing  -> case jubs ! n of
                                 Just ns' -> ( (ns ⊔ ns')             , Nothing)
                                 Nothing  -> (        (ns ⊔ ms),        Just dummyNode)
          [dummyNode] = newNodes 1 graph
          init = Map.fromList $ [ (x, if not $ List.null deadends then
                                        Just $ (∏) [ ns | (ns, Nothing) <- deadends] 
                                      else
                                        Nothing
                                  )
                                | x <- Set.toList $ condNodes,
                                  not $ x ∈ sinkNodes,
                                  let successorsX  = successors ! x,
                                  let deadends =  [ s | s@(_,Nothing) <- successorsX ]
                                ]
                                ++
                                [ (x, Just $ Set.fromList $ the (x ∊) sinks ) | x <- Set.toList $ condNodes,
                                                                                     x ∈ sinkNodes
                                ]
                                ++
                                [ (dummyNode, Nothing) ]
                                   
          successors :: Map Node [Successor] 
          successors = Map.fromList [ (x, [ (Set.fromList $ toNextCond x',
                                             nextCond x'
                                            ) | x' <- Set.toList $ succs x ] 
                                      ) | x <- Set.toList $ condNodes]

          
          succs  x    = Set.delete x $ Set.fromList $ suc graph x
          preds  x    = Set.delete x $ Set.fromList $ pre graph x
          condNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ succs x) > 1 ]
          joinNodes   = Set.fromList [ x | x <- nodes graph, (Set.size $ preds x) > 1 ]
          sinkNodes   = Set.fromList [ x | x <- nodes graph, sink <- sinks, x <- sink]
          sinks       =  controlSinks graph
          nextCond    = nextRealCondNode graph
          prevConds   = prevRealCondNodes graph
          toNextCond  = toNextRealCondNode graph


mdomOfimdomProperty :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mdomOfimdomProperty graph =
          Map.fromList [ (y,
                 Set.fromList [ y ]
               ⊔ (∐) [ mdom ! z | z <- suc imdom y]
            )
          | y <- nodes graph]
  where mdom = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs

isinkdomOf    graph = immediateOf $ sinkdomOf    graph
isinkdomOfGfp graph = immediateOf $ sinkdomOfGfp graph

imdomOf    graph = immediateOf $ mdomOf    graph
imdomOfLfp graph = immediateOf $ mdomOfLfp graph


imdomOfTwoFinger6 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
imdomOfTwoFinger6 graph = Map.mapWithKey (\n ms -> Set.delete n ms) $
                          fmap toSet $ 
                          twoFinger 0 worklist0 imdom0 imdom0Rev
  where imdom0   =             Map.fromList [ (x, Just z )       | x <- nodes graph, [z] <- [suc graph x], z /= x]
                   `Map.union` Map.fromList [ (x, Nothing)       | x <- nodes graph]
        imdom0Rev = invert''' imdom0
        worklist0   = condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (suc graph x) > 1 ]
        nextCond    = nextCondNode graph
        prevConds   = prevCondNodes graph
        prevCondsImmediate = prevCondImmediateNodes graph

        solution = mdomOfLfp graph
        dom = solution
        doms = domsOf graph dom
        invariant worklist imdom = -- if (True) then True else
                                   -- (if (not inv) then (traceShow (worklist, imdom, imdomWorklist)) else id) $
                                   inv
          where inv =   (∀) (nodes graph) (\n -> (∀) (nodes graph) (\m ->
                                (m ∊ (suc imdomWorklistTrc  n)) ↔ (m ∈ solution ! n)
                        ))
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> (m ∈ solution ! n) ∧ (∀) (solution ! n) (\m' -> m' == n  ∨  (m' ∈ solution ! m))
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> m ∈ doms ! n
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          (isNothing ms  ∧  (∃) (solution ! n) (\m -> m /= n)) → (
                            n ∈ worklistLfp
                          )
                        )
                imdomTrc = trc $ (fromSuccMap (fmap toSet imdom) :: gr () ())
                worklistLfp = (㎲⊒) Set.empty f
                  where f wl = worklist
                             ⊔ Set.fromList [ n | n <- Set.toList condNodes,
                                                  w <- Set.toList wl,
                                                  (∃) (suc graph n) (\y -> reachableFromSeenM imdom y w Set.empty)
                                            ]
                imdomWorklist = fmap toSet imdom
                              ⊔ Map.fromList [ (w, doms ! w) | w <- Set.toList $ worklistLfp ]
                imdomWorklistTrc = trc $ (fromSuccMap  imdomWorklist :: gr () ())

        twoFinger :: Integer -> Set Node ->  Map Node (Maybe Node) ->  Map Node (Set Node) -> Map Node (Maybe Node)
        twoFinger i worklist imdom imdomRev
            | Set.null worklist = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                  -- traceShow (Set.size worklist0, i) $ 
                                  assert (invariant worklist imdom) $
                                  imdom
            | otherwise         = -- traceShow (x, mz, zs, influenced, influencedSlow, worklist, imdom) $
                                  assert (influenced == influencedSlow) $ 
                                  assert (invariant worklist imdom) $
                                  assert (changed → (zs /= Nothing)) $
                                  assert (changed → ( case imdom ! x of { Nothing -> True ; Just _  -> not $ x ∈ reachableFromM imdom (Set.fromList [ z ]) Set.empty })) $
                                  assert (changed → ( case imdom ! x of { Nothing -> True ; Just z0 -> (z0 ∈ reachableFromM imdom (Set.fromList [z ]) Set.empty)
                                                                                                      ∧ ( z ∈ reachableFromM imdom (Set.fromList [z0]) Set.empty) } )) $
                                  if (not $ changed) then twoFinger (i+1)               worklist'                                   imdom                                          imdomRev
                                                     else twoFinger (i+1) (influenced ⊔ worklist')  (Map.insert x zs                imdom) (Map.insertWith (∪) z (Set.singleton x) imdomRev)
          where (x, worklist')  = Set.deleteFindMin worklist
                mz = foldM1 (lca imdom) (suc graph x)
                Just z = zs
                zs = case mz of
                      Just z  -> if z/= x then
                                   Just z
                                 else
                                   Nothing
                      Nothing -> Nothing
                changed = zs /= (imdom ! x)
                influenced = let preds = reachableFrom imdomRev (Set.fromList [x])
                             in Set.fromList $ [ n | n <- foldMap prevCondsImmediate preds,  n /= x]
                influencedSlow = Set.fromList [ n | n <- Set.toList condNodes, n /= x, (∃) (suc graph n) (\y -> reachableFromSeenM imdom y x Set.empty) ]


imdomOfTwoFinger7 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
imdomOfTwoFinger7 graph = Map.mapWithKey (\n ms -> Set.delete n ms) $
                          fmap toSet $ twoFinger 0 workqueue0 Nothing imdom0
  where imdom0   =             Map.fromList [ (x, Just z   ) | x <- nodes graph, [z] <- [suc graph x], z /= x]
                   `Map.union` Map.fromList [ (x, Nothing  ) | x <- nodes graph]
        workqueue0   = Dequeue.fromList $ Set.toList $ condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (suc graph x) > 1 ]
        prevConds   = prevCondNodes graph
        prevCondsImmediate = prevCondImmediateNodes graph
        nextCond    = nextCondNode graph

        solution = mdomOfLfp graph
        dom = solution
        onedom = onedomOf solution
        invariant workqueue imdom = -- if (True) then True else
                                   -- (if (not inv) then (traceShow (worklist, imdom, imdomWorklist)) else id) $
                                   inv
          where worklist = Set.fromList $ Foldable.toList $ workqueue
                inv =   (∀) (nodes graph) (\n -> (∀) (solution ! n) (\m ->
                                (m ∊ (suc imdomWorklistTrc  n))
                        ))
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> (m ∈ solution ! n) ∧ (∀) (solution ! n) (\m' -> m' == n  ∨  (m' ∈ solution ! m))
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          case ms of
                            Nothing -> True
                            Just m  -> (m ∈ onedom n) ∧ (∀) (onedom n) (\m' -> m' ∈ solution ! m)
                        )
                       ∧
                        (∀) (nodes graph) (\n -> let ms = imdom ! n  in
                          (isNothing ms  ∧  (∃) (solution ! n) (\m -> m /= n)) → (
                            n ∈ worklistLfp
                          )
                        )
                imdomTrc = trc $ (fromSuccMap (fmap toSet imdom) :: gr () ())
                worklistLfp = (㎲⊒) Set.empty f
                  where f wl = worklist
                             ⊔ Set.fromList [ n | n <- Set.toList condNodes,
                                                  w <- Set.toList wl,
                                                  p <- nodes graph,
                                                  (w ∈  onedom p ∧ (∀) (onedom p) (\w' -> w' ∈ solution ! w)) ∨ w == p,
                                                  (∃) (suc graph n) (\y -> Just p == nextCond y)
                                            ]
                imdomWorklist = fmap toSet imdom
                              ⊔ Map.fromList [ (w, Set.fromList [ m | m <- Set.toList $ onedom w,
                                                                      (∀) (onedom w) (\m' -> m' ∈ solution ! m)
                                                                ]
                                               )
                                             | w <- Set.toList $ worklistLfp ]
                imdomWorklistTrc = trc $ (fromSuccMap  imdomWorklist :: gr () ())

        twoFinger :: Integer -> SimpleDequeue Node -> Maybe Node -> Map Node (Maybe Node) -> Map Node (Maybe Node)
        twoFinger i worklist oldest imdom 
            |  (Dequeue.null worklist)
             ∨ (Just x == oldest) = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                    -- traceShow (Set.size worklist0, i) $ 
                                    assert (invariant worklist imdom) $
                                    imdom
            | otherwise           = -- traceShow (x, mz, zs, worklist, imdom) $
                                    assert (invariant worklist imdom) $
                                    if (not $ new) then twoFinger (i+1) (pushBack worklist' x) oldest'                    imdom
                                    else                twoFinger (i+1) (         worklist'  ) Nothing  (Map.insert x zs  imdom)
          where Just (x, worklist')  = popFront worklist
                mz = foldM1 (lca imdom) (suc graph x)
                zs = case mz of
                      Just z  -> if z/= x then
                                   Just z
                                 else
                                   Nothing
                      Nothing ->  Nothing
                new     = assert (isNothing $ imdom ! x) $
                          (not $ isNothing zs)
                oldest' = case oldest of
                  Nothing -> Just x
                  _       -> oldest



isinkdomOfTwoFinger8Down :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8Down graph sinkNodes sinks nonSinkCondNodes = twoFingerDown
  where sinkNodesToCanonical = Map.fromList [ (s, s1) | sink <- sinks, let (s1:_) = sink, s <- sink ]
        prevCondsImmediate = prevCondImmediateNodes graph
        twoFingerDown worklist imdom
            | Map.null worklist   = imdom
            | otherwise           = assert (influenced == influencedSlow) $ 
                                    assert ((imdom ! x == Nothing) → (zs == Nothing)) $
                                    if (not $ changed) then twoFingerDown                          worklist'                                   imdom
                                    else                    twoFingerDown  (influenced `Map.union` worklist')  (Map.insert x zs                imdom)
          where ((x, succs), worklist')  = Map.deleteFindMin worklist
                mz = require (succs == suc graph x) $
                     foldM1 (lca imdom) succs
                zs = case mz of
                       Nothing -> Nothing
                       Just z  -> assert (z /= x) $
                                  case Map.lookup z sinkNodesToCanonical of
                                    Just s1 -> Just s1
                                    Nothing -> Just z
                changed = imdom ! x /= zs
                influenced = let imdomRev = invert''' $ imdom
                                 preds = reachableFrom imdomRev (Set.fromList [x])
                             in Map.fromList $ [ (n, succ) | n <- foldMap prevCondsImmediate preds, Just succ <- [Map.lookup n nonSinkCondNodes]]
                influencedSlow = Map.fromList [ (n, succ) | (n, succ) <- Map.assocs nonSinkCondNodes, (∃) succ (\y -> reachableFromSeenM imdom y x Set.empty) ]


isinkdomOfTwoFinger8DownRandomTraversalOrder :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownRandomTraversalOrder graph sinkNodes sinks nonSinkCondNodes = twoFingerDown rs
  where sinkNodesToCanonical = Map.fromList [ (s, s1) | sink <- sinks, let (s1:_) = sink, s <- sink ]
        prevCondsImmediate = prevCondImmediateNodes graph
        rand = mkStdGen 42
        rs = randoms rand
        twoFingerDown rs worklist imdom
            | Map.null worklist   = imdom
            | otherwise           = assert (influenced == influencedSlow) $ 
                                    assert ((imdom ! x == Nothing) → (zs == Nothing)) $
                                    if (not $ changed) then twoFingerDown rs'                         worklist'                                   imdom
                                    else                    twoFingerDown rs' (influenced `Map.union` worklist')  (Map.insert x zs                imdom)
          where (x, succs) = (Map.assocs $ worklist) !! ((abs r) `mod` n)
                  where n = Map.size worklist
                worklist' = Map.delete x worklist
                (r:rs') = rs
                mz = require (succs == suc graph x) $
                     foldM1 (lca imdom) succs
                zs = case mz of
                       Nothing -> Nothing
                       Just z  -> assert (z /= x) $
                                  case Map.lookup z sinkNodesToCanonical of
                                    Just s1 -> Just s1
                                    Nothing -> Just z
                changed = imdom ! x /= zs
                influenced = let imdomRev = invert''' $ imdom
                                 preds = reachableFrom imdomRev (Set.fromList [x])
                             in Map.fromList $ [ (n, succ) | n <- foldMap prevCondsImmediate preds, Just succ <- [Map.lookup n nonSinkCondNodes]]
                influencedSlow = Map.fromList [ (n, succ) | (n, succ) <- Map.assocs nonSinkCondNodes, (∃) succ (\y -> reachableFromSeenM imdom y x Set.empty) ]

isinkdomOfTwoFinger8DownFixedTraversalForOrder :: forall gr a b. (DynGraph gr) =>
     (gr a b -> Set Node -> [[Node]] -> Map Node [Node] -> Map Node (Maybe Node) -> [(Node, [Node])])
  -> gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownFixedTraversalForOrder order graph sinkNodes sinks toConsider imdom0 =
      id
    $ require (Map.fromList workLeft == toConsider)
    $ result
  where result = twoFingerDown workLeft [] imdom0 False

        sinkNodesToCanonical = Map.fromList [ (s, s1) | sink <- sinks, let (s1:_) = sink, s <- sink ]
        workLeft  = order graph sinkNodes sinks toConsider imdom0
        
        twoFingerDown []                       _         imdom False   = imdom
        twoFingerDown []                       workRight imdom True    = twoFingerDown workLeft'  []                          imdom    False
          where workLeft'  = reverse workRight
        twoFingerDown (w@(x, succs):workLeft') workRight imdom changed = twoFingerDown workLeft'  workRight' (Map.insert x zs imdom)  (changed ∨ changed')
          where workRight' = if done then workRight else w:workRight
                mz = require (succs == suc graph x) $
                     foldM1 (lca imdom) succs
                changed' = imdom ! x /= zs
                (zs, done) = case mz of
                       Nothing -> (Nothing, True)
                       Just z  -> assert (z /= x) $
                                  case Map.lookup z sinkNodesToCanonical of
                                    Just s1 -> (Just s1, False)
                                    Nothing -> (Just z, False)


isinkdomOfTwoFinger8DownSingleNodeSinks :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownSingleNodeSinks graph nxs condNodes imdom0 =
      id
    $ require ((∀) nxs (\nx -> imdom0 ! nx == Nothing))
    $ require ((∀) nxs (\nx -> not $ Map.member nx condNodes))
    --   traceShow (workset, worklist, imdom0)
    -- $ traceShow result
    $ result
  where result = twoFingerDown workLeft [] imdom0 False

        workLeft = Map.assocs condNodes

        twoFingerDown []                       _         imdom False   = imdom
        twoFingerDown []                       workRight imdom True    = twoFingerDown workLeft'  []                          imdom    False
          where workLeft'  = reverse workRight
        twoFingerDown (w@(x, succs):workLeft') workRight imdom changed = twoFingerDown workLeft'  workRight' (Map.insert x mz imdom)  (changed ∨ changed')
          where changed' =  mz /= (imdom ! x)
                workRight' = if mz == Nothing then workRight else w:workRight
                  where Just z = mz
                mz = require (succs == suc graph x) $
                     foldM1 lca succs
                lca = lcaSingleNodeSinks imdom nxs



isinkdomOfTwoFinger8DownTreeTraversal :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownTreeTraversal = isinkdomOfTwoFinger8DownFixedTraversalForOrder order
  where order graph sinkNodes sinks toConsider imdom0 = worklist
          where worklist = [ (n, succs) | (n, succs, _) <- sortBy (comparing sucOrder) [ (n, succs, minimum [ treeOrderOf x | x <- succs] ) | (n, succs) <- Map.assocs toConsider ]]
                sucOrder (n, succs, succOrder) = succOrder 
                treeOrderOf n = treeOrder ! n
                  where treeOrder :: Map Node Integer
                        treeOrder = Map.fromList $ zip (Set.toList sinkNodes ++ [ n | n <- treeDfs (fmap maybeToList imdom0) roots]) [0..]
                          where roots = [ n | (n, Just m) <- Map.assocs imdom0, not $ n ∈ sinkNodes, m ∈ sinkNodes]


isinkdomOfTwoFinger8DownFixedTraversal :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Set Node
  -> [[Node]]
  -> Map Node [Node]
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger8DownFixedTraversal = isinkdomOfTwoFinger8DownFixedTraversalForOrder order
  where order graph sinkNodes sinks toConsider imdom0 = Map.assocs toConsider



isinkdomOfTwoFinger8ForSinks :: forall gr a b. (DynGraph gr) => [[Node]] -> Set Node -> Map Node [Node] -> gr a b -> Map Node (Maybe Node)
isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph =
                          require ((Set.fromList sinks) == (Set.fromList $ controlSinks graph))
                        $ require (sinkNodes == (∐) [ Set.fromList sink | sink <- sinks])
                        $ require (nonSinkCondNodes == Map.fromList [ (n, succs) | n <- nodes graph, not $ n ∈ sinkNodes, let succs = suc graph n, length succs > 1 ])
                        $ Map.mapWithKey (\n m -> if m == Just n then Nothing else m)
                        $ imdom''
  where imdom0   =              Map.fromList [ (s1, Just s2)  | (s:sink) <- sinks, sink /= [], (s1,s2) <- zip (s:sink) (sink ++ [s]) ]
                   `Map.union` (Map.fromList [ (x, case suc graph x of { [z] -> assert (z /= x) $ Just z               ; _ -> Nothing  }) | x <- nodes graph, not $ x ∈ sinkNodes ])
                   `Map.union` (Map.fromList [ (x, case suc graph x of { [z] -> if (z /= x) then  Just z else Nothing  ; _ -> Nothing  }) | [x] <- sinks ])
        worklist0 :: SimpleDequeue (Node, [Node])
        worklist0   = Dequeue.fromList $ Map.assocs $ nonSinkCondNodes
--        processed0  = (㎲⊒) sinkNodes (\processed -> processed ⊔ (Set.fromList [ x | x <- nodes graph, [z] <- [suc graph x], z ∈ processed]))
        processed0  = Set.fold f Set.empty sinkNodes
          where f s processed
                    | s ∈ processed = processed
                    | otherwise     = processed'From graph nonSinkCondNodes (Set.fromList [s]) (processed ∪ Set.fromList [s])

--      imdom'  = isinkdomOftwoFinger8UpDfs              graph           sinks                                          imdom0
        imdom'  = isinkdomOftwoFinger8Up                 graph                   nonSinkCondNodes  worklist0 processed0 (invert''' imdom0) imdom0 
        imdom'' = isinkdomOfTwoFinger8DownFixedTraversal graph sinkNodes sinks                    (Map.filterWithKey (\x _ -> imdom' ! x /= Nothing) nonSinkCondNodes) imdom'
--      imdom'' = isinkdomOfTwoFinger8Down               graph sinkNodes sinks   nonSinkCondNodes (Map.filterWithKey (\x _ -> imdom' ! x /= Nothing) nonSinkCondNodes) imdom'
--      imdom'' = isinkdomOfTwoFinger8DownRandomTraversalOrder
--                                                       graph sinkNodes sinks   nonSinkCondNodes (Map.filterWithKey (\x _ -> imdom' ! x /= Nothing) nonSinkCondNodes) imdom'


processed'From  :: Graph gr => gr a b -> Map Node c -> Set Node -> Set Node -> Set Node
{-# INLINE processed'From #-}
processed'From graph nonSinkCondNodes = processed'F
  where processed'F xs processed
            | Set.null xs   = processed
            | otherwise     = processed'F (foldr Set.insert xs' new) (foldr Set.insert processed new)
                where (x, xs') = Set.deleteFindMin xs
                      new      = [ x'| x' <- pre graph x, not $ Map.member x' nonSinkCondNodes, not $ x' ∈ processed]


isinkdomOftwoFinger8Up ::  forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> SimpleDequeue (Node, [Node]) -> Set Node ->  Map Node (Set Node) -> Map Node (Maybe Node) -> Map Node (Maybe Node)
isinkdomOftwoFinger8Up graph nonSinkCondNodes  worklist processed imdomRev imdom =
      require (Map.filter (not . Set.null) imdomRev == invert''' imdom)
    $ twoFinger worklist processed imdom imdomRev
  where -- solution = sinkdomOfGfp graph
        twoFinger worklist processed imdom imdomRev
            | Dequeue.null worklist   = -- traceShow ("x", "mz", "zs", "influenced", worklist, imdom) $
                                    -- traceShow (Set.size worklist0, i) $
                                    {- assert (  (Set.fromList $ edges $ trc $ (fromSuccMap $ fmap toSet imdom :: gr ()()))
                                            ⊇ (Set.fromList $ edges $ trc $ (fromSuccMap $ solution :: gr () ()))) $ this one is true, but too expensive :O -}
                                    imdom
            | otherwise           = -- traceShow (x, worklist', mz, processed', new, imdom) $
                                    assert (imdom ! x == Nothing) $
                                    assert (not $ x ∈ processed) $
                                    if   (not $ new) then twoFinger (pushBack worklist' w)   processed                      imdom                                           imdomRev
                                    else                  twoFinger (         worklist'  )   processed' (Map.insert x mz    imdom) (Map.insertWith (∪) z (Set.fromList [x]) imdomRev)
          where Just (w@(x, succs0), worklist')  = popFront worklist
                processed' = processed ∪ (reachableFrom imdomRev (Set.fromList [x]))
                z = case mz of
                  Nothing -> undefined
                  Just z  -> z
                mz
                  | List.null succs   = Nothing
                  -- | otherwise         = Just $ head $ succs
                  | otherwise  = case foldM1 (lca imdom) succs of
                      Nothing -> Just $ head $ succs
                      Just z  -> Just z
                  where succs    = require (succs0 == (suc graph x)) $
                                   [ y | y <- succs0, y ∈ processed ]
                new     = not $ isNothing mz


isinkdomOftwoFinger8UpDfs ::  forall gr a b. (DynGraph gr) => gr a b -> [[Node]] -> Map Node (Maybe Node) -> Map Node (Maybe Node)
isinkdomOftwoFinger8UpDfs graph sinks idom =
    assert (  (Set.fromList $ edges $ trc $ (fromSuccMap $ fmap toSet idom' :: gr ()()))
           ⊇ (Set.fromList $ edges $ trc $ (fromSuccMap $ solution :: gr () ()))) $
    idom'
  where solution = sinkdomOfGfp graph

        idom' = go [forest] idom

        forest = rdff [ s | (s:_) <- sinks ] graph

        go :: [[Tree Node]] -> Map Node (Maybe Node) -> Map Node (Maybe Node)
        go []                       idom = idom
        go ([]               :ts'') idom = go         ts''  idom
        go (((Node n ts):ts'):ts'') idom = go (ts:ts':ts'') idom'
          where idom' = foldr f idom [ Tree.rootLabel t | t <- ts ]
                f m = Map.insertWith g m (Just n)
                g n  Nothing  = n
                g _        n' = n'



isinkdomOfTwoFinger8 :: forall gr a b. (DynGraph gr) => gr a b -> Map Node (Set Node)
isinkdomOfTwoFinger8 graph = fmap toSet $ isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph
  where sinkNodes   = Set.fromList [ x | sink <- sinks, x <- sink]
        sinks = controlSinks graph
        nonSinkCondNodes = Map.fromList [ (x, succs) | x <- nodes graph, not $ x ∈ sinkNodes, let succs = suc graph x, length succs > 1 ]












{- 
isinkdomOfTwoFinger9DownFixedTraversal :: forall gr a b. (DynGraph gr) =>
     gr a b
  -> Integer
  -> Map Node (Maybe Node)
  -> Map Node (Maybe Node)
isinkdomOfTwoFinger9DownFixedTraversal graph i imdom0 =
      id
    $ result
  where solution = sinkdomOfGfp graph
        result = twoFingerDown i worklist imdom0 False
        worklist = [(n, succs) | n <- nodes graph, let succs = suc graph n]
        
        twoFingerDown i []                     imdom False   = imdom
        twoFingerDown i []                     imdom True    = twoFingerDown  i    worklist                   imdom    False
        twoFingerDown i ((x, succs):worklist') imdom changed = if (not $ expanded ⊒ solution) then traceShow (x, zs, imdom) $ error "rofl" else
                                                               twoFingerDown (i+1) worklist' (Map.insert x zs imdom)  (changed ∨ changed')
          where expanded = toSuccMap $ trc $ (fromSuccMap $ fmap toSet $ Map.insert x zs $ imdom :: gr () ())
                mz = require (succs == suc graph x) $
                     case succs of
                       [] -> Nothing
                       _  -> foldM1 (lca imdom) succs
                changed' = imdom ! x /= zs
                zs = case mz of
                       Nothing -> Nothing
                       Just z  -> assert (z /= x) $
                                  -- if (x ∈ reachableFrom (fmap toSet (Map.insert x (Just z) imdom)) (Set.fromList [z]) (Set.empty)) then imdom ! x else Just z
                                  Just z

        lca imdom n m = let result = lcaDown' (n, Set.fromList [n]) (m, Set.fromList [m]) in result
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


isinkdomOfTwoFinger9 :: forall gr a b. (DynGraph gr) => gr a b -> Map Node (Set Node)
isinkdomOfTwoFinger9 graph
    | List.null $ nodes graph = Map.empty
    | otherwise =         Map.mapWithKey (\n ms -> Set.delete n ms)
                        $ fmap toSet
                        -- $ traceShow (zip starts ends)
                        -- $ traceShow imdomLin'
                        $ isinkdomOfTwoFinger9DownFixedTraversal graph 0 imdom0
  where
        -- imdomLin  =  Map.fromList [ (m, Just m')  | m <- nodes graph, [m'] <- [suc graph m]]
        -- imdomLin' = case starts of
        --              []  -> imdomLin
        --              [s] -> imdomLin
        --              _   -> imdomLin `Map.union` Map.fromList [ (end, Just start)  | (end, start) <- zip ends starts0]
        -- starts = [ m  | m <- Map.keys imdomLin, not $ (∃) (Map.elems imdomLin) (\(Just m') -> m == m') ]
        -- ends   = [ go m | m <- starts ]
        --   where go m = case Map.lookup m imdomLin of
        --                          Nothing        -> m
        --                          Just (Just m') -> go m'
        -- (_:_:starts0) = starts 

        imdom0   =  Map.fromList [ (m, Just m')  | (m,m') <- zip (n:ns) (ns ++ [n]) ]
          where (n:ns) = nodes graph
-}
