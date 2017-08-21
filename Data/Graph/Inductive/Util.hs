module Data.Graph.Inductive.Util where

import Util
import Unicode

import Data.List(delete)

import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Tree as Tree
import Data.Tree (Tree)
import Control.Monad(liftM2,guard)

import Data.Graph.Inductive.Graph hiding (labnfilter) -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Query.DFS (scc, condensation, dff')
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Tree

-- adapted from from https://hackage.haskell.org/package/gbu-0.1/
mergeTwoGraphs :: DynGraph gr => gr a b -> gr a b -> gr a b
mergeTwoGraphs g1 g2 = foldr insEdge g1' $ labEdges g2
 where g1' = foldr mergeNode g1 $ labNodes g2
       mergeNode (n,a) g =
         if n `gelem` g1 then g
                         else insNode (n,a) g



relabelingWrt :: (Graph gr, Graph gr') => gr a b -> gr' c d -> (Node -> Node)
relabelingWrt g1 g2 n1
    | isEmpty g1 || isEmpty g2 || max2 < min1 || max1 < min2 = n1
    | otherwise                                = n1 + (max2 - min1) + 1
  where (min1,max1) = nodeRange g1
        (min2,max2) = nodeRange g2

relabeledWrt :: (Graph gr, Graph gr', Graph gr'') => gr a b -> gr' a b -> gr'' a b
g1 `relabeledWrt` g2 = mkGraph  [(newId n, a) | (n,a) <- labNodes g1] [(newId n, newId n', e) | (n,n',e) <- labEdges g1]
 where newId = relabelingWrt g1 g2

-- | Returns the subgraph only containing the nodes which satisfy the
-- given predicate.
nfilter :: Graph gr => (Node -> Bool) -> gr a b -> gr a b
nfilter f = labnfilter (f . fst)


-- | Returns the subgraph only containing the labelled nodes which
-- satisfy the given predicate.
labnfilter :: Graph gr => (LNode a -> Bool) -> gr a b -> gr a b
labnfilter p gr = delNodes (map fst . filter (not . p) $ labNodes gr) gr


isInCycle :: Graph gr => gr a b -> Node -> Bool
isInCycle graph node = length component > 1
  where component = the (node `elem`) $ scc graph


isInCycleMap :: Graph gr => gr a b -> Map Node Bool
isInCycleMap graph  = Map.fromList [ (n, True)  | c@(_:ns) <- sccs, not $ null ns, n <- c ]
          `Map.union` Map.fromList [ (n, False) | [n] <- sccs]
  where sccs = scc graph


notInCycleSet :: Graph gr => gr a b -> Set Node
notInCycleSet graph  = Set.fromList [ n | [n] <- sccs]
  where sccs = scc graph


-- | The condensation of the given graph by equivalence classes
-- adapted from Data.Graph.Inductive.Query.DFS.condensation
eqGraph :: Graph gr => [[Node]] -> gr a b -> gr [Node] ()
eqGraph classes gr = mkGraph vs es
  where
    vs = zip [1..] classes
    vMap = Map.fromList $ map swap vs

    swap = uncurry $ flip (,)

    getN = (vMap Map.!)
    es = [ (getN c1, getN c2, ()) | c1 <- classes, c2 <- classes
                                  , (c1 /= c2) && any (hasEdge gr) (liftM2 (,) c1 c2) ]


-- via http://dx.doi.org/10.1016/0167-6423(89)90039-7
trrAcyclic :: DynGraph gr => gr a () -> gr a ()
trrAcyclic graph = trrAcyclicCurrent closure (nodes graph)
  where closure = delEdges [(n,n) | n <- nodes graph] $ trc graph
        trrAcyclicCurrent g []     = g
        trrAcyclicCurrent g (k:ks) =
            trrAcyclicCurrent (delEdges [(i,j) | i <- pre g k,
                                                 j <- suc g k
                                        ]
                                        g
                              )
                              ks


trr :: DynGraph gr => gr a () -> gr a ()
trr g =
    mkGraph (labNodes g)
            (    [(n, n', ())           | (_,e) <- labNodes g1t, (n,n') <- zip e (tail e)]
              ++ [(last e, head e,  ()) | (_,e) <- labNodes g1t, length e > 1            ]
              ++ [(head e, head e', ()) | (m,m') <- edges g1t, let (Just e, Just e') = (lab g1 m, lab g1 m') ]
            )
  where g1   = condensation g
        g1t  = trrAcyclic g1


trcOfTrrIsTrc ::  Gr String () -> Bool
trcOfTrrIsTrc g = trc g == (trc $ trr g)


fromPredMap :: DynGraph gr => Map Node (Set Node) -> gr () () 
fromPredMap pred = mkGraph [(n,()) | n <- Map.keys pred]
                           [(m,n,()) | (n,ms) <- Map.assocs pred, m <- Set.toList ms]

fromSuccMap :: DynGraph gr => Map Node (Set Node) -> gr () () 
fromSuccMap succ = mkGraph [(n,()) | n <- Map.keys succ]
                           [(n,m,()) | (n,ms) <- Map.assocs succ, m <- Set.toList ms]

toPredMap ::  Graph gr => gr a b -> Map Node (Set Node)
toPredMap gr = Map.fromList [(n, Set.fromList $ pre gr n ) | n <- nodes gr]


fromSuccMapWithEdgeAnnotation :: DynGraph gr => Map Node (Set (Node,b)) -> gr () b
fromSuccMapWithEdgeAnnotation succ = mkGraph [(n,()) | n <- Map.keys succ]
                                             [(n,m,b) | (n,ps) <- Map.assocs succ, (m,b) <- Set.toList ps]



fromSuccPairMap :: DynGraph gr => Map Node (Set (Node,Node)) -> gr () () 
fromSuccPairMap succ = mkGraph [(n,()) | n <- Map.keys succ]
                               [(n,m,()) | (n,ps) <- Map.assocs succ, m <- (fmap fst $ Set.toList ps) ++ (fmap snd $ Set.toList ps)]


trrAcyclicPredMap :: Map Node (Set Node) -> Map Node (Set Node)
trrAcyclicPredMap pred = toPredMap $ trrAcyclic $ (fromPredMap pred :: Gr () ())

enumCycles :: (Graph gr) => gr a b -> [[Node]]
enumCycles gr = do
    c <- sccs
    n <- c
    cycles gr [n] c n
  where sccs = scc gr

cycles :: (Graph gr) => gr a b -> [Node] -> [Node] -> Node -> [[Node]]
cycles gr (p:path) [] end = do
      guard $ end `elem` (pre gr p)
      return (p:path)
cycles gr (p:path) ns end = do
        n <- ns
        guard $ n `elem` (pre gr p)
        if (n == end) then
          return (n:p:path)
        else do
          cycles gr (n:p:path) (delete n ns) end

addUniqueEndNode :: DynGraph gr => a -> b -> gr a b -> (Node, gr a b)
addUniqueEndNode endLabel endEdgeLabel gr = (end,
        foldr (\n g -> insEdge (n, end, endEdgeLabel) g)
              (insNode (end, endLabel) gr)
              [ n | scc <- sccs, isEndScc scc, let n = head scc ]
      )
    where sccs = scc gr
          [end] = newNodes 1 gr
          isEndScc scc = (∀) scc (\n -> (∀) (suc gr n) (\n' -> n' `elem` scc))


uniqueEndNodes :: DynGraph gr => gr a b -> [Node]
uniqueEndNodes gr = [ n | n <- nodes gr, (∀) (nodes gr) (\m -> n `elem` suc trncl m), suc gr n == []]
    where trncl = trc gr

withUniqueEndNode :: DynGraph gr => a -> b -> gr a b -> (Node, gr a b)
withUniqueEndNode endLabel endEdgeLabel gr =
    case uniqueEndNodes gr of
      []    -> addUniqueEndNode endLabel endEdgeLabel gr
      [end] -> (end, gr)
      _     -> error "cannot happen: there cannot be multiple unique nodes"



postorder :: Graph gr => gr a b -> (Map Node Integer, Map Integer Node)
postorder g = (Map.fromList $ zip po [0..],
               Map.fromList $ zip [0..] po)
  where po = (postorderF $ dff' g)
{-
postorder g = Map.fromList $ postorderTs 0 dftree
  where dftree = dff' g
        postorderTs :: Integer -> [Tree Node] -> [(Node, Integer)]
        postorderTs n [] = []
        postorderTs n (t:ts) = foldr f first ts
          where first@((m,p):mps) = postorderT n t
                f t ((m,p):mps) = (postorderT (p+1) t) ++ ((m,p) : mps)
        postorderT :: Integer -> Tree Node -> [(Node, Integer)]
        postorderT n (Tree.Node x []) = [(x,n)]
        postorderT n (Tree.Node x ts) = (x, p+1) : (m,p) : mps
          where (m,p):mps = postorderTs n ts
-}
