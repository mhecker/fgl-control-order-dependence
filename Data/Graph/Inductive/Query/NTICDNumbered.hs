module Data.Graph.Inductive.Query.NTICDNumbered where


-- Find Dominators of a graph.
--
-- Author: Bertram Felgenhauer <int-e@gmx.de>
-- Author: Martin Hecker <martin.hecker@kit.edu>


import           Data.Array
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Query.DFS
import           Data.IntMap                    (IntMap)
import qualified Data.IntMap                    as I
import           Data.Tree                      (Tree (..))
import qualified Data.Tree                      as T

import Debug.Trace

import Data.Graph.Inductive.Query.NTICD (controlSinks)


{-# ANN iPDom "HLint: ignore Use ***" #-}
-- | return immediate post-dominators for each node of a graph
iPDom :: (Graph gr) => gr a b -> [(Node,Maybe Node)]
iPDom g = iPDomForSinks sinks g
  where sinks = controlSinks g

-- | return immediate post-dominators for each node of a graph, given its sinks
iPDomForSinks :: (Graph gr) => [[Node]] -> gr a b -> [(Node,Maybe Node)]
iPDomForSinks sinks g = let (result, toNode, _) = idomWork g sinks
                in  map (\(a, b) -> (toNode ! a, toNode `at` b)) (assocs result)

at toNode x = if x == nothing then Nothing else Just $ toNode ! x

-- | return the set of post-dominators of the nodes of a graph
pdom :: (Graph gr) => gr a b ->  [(Node,[Node])]
pdom g = pdomForSinks sinks g
  where sinks = controlSinks g


-- | return the set of post-dominators of the nodes of a graph, given its sinks
pdomForSinks :: (Graph gr) => [[Node ]] -> gr a b -> [(Node,[Node])]
pdomForSinks sinks g = let
    (iD, toNode, fromNode) = idomWork g sinks
    dom' = getDom fromNode toNode sinks iD
    nodes' = nodes g
  in
    [(toNode ! i, dom' ! i) | i <- range (bounds dom'), i /= nothing]

-- internal node type
type Node' = Int
-- array containing the immediate dominator of each node, or an approximation
-- thereof. the dominance set of a node can be found by taking the union of
-- {node} and the dominance set of its immediate dominator.
type IPDom = Array Node' Node'
-- array containing the list of predecessors of each node
type Succs = Array Node' [Node']
-- array containing the canonical representative (== itself for non-sink-nodes) of each node
type ToCanonical = Array Node' Node' 
-- arrays for translating internal nodes back to graph nodes and back
type ToNode = Array Node' Node
type FromNode = IntMap Node'

idomWork :: (Graph gr) => gr a b -> [[Node]] -> (IPDom, ToNode, FromNode)
idomWork g sinks = let
    -- use depth first tree from root do build the first approximation
    tree = Node undefined $ rdff [ s| (s:_) <- sinks] g
    -- relabel the tree so that paths from the root have increasing nodes
    (s, ntree) = numberTree 0 tree
    -- sink nodes must be given a fixed idom s.t. node from the same sink form a cycle
    sinkSuccs = [ (fromNode I.! s1, fromNode I.! s2) | (s:sink) <- sinks, sink /= [], (s1,s2) <- zip (s:sink) (sink ++ [s]) ]
    -- the approximation iPDom0 just maps each node to its parent
    iPD0 = array (1, s-1) (tail $ treeEdges (-1) ntree)   // sinkSuccs
    -- in order to preserve sink-cycles in idom, chose a canonical representative for each sink
    toCanonical = array (1, s-1)  [(i,i) | i <- [1..s-1]] // [ (fromNode I.! s', fromNode I.! s ) | (s:sink) <- sinks, s' <- (s:sink) ]
    -- fromNode translates graph nodes to relabeled (internal) nodes
    fromNode = I.unionWith const  (I.fromList (zip (tail $ T.flatten tree) (tail $ T.flatten ntree))) (I.fromList (zip (nodes g) (repeat (-1))))
    -- toNode translates internal nodes to graph nodes
    toNode = array (1, s-1) (zip (tail $ T.flatten ntree) (tail $ T.flatten tree))
    --  in order to preserve sink-cycles in idom, override successors for sink nodes with their idom-successor
    succs  = array (1, s-1) [(i, filter (\i' -> i' /= -1  && i' /= i) (map (fromNode I.!) (suc g (toNode ! i)))) | i <- [1..s-1]] // fmap (\(n,x) -> (n,[x])) sinkSuccs
    -- iteratively improve the approximation to find iDom.
    iD = fixEq (refineIDom toCanonical toNode succs) iPD0
    
  in if null tree then error "Dominators.idomWork: root not in graph"
                  else (iD, toNode, fromNode)




-- for each node in iDom, find the intersection of all its predecessor's
-- dominating sets, and update iDom accordingly.
refineIDom :: ToCanonical -> ToNode -> Succs -> IPDom -> IPDom
refineIDom toCanonical toNode preds iD = {- traceShow (  map (\(a, b) -> (toNode ! a, toNode `at` b)) (assocs iD)) $ -} traceShow iD $ fmap f preds
  where f []  = nothing
        f [x] = x
        f ps = foldl1 (intersect toCanonical toNode iD) ps

nothing :: Node'
nothing = 0

-- find the intersection of the two given dominance sets.
intersect ::  ToCanonical -> ToNode -> IPDom -> Node' -> Node' -> Node'
intersect toCanonical toNode iD a b
  | a == nothing  || b == nothing = nothing
  | otherwise = traceShow (a, b) $ case a `compare` b of
    LT -> let b' = (iD ! b) in if (b' >= b) then lin toCanonical iD b a else intersect toCanonical toNode iD  a  b'
    EQ -> toCanonical ! a
    GT -> let a' = (iD ! a) in if (a' >= a) then lin toCanonical iD a b else intersect toCanonical toNode iD  a' b

lin toCanonical iD min x
 | x == nothing = nothing
 | otherwise = traceShow (min, x) $ case min `compare` x of
     LT -> let x' = (iD ! x) in if (x' >= x) then nothing else lin toCanonical iD min x'
     EQ -> toCanonical ! x
     GT -> nothing

-- convert an IDom to dominance sets. we translate to graph nodes here
-- because mapping later would be more expensive and lose sharing.
getDom :: FromNode -> ToNode -> [[Node]] -> IPDom -> Array Node' [Node]
getDom fromNode toNode sinks iD = let
    sinknodes = concat sinks
    res = array
            (0, snd (bounds iD))
            ((nothing, []) : [(fromNode I.! s, sink) | sink <- sinks, s <- sink]  ++  [(i, n : res ! (iD ! i)) | i <- range (bounds iD), let n = toNode ! i, not $ n `elem` sinknodes ])
  in
    res

-- relabel tree, labeling vertices with consecutive numbers in depth first order
numberTree :: Node' -> Tree a -> (Node', Tree Node')
numberTree n (Node _ ts) = let (n', ts') = numberForest (n+1) ts
                           in  (n', Node n ts')

-- same as numberTree, for forests.
numberForest :: Node' -> [Tree a] -> (Node', [Tree Node'])
numberForest n []     = (n, [])
numberForest n (t:ts) = let (n', t')   = numberTree n t
                            (n'', ts') = numberForest n' ts
                        in  (n'', t':ts')

-- return the edges of the tree, with an added dummy root node.
treeEdges :: a -> Tree a -> [(a,a)]
treeEdges a (Node b ts) = (b,a) : concatMap (treeEdges b) ts

-- find a fixed point of f, iteratively
fixEq :: (Eq a) => (a -> a) -> a -> a
fixEq f v | v' == v   = v
          | otherwise = fixEq f v'
    where v' = f v

{-
:m +Data.Graph.Inductive
let g0 = mkGraph [(i,()) | i <- [0..4]] [(a,b,()) | (a,b) <- [(0,1),(1,2),(0,3),(3,2),(4,0)]] :: Gr () ()
let g1 = mkGraph [(i,()) | i <- [0..4]] [(a,b,()) | (a,b) <- [(0,1),(1,2),(2,3),(1,3),(3,4)]] :: Gr () ()
let g2,g3,g4 :: Int -> Gr () (); g2 n = mkGraph [(i,()) | i <- [0..n-1]] ([(a,a+1,()) | a <- [0..n-2]] ++ [(a,a+2,()) | a <- [0..n-3]]); g3 n =mkGraph [(i,()) | i <- [0..n-1]] ([(a,a+2,()) | a <- [0..n-3]] ++ [(a,a+1,()) | a <- [0..n-2]]); g4 n =mkGraph [(i,()) | i <- [0..n-1]] ([(a+2,a,()) | a <- [0..n-3]] ++ [(a+1,a,()) | a <- [0..n-2]])
:m -Data.Graph.Inductive
-}

