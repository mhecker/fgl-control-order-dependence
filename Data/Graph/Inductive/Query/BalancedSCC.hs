module Data.Graph.Inductive.Query.BalancedSCC where



import Debug.Trace
import Util

import Algebra.Lattice

import Unicode

import Data.Maybe(fromJust)

import Data.List(union, intersect, elem, delete, sort)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.DFS

import Test.QuickCheck

import Data.Graph.Inductive.Arbitrary

data Parantheses b = Open b | Close b deriving (Ord, Eq)
type Annotation b = Maybe (Parantheses b)

merge :: [[Node]] -> [Node] -> [[Node]]
merge [] cycle = [cycle]
merge (c:cs) cycle
  | c `intersect` cycle == [] = c:(merge cs cycle)
  | otherwise                 = merge cs (c `union` cycle)

sccNaive :: DynGraph gr => gr a b -> [[Node]]
sccNaive gr = scc (edges gr) [[n] | n <- nodes gr] []
  where scc []                sccs []          = sccs
        scc uedges@((n,m):es) sccs []          = scc uedges sccs [n]
        scc uedges            sccs path@(n:ns) = -- trace ((show path) ++ "\t\t" ++ (show sccs)) $
         case es of
          []          -> scc uedges sccs ns
          ((n',m):_) -> if (any (m `elem`) (fmap sccOf path)) then
                           scc (delete (n',m) uedges) (merge sccs (m:cycle)) prefix
                         else
                           scc (delete (n',m) uedges)  sccs                  (m:path)
            where (cycle, prefix) = span (\n -> not $ m `elem` (sccOf n)) path
         where es = [ (n',m) | n' <- sccOf n, m <- suc gr n', (n',m) `elem` uedges ]
               sccOf m =  the (m `elem`) $ sccs



balancedScc :: DynGraph gr => gr a (Set Node) -> Map Node (Set Node)
balancedScc gr = scc (labEdges gr) (Map.fromList $ [(n,Set.fromList [n]) | n <- nodes gr]) []
  where scc :: [(Node,Node,Set Node)] -> Map Node (Set Node) -> [(Node, Set Node)] -> Map Node (Set Node)
        scc []                  sccs []               = sccs
        scc uedges@((n,m,_):es) sccs []               = scc uedges sccs [(n,Set.empty)]
        scc uedges              sccs path@((n,_):ns)  = -- trace ((show path) ++ "\t\t" ++ (show sccs)) $
         case es of
          []                  -> scc uedges sccs ns
          ((n',m,summ):_) ->   if (any (m ∈) ( [ sccOf n ⊔ summN | (n,summN) <- path] ++ [summ])) then
                                 scc (delete (n',m,summ) uedges) (merge sccs ((m,summ):cycle)) prefix
                               else
                                 scc (delete (n',m,summ) uedges)  sccs                         ((m,summ):path)
            where (cycle, prefix) = span (\(n,summ) -> not $ (m ∈) (sccOf n ⊔ summ)) path
         where es :: [(Node,Node,Set Node)]
               es = [ (n',m,summ) | n' <- Set.toList $ sccOf n, (m,summ) <- lsuc gr n', (n',m,summ) `elem` uedges ]
               sccOf m =  sccs ! m
               merge sccs cycle = -- trace ("Merge: " ++ ((show cycle) ++ "\t\t" ++ (show sccs))) $
                                  sccs ⊔ (Map.fromList [ (n, (∐) [ sccs ! n' | (c,summ) <- cycle, n' <- c : (Set.toList summ) ])
                                                       | (c,summ) <- cycle, m <- c : (Set.toList summ), n <- Set.toList (sccs ! m)
                                                       ])


toBalanced :: (Graph gr) => gr a b -> gr a (Annotation ())
toBalanced gr = mkGraph (labNodes gr) [ (n,m,Nothing) | (m,n) <- edges gr]

sccIsSccNaive :: Gr () () -> Bool
sccIsSccNaive gr = sccs == sccsNaive
  where sccs      = Set.fromList $ (fmap Set.fromList $ scc gr)
        sccsNaive = Set.fromList $ (fmap Set.fromList $ sccNaive gr)


sccIsBalancedSccNaive :: Gr () () -> Bool
sccIsBalancedSccNaive gr = sccs == sccsNaive
  where sccs      = Set.fromList $ (fmap Set.fromList $ scc gr)
        sccsNaive = Set.fromList $ [ balancedSccs ! n | n <- nodes $ gr]
        balancedSccs = balancedScc $ sameLevelSummaryGraph $ toBalanced $ gr



proceduresIn gr = Set.fromList $ [ b | (_,_,Just (Open b)) <- labEdges gr] ++
                                 [ b | (_,_,Just (Close b)) <- labEdges gr]


sameLvlNodes gr = 
    (㎲⊒) (Map.fromList [ ((n,m,b),Set.empty) | (_,n,Just (Open  b )) <- labEdges gr,
                                                (m,_,Just (Close b')) <- labEdges gr, b == b'
                        ],
           Map.fromList [ ((n,m,b),Set.empty) | (_,n,Just (Open  b )) <- labEdges gr, m <- nodes gr ]
          )
          (\(sameLevel, onLevel) -> (
            sameLevel ⊔ (onLevel `restrict` (Map.keys sameLevel)),
            onLevel   ⊔ Map.fromList [ ((n,n,b),  Set.fromList [n]) | (_,n,Just (Open  b )) <- labEdges gr]
                      ⊔ Map.fromList [ ((n,n',b), (∐) [ Set.fromList [n'] ⊔  onLevel ! (n,m,b) | m <- [ m | (m, Nothing) <- lpre gr n'], not $ Set.null $ onLevel ! (n,m,b)])
                                     |  (n,n',b) <- Map.keys onLevel
                                     ]
                      ⊔ Map.fromList [ ((n,n',c), (∐) [ sameLevel ! (m,m',b) | (m',  Just (Close b)) <- lpre gr n',
                                                                               (_,m, Just (Open b')) <- labEdges gr, b' == b
                                                      ]
                                       )
                                     | (n,n',c) <- Map.keys onLevel
                                     ]
                      ⊔ Map.fromList [ ((n,n',c), (∐) [ Set.fromList [n'] ⊔ onLevel ! (n,m,c) | (m',  Just (Close b)) <- lpre gr n',
                                                                                                 (m,_, Just (Open b')) <- labEdges gr, b' == b,
                                                                                                 not $ Set.null $ onLevel ! (n,m,c)
                                                      ]
                                       )
                                     | (n,n',c) <- Map.keys onLevel
                                     ]
            )
          )

sameLevelNodes :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node,b) (Set Node)
sameLevelNodes = fst . sameLvlNodes

sameLevelSummaryGraph :: (Graph gr, Ord b) => gr a (Annotation b) -> gr a (Set Node)
sameLevelSummaryGraph gr =
    mkGraph (labNodes gr)
            ( [(n,m,Set.empty) | (n,m,Nothing) <- labEdges gr] ++
--              [(n,m,Set.empty) | (n,m, Just (Close _))) <- labEdges gr] ++
              [(n,n', sameLevel ! (m, m', b)) | n <- nodes gr, n' <- nodes gr,
                                                (m',  Just (Close b)) <- lpre gr n',
                                                (m,   Just (Open b')) <- lsuc gr n, b' == b
              ]
            )
  where sameLevel = sameLevelNodes gr


sameLevelSummaryGraphNodeAnnotated :: (Graph gr, Ord b) => gr a (Annotation b) -> gr Node (Set Node)
sameLevelSummaryGraphNodeAnnotated gr =
    mkGraph ( [(n,n) | n <- nodes gr])
            ( [(n,m,Set.empty) | (n,m,Nothing) <- labEdges gr] ++
              [(n,n', sameLevel ! (m, m', b)) | n <- nodes gr, n' <- nodes gr,
                                                (m',  Just (Close b)) <- lpre gr n',
                                                (m,   Just (Open b')) <- lsuc gr n, b' == b
              ]
            )
  where sameLevel = sameLevelNodes gr


graphTest :: Gr () (Annotation String)
graphTest = mkGraph [ (i,()) | i <- [0..7]]
                    [ (0,1, Just $ Open "main"),
                      (1,2, Just $ Open "l"),
                      (2,3, Nothing),
                      (3,4, Just $ Close "l"),
                      (4,5, Nothing),
                      (5,2, Just $ Open "r"),
                      (3,6, Just $ Close "r"),
                      (6,5, Nothing),
                      (6,7, Just $ Close "main")
                    ]

graphTest2 :: Gr () (Annotation String)
graphTest2 =
    mkGraph [ (i,()) | i <- [0..8]]
            [ (0,1, Just $ Open "main"),
              (1,2, Just $ Open "l"),
              (2,3, Nothing),
              (3,1, Just $ Open "r"),
              (4,5, Nothing),
              (5,6, Just $ Close "r"),
              (6,7, Nothing),
              (7,4, Just $ Close "l"),
              (2,7, Nothing),
              (5,8, Just $ Close "main")
            ]

-- balancedScc :: DynGraph gr => gr a (Annotation b) -> Map Node [Node]
-- balancedScc :: bscc parenstack sccsOf unvisited 

--   w
