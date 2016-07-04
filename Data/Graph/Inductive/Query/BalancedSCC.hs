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



-- balancedScc :: DynGraph gr => gr a (Annotation b) -> Map Node [Node]
-- balancedScc gr = scc (nodes gr) (labEdges gr) (Map.fromList $ [(n,[n]) | n <- nodes gr]) []
--   where sameLevel = sameLevelNodes gr
--         scc uedges sccs []              = sccs
--         scc uedges@((n,m,_):es) sccs [] = scc uedges sccs [n]
--         scc uedges sccs []              = scc (u:us) uedges sccs [(u,c)]
--         scc uedges sccs path@(n:ns) (c:cs) = -- trace ((show path) ++ "\t\t" ++ (show sccs)) $
--          case es of
--           []                  -> scc uedges sccs ns cs
--           ((n',m,Nothing      ):_) ->    if (any (m `elem`) (fmap sccOf path)) then
--                                            scc (delete (n',m,c) uedges) (merge sccs (m:cycle)) prefix   (c:c:cs)
--                                          else
--                                            scc (delete (n',m,c) uedges)  sccs                  (m:path) (c:c:cs)
--             where (cycle, prefix) = span (\n -> not $ m `elem` (sccOf n)) path
--           ((n',m,Just (Open a)):_) -> let ms = sameLevel (
--                                          if (any (m `elem`) (fmap sccOf path)) then
--                                            scc (delete (n',m,c) uedges) (merge sccs (m:cycle)) prefix   (a:c:cs)
--                                          else
--                                            scc (delete (n',m,c) uedges)  sccs                  (m:path)
--             where (cycle, prefix) = span (\n -> not $ m `elem` (sccOf n)) path
--           ((n',m,Just (Close a)):ms) ->   if (any (m `elem`) (fmap sccOf path)) then
--                                            scc (delete (n',m,c) uedges) (merge sccs (m:cycle)) prefix
--                                          else
--                                            scc  (delete (n',m,c) uedges)  sccs                  (m:path)
--             where (cycle, prefix) = span (\n -> not $ m `elem` (sccOf n)) path
--          where es = [ (n',m) | n' <- sccOf n,
--                                (m,ann) <- lsuc gr n',
--                                ((n',m),c) `elem` uedges,
--                                 case ann of
--                                   Just (Close x) -> c == Just x
--                                   _              -> True
--                     ]
--                sccOf m =  sccs ! m
--                merge sccs cycle =
--                c = listToMaybe stack


sccIsSccNaive :: Gr () () -> Bool
sccIsSccNaive gr = sccs == sccsNaive
  where sccs      = Set.fromList $ (fmap Set.fromList $ scc gr)
        sccsNaive = Set.fromList $ (fmap Set.fromList $ sccNaive gr)



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
