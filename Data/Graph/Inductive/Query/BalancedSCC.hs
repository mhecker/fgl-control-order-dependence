{-# LANGUAGE FlexibleInstances, ScopedTypeVariables #-}

module Data.Graph.Inductive.Query.BalancedSCC where
import Data.Time

import Debug.Trace
import Util

import Algebra.Lattice hiding (gfpFrom)
import Algebra.PartialOrd (gfpFrom)

import Unicode

import Data.Maybe(fromJust)

import Data.List(union, intersect, elem, delete, sort, (\\), nub)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Query.Dominators (dom, iDom)

import Program.CDom (inclChop)

import Test.QuickCheck
import Test.QuickCheck.Random (mkQCGen)
import Test.QuickCheck.Gen (Gen(MkGen))

import Data.Graph.Inductive.Arbitrary

data Parantheses b = Open b | Close b deriving (Ord, Eq, Show)
type Annotation b = Maybe (Parantheses b)

data   InterGraph a b = InterGraph (Gr a (Annotation b)) deriving (Show)
data   InterCFG   a b = InterCFG Node (Gr a (Annotation b)) deriving (Show)

instance Arbitrary (Parantheses String) where
    arbitrary = sized $ \n ->
                  do p <- elements ["a", "b", "c"]
                     oc <- elements [Open, Close]
                     return $ oc p

instance Arbitrary (InterGraph () String) where
  arbitrary = sized $ \size ->
                 do (g :: Gr () ()) <- resize size arbitrary
                    edges <- mapM (\(n,n',()) ->
                      do (oc :: Maybe (Parantheses String)) <- resize size arbitrary
                         return (n,n',oc)
                     ) (labEdges g)
                    return $ InterGraph $ mkGraph (labNodes g) edges


-- instance Arbitrary (InterCFG () String) where
--   arbitrary = sized $ \size ->
--                  do (CG s g :: Connected Gr () ()) <- resize size arbitrary
--                     edges <- mapM (\(n,n',()) ->
--                       do (oc :: Maybe (Parantheses String)) <- resize size arbitrary
--                          return (n,n',oc)
--                      ) (labEdges g)
--                     return $ InterCFG s $ mkGraph (labNodes g) edges


instance Arbitrary (InterCFG () String) where
    arbitrary = sized $ \size ->
                  do (s,t,p) <- genProc size
                     addProcedures [(InterCFG s p,t)] (size `div` 5) (size `div` 2) size
      where
        genProc :: Int -> Gen (Node, Node, Gr () (Annotation String))
        genProc size =
            do (CG s p  :: Connected Gr () ()) <- resize size arbitrary
               t <- elements (nodes p)
               let p' =   delEdges [(t,n) | n <- suc p t]
                        $ emap (\() -> Nothing) p
               return (s,t, subgraph (inclChop p' s t) p')
        
        addProcedures :: [(InterCFG () String,Node)] -> Int -> Int -> Int -> Gen (InterCFG () String)
        addProcedures ps 0 nrCalls size = addCalls nrCalls  merged sts
                 where (merged, sts) =
                                foldr (\(InterCFG s p,t) (gr,sts) ->
                                                               let relabeling = p `relabelingWrt` gr
                                                                   (s',t') = (relabeling s, relabeling t)
                                                                   p' = p `relabeledWrt` gr
                                                                   gr' = p' `mergeTwoGraphs` gr
                                                                   (n,m) = (head $ nodes p', last $ nodes p') -- TODO: choose random
                                                                   (ssuc,tsuc) = head sts
                                                                   gr'' = if (not $ all (`elem` nodes gr') [n,ssuc,tsuc,m]) then error (show ([n,ssuc,tsuc,t], gr', p')) else
                                                                            insEdge (n,ssuc, Just $ Open (show (n,ssuc)))
                                                                          $ insEdge (tsuc,m, Just $ Close (show (n,ssuc)))
                                                                          $ gr'
                                                               in (gr'', (s',t'):sts)
                                      )
                                      (mkGraph [(1,())] [] :: Gr () (Annotation String),
                                       [(1,1)]
                                      )
                                      ps
        addProcedures ps nrProcs nrCalls size = do (s,t,p) <- genProc size
                                                   addProcedures ((InterCFG s p,t):ps) (nrProcs-1)  nrCalls size
        
        addCalls :: Int -> (Gr () (Annotation String)) -> [(Node,Node)] ->  Gen (InterCFG () String)
        addCalls 0       gr sts = addMain gr s t 
          where (s,t):_ = sts
        addCalls nrCalls gr sts
            | null candidates = addCalls 0 gr sts
            | otherwise = do e@(n,m,Nothing) <- elements candidates
                             (s,t) <- elements sts
                             let gr' =   insEdge (n,s, Just $ Open (show (n,s)))
                                       $ insEdge (t,m, Just $ Close (show (n,s)))
                                       $ delLEdge e
                                       $ gr
                             addCalls (nrCalls-1) gr' sts
          where candidates = [(n,m,Nothing) | (n,m,Nothing) <- labEdges gr, not $ n `elem` ((fmap fst sts) ++ (fmap snd sts)),
                                                                            not $ m `elem` ((fmap fst sts) ++ (fmap snd sts))
                             ]
        
        
        addMain gr s t =  return $ InterCFG ms $
                            insEdge (ms,s,  Just $ Open (show (ms,s)))
                          $ insEdge (t,mt, Just $ Close (show (ms,s)))
                          $ insNodes [(ms,()), (mt,())]
                          $ gr
          where [ms,mt] = newNodes 2 gr


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




sameLevelScc :: DynGraph gr => gr a (Set Node) -> Map Node (Set Node)
sameLevelScc gr = scc (labEdges gr) (Map.fromList $ [(n,Set.fromList [n]) | n <- nodes gr]) []
  where scc :: [(Node,Node,Set Node)] -> Map Node (Set Node) -> [(Set Node,Node)] -> Map Node (Set Node)
        scc []                  sccs []               = sccs
        scc uedges@((n,m,_):es) sccs []               = scc uedges sccs [(Set.empty,n)]
        scc uedges              sccs path@((_,n):ns)  = -- trace ((show path) ++ "\t\t" ++ (show sccs)) $
         case es of
          []                  -> scc uedges sccs ns
          ((n',m,summ):_) ->   if (any (m ∈) ( [ sccs ! n | (_,n) <- path])) then
                                 scc (delete (n',m,summ) uedges) (merge sccs ((summ,m):cycle)) prefix
                               else
                                 scc (delete (n',m,summ) uedges)  sccs                         ((summ,m):path)
            where (cycle, prefix) = span (\(summ,n) -> not $ (m ∈) (sccs ! n)) path
         where es :: [(Node,Node,Set Node)]
               es = [ (n',m,summ) | n' <- Set.toList $ sccs ! n, (m,summ) <- lsuc gr n', (n',m,summ) `elem` uedges ]
               merge sccs cycle = -- trace ("Merge: " ++ ((show cycle) ++ "\t\t" ++ (show sccs))) $
                                  sccs ⊔ (Map.fromList [ (n, (∐) [ sccs ! n' | (summ,c) <- cycle, n' <- c : (Set.toList summ) ])
                                                       | (summ,c) <- cycle,  n <- Set.toList (sccs ! c)
                                                       ])

                  -- summToSumm = if (any (any (∈) [ summN | (summN,_) <- path]) summ then
                  --                Map.fromList [ (m, [ n | (_,n) <- cycle]) | m <- Set.toList $ summ, m ∈ summ' ]
                  --              else
                  --                Set.empty
                  --    where (cycle,(summ',m'):prefix) = span (\(summN,n) -> not $ (any (∈ summN) summ)) path


-- balancedSCC  :: DynGraph gr => gr a (Set Node) -> Map Node (Set Node)
-- balancedSCC gr = scc (labEdges gr) (Map.fromList $ [(n,Set.fromList [n]) | n <- nodes gr]) []
--   where sameLvlSccs = sameLevelSccs gr
--         scc :: [(Node,Node,Set Node)] -> Map Node (Set Node) -> [(Set Node,Node)] -> Map Node (Set Node)
--         scc []                  sccs []               = sccs
--         scc uedges@((n,m,_):es) sccs []               = scc uedges sccs [(Set.empty,n)]
--         scc uedges              sccs path@((_,n):ns)  = -- trace ((show path) ++ "\t\t" ++ (show sccs)) $
--          case es of
--           []                  -> scc uedges sccs ns
--           ((n',m,summ):_) ->   if (any (m ∈) ( [ sccs ! n | (_,n) <- path])) then
--                                  scc (delete (n',m,summ) uedges) (merge sccs ((summ,m):cycle)) prefix
--                                else
--                                  scc (delete (n',m,summ) uedges)  sccs                         ((summ,m):path)
--             where (cycle, prefix) = span (\(summ,n) -> not $ (m ∈) (sccs ! n)) path
--                   summToSumm = if (any (any (∈) [ summN | (summN,_) <- path]) summ then
--                                  Map.fromList [ (m, [ n | (_,n) <- cycle]) | m <- Set.toList $ summ, m ∈ summ' ]
--                                else
--                                  Map.empty
-- --                     where (cycle,(summ',m'):prefix) = span (\(summN,n) -> not $ (any (∈ summN) summ)) path
--                   nodeToSumm = if (any (∈ summ ) [ (_,n) <- path]) then
--                                  Map.fromList 
--                                else
--                      where (cycle,prefix) = span (\(_,n) -> not $ ∈ summ) path
--          where es :: [(Node,Node,Set Node)]
--                es = [ (n',m,summ) | n' <- Set.toList $ sameLevelSccs ! n, (m,summ) <- lsuc gr n', (n',m,summ) `elem` uedges ]



toBalanced :: (Graph gr) => gr a b -> gr a (Annotation ())
toBalanced gr = mkGraph (labNodes gr) [ (n,m,Nothing) | (m,n) <- edges gr]

sccIsSccNaive :: Gr () () -> Bool
sccIsSccNaive gr = sccs == sccsNaive
  where sccs      = Set.fromList $ (fmap Set.fromList $ scc gr)
        sccsNaive = Set.fromList $ (fmap Set.fromList $ sccNaive gr)


sccIsSameLevelScc :: Gr () () -> Bool
sccIsSameLevelScc gr = sccs == sccsNaive
  where sccs      = Set.fromList $ (fmap Set.fromList $ scc gr)
        sccsNaive = Set.fromList $ [ balancedSccs ! n | n <- nodes $ gr]
        balancedSccs = sameLevelScc $ sameLevelSummaryGraph'WithoutBs $ toBalanced $ gr



parenLabelsIn gr = Set.fromList $ [ b | (_,_,Just (Open b)) <- labEdges gr] ++
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


sameLvlNodes'WithoutBs gr =
    (㎲⊒) (  Map.fromList [ ((n,m), Set.empty                                   ) | n <- nodes gr, m <- nodes gr],
             Map.fromList [ ((n,m), if n==m then Set.fromList [n] else Set.empty) | n <- nodes gr, m <- nodes gr]
          )
          (\(sameLevel, onLevel) -> (
             sameLevel ⊔ Map.fromList [ ((n,m), (∐) [ onLevel ! (n',m') | (n', Just (Open b ))  <- lsuc gr n,
                                                                          (m', Just (Close b')) <- lpre gr m,  b' == b,  not $ Set.null $ onLevel ! (n',m')
                                                    ]
                                        )
                                      | n <- nodes gr, m <- nodes gr ]
             ,
             onLevel   ⊔ Map.fromList [ ((n,m),   (∐) [ onLevel ! (n',m)  ⊔  onLevel ! (n,n)                        | n' <- successors           n, not $ Set.null $ onLevel ! (n', m)]
                                                ⊔ (∐) [ onLevel ! (n',m)  ⊔  onLevel ! (n,n)  ⊔  sameLevel ! (n,n') | n' <- samelvlsuc sameLevel n, not $ Set.null $ onLevel ! (n', m)]
                                        )
                                      | n <- nodes gr, m <- nodes gr ]
             )
           )
    where successors n = nub [ n' | (n',Nothing)         <- lsuc gr n]
          samelvlsuc sameLevel
                     n = nub [ n' | (n'',  Just (Open  b))  <- lsuc gr n,
                                    (m,n', Just (Close b')) <- labEdges gr, b' == b, not $ Set.null $  sameLevel ! (n,n')
                             ]


sameLvlNodes' gr =
    (㎲⊒) (  Map.fromList [ ((n,m,b), Set.empty                                  ) | n <- nodes gr, m <- nodes gr, b <- parenLabels],
             Map.fromList [ ((n,m),if n==m then Set.fromList [n] else Set.empty)   | n <- nodes gr, m <- nodes gr]
          )
          (\(sameLevel, onLevel) -> (
             sameLevel ⊔ Map.fromList [ ((n,m,b), (∐) [ onLevel ! (n',m') | (n', Just (Open b'))   <- lsuc gr n,  b'  == b,
                                                                            (m', Just (Close b'')) <- lpre gr m,  b'' == b',  not $ Set.null $ onLevel ! (n',m')
                                                      ]
                                        )
                                      | n <- nodes gr, m <- nodes gr, b <- parenLabels ]
             ,
             onLevel   ⊔ Map.fromList [ ((n,m),   (∐) [ onLevel ! (n',m)  ⊔  onLevel ! (n,n)                          | n' <- successors           n, not $ Set.null $ onLevel ! (n', m)]
                                                ⊔ (∐) [ onLevel ! (n',m)  ⊔  onLevel ! (n,n)  ⊔  sameLevel ! (n,n',b) | n' <- samelvlsuc sameLevel n, not $ Set.null $ onLevel ! (n', m), b <- parenLabels ]
                                        )
                                      | n <- nodes gr, m <- nodes gr ]
             )
           )
    where successors n = nub [ n' | (n',Nothing)         <- lsuc gr n]
          samelvlsuc sameLevel
                     n = nub [ n' | (n'',  Just (Open  b))  <- lsuc gr n,
                                    (m,n', Just (Close b')) <- labEdges gr, b' == b, not $ Set.null $  sameLevel ! (n,n',b)
                             ]
          parenLabels = Set.toList $ parenLabelsIn gr




sameLevelNodes :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node,b) (Set Node)
sameLevelNodes = fst . sameLvlNodes

sameLevelNodes' :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node,b) (Set Node)
sameLevelNodes' = fst . sameLvlNodes'

sameLevelNodes'WithoutBs :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node) (Set Node)
sameLevelNodes'WithoutBs = fst . sameLvlNodes'WithoutBs

sameLevelSummaryGraph :: (Graph gr, Ord b) => gr a (Annotation b) -> gr a (Set Node)
sameLevelSummaryGraph gr =
    mkGraph (labNodes gr)
            ( [(n,m,Set.empty) | (n,m,Nothing) <- labEdges gr] ++
              [(n,n', sameLevel ! (m, m', b)) | n <- nodes gr, n' <- nodes gr,
                                                (m',  Just (Close b)) <- nub $ lpre gr n',
                                                (m,   Just (Open b')) <- nub $ lsuc gr n, b' == b
              ]
            )
  where sameLevel = sameLevelNodes gr

sameLevelSummaryGraphMerged :: (Graph gr, Ord b) => gr a (Annotation b) -> gr a (Set Node)
sameLevelSummaryGraphMerged gr =
    mkGraph (labNodes gr)
            ( [(n,m,Set.empty) | (n,m,Nothing) <- labEdges gr] ++
              [(n,n', merged)  | n <- nodes gr, n' <- nodes gr,
                                 let merged = (∐) [ sameLevel ! (m, m', b) | (m',  Just (Close b)) <- nub $ lpre gr n',
                                                                             (m,   Just (Open b')) <- nub $ lsuc gr n, b' == b
                                                  ],
                                 not $ Set.null merged
               ]
            )
  where sameLevel = sameLevelNodes gr

sameLevelSummaryGraph' :: (Graph gr, Ord b) => gr a (Annotation b) -> gr a (Set Node)
sameLevelSummaryGraph' gr =
    mkGraph (labNodes gr)
            ( [(n,m,Set.empty) | (n,m,Nothing) <- labEdges gr] ++
              [(n,m, sameLevel ! (n,m,b)) | n <- nodes gr, m <- nodes gr, b <- parenLabels,
                                            not $ Set.null $  sameLevel ! (n,m,b)
              ]
            )
  where sameLevel = sameLevelNodes' gr
        parenLabels = Set.toList $ parenLabelsIn gr


sameLevelSummaryGraph'WithoutBs :: (Graph gr, Ord b) => gr a (Annotation b) -> gr a (Set Node)
sameLevelSummaryGraph'WithoutBs gr =
    mkGraph (labNodes gr)
            ( [(n,m,Set.empty) | (n,m,Nothing) <- labEdges gr] ++
              [(n,m, sameLevel ! (n,m)) | n <- nodes gr, m <- nodes gr,
                                          not $ Set.null $  sameLevel ! (n,m)
              ]
            )
  where sameLevel = sameLevelNodes'WithoutBs gr
        parenLabels = Set.toList $ parenLabelsIn gr



graphTest0 :: Gr () (Annotation String)
graphTest0 = mkGraph [ (i,()) | i <- [0..7]]
                    [ (0,1, Just $ Open "main"),
                      (1,2, Just $ Open "l"),
                      (2,3, Nothing),
                      (3,4, Just $ Close "l"),
                      (4,5, Nothing),
                      (5,2, Just $ Open "r"),
                      (3,6, Just $ Close "r"),
                      (6,7, Just $ Close "main")
                    ]

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


graphTest3 :: Gr () (Annotation String)
graphTest3 =
    mkGraph [ (i,()) | i <- [0..7] ]
            [ (0,1, Just $ Open "main"),
              (1,2, Nothing),
              (2,1, Just $ Open "l"),
              (2,6, Nothing),
              (3,1, Just $ Open "r"),
              (6,5, Nothing),
              (4,5, Nothing),
              (5,3, Just $ Close "l"),
              (5,4, Just $ Close "l"),
              (5,7, Just $ Close "main")
            ]

graphTest4 :: Gr () (Annotation String)
graphTest4 =
    mkGraph [ (i,()) | i <- [0..7] ]
            [ (0,1, Just $ Open "main"),
              (1,2, Just $ Open "a"),
              (2,3, Just $ Open "b"),
              (3,4, Just $ Close "b"),
              (4,5, Just $ Close "a"),
              (5,2, Just $ Open "c"),
              (4,6, Just $ Close "c"),
              (6,7, Just $ Close "main")
            ]


-- http://dx.doi.org/10.1145/1255450.1255452  Fig 2)
graphTest5 :: Gr () (Annotation String)
graphTest5 =
    mkGraph [ (i,()) | i <- [1..8] ]
            [ (1,2, Nothing),
              (1,7, Nothing),
              (2,3, Just $ Open "a"),
              (7,3, Just $ Open "b"),
              (3,4, Nothing),
              (4,5, Just $ Close "a"),
              (4,8, Just $ Close "b"),
              (5,6, Nothing),
              (8,6, Nothing)
            ]

-- http://dx.doi.org/10.1145/1255450.1255452  Fig 3)
graphTest6 :: Gr () (Annotation String)
graphTest6 =
    mkGraph [ (i,()) | i <- [1..4] ]
            [ (1,3, Nothing),
              (1,2, Nothing),
              (3,1, Just $ Open "a"),
              (4,2, Nothing),
              (2,3, Just $ Close "a")
            ]

-- http://dx.doi.org/10.1145/1255450.1255452  Fig 4)
graphTest7 :: Gr () (Annotation String)
graphTest7 =
    mkGraph [ (i,()) | i <- [1..12] ]
            [ ( 1, 2, Nothing),
              ( 1,10, Nothing),
              ( 8, 9, Nothing),
              (12, 9, Nothing),
              ( 3, 4, Nothing),
              ( 6, 7, Nothing),

              ( 2, 3, Just $ Open  "a1"),
              ( 4, 5, Just $ Close "a1"),
              (11, 3, Just $ Open  "a2"),
              ( 4,12, Just $ Close "a2"),
              (10, 6, Just $ Open  "b1"),
              ( 7,11, Just $ Close "b1"),
              ( 5, 6, Just $ Open  "b2"),
              ( 7, 8, Just $ Close "b2")
            ]

-- http://dx.doi.org/10.1145/1255450.1255452  Fig 6)
graphTest8 :: Gr () (Annotation String)
graphTest8 =
    mkGraph [ (i,()) | i <- [0..7] ]
            [ 
              (0,1, Nothing),
              (0,6, Nothing),
              (1,2, Just $ Open "a"),
              (2,3, Nothing),
              (6,3, Just $ Open "b"),
              (3,4, Nothing),
              (4,5, Just $ Close "a"),
              (4,7, Just $ Close "b")
            ]


-- This used to be a  counterexample to balancedChopIsSimulBalancedChop when balancedChop was slightly buggy
graphTest9  :: Gr () (Annotation String)
graphTest9 = mkGraph [(-4,()),(-2,()),(3,()),(18,()),(55,())] [(-4,3,Just (Close "b")),(-2,-4,Just (Close "b")),(-2,-2,Nothing),(3,-2,Nothing),(3,55,Just (Open "a")),(18,-2,Just (Close "a")),(55,18,Just (Open "a"))] 

funbl summary graph s = forward s s
  where forward []     found = found
        forward (n:ns) found = forward  ((new       ) ++ ns) (new ++ found)
           where successors = nub $ 
                                  [n' | (n',Nothing)        <- lsuc graph n]
                               ++ [n' | (n', Just (Open _)) <- lsuc graph n]
                               ++ [n' | (n', ms)            <- lsuc summary n, not $ Set.null ms]
                 new        = successors \\ found

funbr summary graph s = forward s s
  where forward []     found = found
        forward (n:ns) found = forward  ((new       ) ++ ns) (new ++ found)
           where successors = nub $ 
                                  [n' | (n',Nothing)         <- lsuc graph n]
                               ++ [n' | (n', Just (Close _)) <- lsuc graph n]
                               ++ [n' | (n', ms)             <- lsuc summary n, not $ Set.null ms]
                 new        = successors \\ found


bunbr summary graph t = backward t t
  where backward []     found = found
        backward (n:ns) found = backward  ((new       ) ++ ns) (new ++ found)
           where predecessors = nub $ 
                                   [n' | (n',Nothing)         <- lpre graph n]
                                ++ [n' | (n', Just (Close _)) <- lpre graph n]
                                ++ [n' | (n', ms)             <- lpre summary n, not $ Set.null ms]
                 new        = predecessors \\ found

bunbl summary graph t = backward t t
  where backward []     found = found
        backward (n:ns) found = backward  ((new       ) ++ ns) (new ++ found)
           where predecessors = nub $ 
                                   [n' | (n',Nothing)        <- lpre graph n]
                                ++ [n' | (n', Just (Open _)) <- lpre graph n]
                                ++ [n' | (n', ms)            <- lpre summary n, not $ Set.null ms]
                 new        = predecessors \\ found


balancedChop summary graph s t = -- trace ((show $ Set.fromList w) ++ "   " ++ (show $ Set.fromList vr) ++ "   " ++ (show $ Set.fromList vl) ++ "\n")  $
 Set.fromList vr ∪ Set.fromList vl ∪ (∐) [ ms | (n,n',ms) <- labEdges summary, not $ Set.null ms, (n `elem` vr && n' `elem` vr) || (n `elem` vl && n' `elem`vl)]
    where w  = (funbr summary graph [s]) `intersect` (bunbl summary graph [t])
          vr = (funbr summary graph [s]) `intersect` (bunbr summary graph w  )
          vl = (funbl summary graph w  ) `intersect` (bunbl summary graph [t])


simulUnbr summary gr =
    (㎲⊒) (  Map.fromList [ ((n,m),if n==m then Set.fromList [n] else Set.empty) | n <- nodes gr, m <- nodes gr])
          (\ch ->
             ch
           ⊔ Map.fromList [ ((n,m),  (∐) [ ch ! (n',m)  ⊔  ch ! (n,n) | n' <- successors n, not $ Set.null $ ch ! (n', m)]) | n <- nodes gr, m <- nodes gr ]
          )
    where successors n = nub $
                            [n' | (n',Nothing)          <- lsuc gr n]
                         ++ [n' | (n', Just (Close _))  <- lsuc gr n]
                         ++ [n' | (n', ms)              <- lsuc summary n, not $ Set.null ms]


simulUnbl summary gr =
    (㎲⊒) (  Map.fromList [ ((n,m),if n==m then Set.fromList [n] else Set.empty) | n <- nodes gr, m <- nodes gr])
          (\ch ->
             ch
           ⊔ Map.fromList [ ((n,m),  (∐) [ ch ! (n',m)  ⊔  ch ! (n,n) | n' <- successors n, not $ Set.null $ ch ! (n', m)]) | n <- nodes gr, m <- nodes gr ]
          )
    where successors n = nub $
                            [n' | (n',Nothing)          <- lsuc gr n]
                         ++ [n' | (n', Just (Open _))   <- lsuc gr n]
                         ++ [n' | (n', ms)              <- lsuc summary n, not $ Set.null ms]


simulUnbl' summary gr =
    (㎲⊒) (  Map.fromList [ ((n,m),(if n==m then Set.fromList [n] else Set.empty, Set.empty)) | n <- nodes gr, m <- nodes gr])
          (\ch ->
             ch
           ⊔ Map.fromList [ ((n,m),  (∐) [ ch ! (n',m)  ⊔  ch ! (n,n) ⊔ (Set.empty,  if (isSummary) then Set.fromList [(n,n')] else Set.empty) | (n',isSummary) <- successors n, not $ Set.null $ fst $ ch ! (n', m)]) | n <- nodes gr, m <- nodes gr ]
          )
    where successors n = nub $
                            [(n',False) | (n',Nothing)          <- lsuc gr n]
                         ++ [(n',False) | (n', Just (Open _))   <- lsuc gr n]
                         ++ [(n',True)  | (n', ms)              <- lsuc summary n, not $ Set.null ms]


simulUnbr' summary gr =
    (㎲⊒) (  Map.fromList [ ((n,m),(if n==m then Set.fromList [n] else Set.empty, Set.empty)) | n <- nodes gr, m <- nodes gr])
          (\ch ->
             ch
           ⊔ Map.fromList [ ((n,m),  (∐) [ ch ! (n',m)  ⊔  ch ! (n,n) ⊔ (Set.empty,  if (isSummary) then Set.fromList [(n,n')] else Set.empty) | (n',isSummary) <- successors n, not $ Set.null $ fst $ ch ! (n', m)]) | n <- nodes gr, m <- nodes gr ]
          )
    where successors n = nub $
                            [(n',False) | (n',Nothing)          <- lsuc gr n]
                         ++ [(n',False) | (n', Just (Close _))   <- lsuc gr n]
                         ++ [(n',True)  | (n', ms)              <- lsuc summary n, not $ Set.null ms]

simulUnbr'' summary gr =
    floydWarshall (nodes gr)
                  (         Map.fromList [((n,m), (Set.empty, Set.empty)) | n <- nodes gr, m <- nodes gr]
                     ⊔ (∐) [Map.fromList [((n,m), (Set.fromList [n,m], ss))]  | (n,m,ss) <- es]
                  )
  where floydWarshall []     ch = ch
        floydWarshall (k:ks) ch = floydWarshall ks (
          Map.mapWithKey (\(n,m) chnm ->
           let chnk = ch ! (n,k)
               chkm = ch ! (k,m) in
           if ((not $ Set.null $ fst $ chnk) &&
               (not $ Set.null $ fst $ chkm))
           then chnm  ⊔  chnk ⊔ chkm
           else chnm
          ) ch
         )
        es =    [(n, m, Set.empty)            | (n,m, Nothing)         <- labEdges gr]
             ++ [(n, m, Set.empty)            | (n,m, Just (Close _))  <- labEdges gr]
             ++ [(n, m, Set.fromList [(n,m)]) | (n,m, ms) <- labEdges summary, not $ Set.null ms]
             ++ [(n, n, Set.empty)            | n <- nodes gr]


simulBalancedChop summary gr =
    Map.mapWithKey (\(n,m) ns -> (fst ns) ⊔ (∐) [ ms | (n',m') <- Set.toList $ snd ns, ms <- [ ms | (n',m'',ms) <- out summary n', m'' == m']]) updown
  where
        updown = Map.fromList [ ((n,m), (∐) [ if ((Set.null $ fst $ unbr ! (n,n')) || (Set.null $ fst $ unbl ! (n',m))) then (Set.empty, Set.empty) else unbr ! (n,n') ⊔  unbl ! (n',m)   | n' <- nodes gr]) 
                              | n <- nodes gr, m <- nodes gr ]

        unbr = simulUnbr' summary gr
        unbl = simulUnbl' summary gr




simulUnbrIsUnbr ::  Gr () (Annotation String) -> Bool
simulUnbrIsUnbr gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (Set.fromList $ funbr summary gr [s])  ∩
             (Set.fromList $ bunbr summary gr [t])   == (simul ! (s,t))
      )
    )
  where simul = simulUnbr summary gr
        summary = sameLevelSummaryGraph'WithoutBs gr


simulUnblIsUnbl ::  Gr () (Annotation String) -> Bool
simulUnblIsUnbl gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (Set.fromList $ funbl summary gr [s])  ∩
             (Set.fromList $ bunbl summary gr [t])   == (simul ! (s,t))
      )
    )
  where simul = simulUnbl summary gr
        summary = sameLevelSummaryGraph'WithoutBs gr


simulUnbr'IsUnbr ::  Gr () (Annotation String) -> Bool
simulUnbr'IsUnbr gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (Set.fromList $ funbr summary gr [s])  ∩
             (Set.fromList $ bunbr summary gr [t])   == (simul ! (s,t))
      )
    )
  where simul = fmap fst $ simulUnbr' summary gr
        summary = sameLevelSummaryGraph'WithoutBs gr


simulUnbl'IsUnbl ::  Gr () (Annotation String) -> Bool
simulUnbl'IsUnbl gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (Set.fromList $ funbl summary gr [s])  ∩
             (Set.fromList $ bunbl summary gr [t])   == (simul ! (s,t))
      )
    )
  where simul = fmap fst $ simulUnbl' summary gr
        summary = sameLevelSummaryGraph'WithoutBs gr


balancedChopIsSimulBalancedChop ::  Gr () (Annotation String) -> Bool
balancedChopIsSimulBalancedChop gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (balanced s t) == (simul ! (s,t))
      )
    )
  where simul = simulBalancedChop summary gr
        balanced = balancedChop summary gr
        summary = sameLevelSummaryGraph'WithoutBs gr

rofl = do
--    InterGraph gr <- generate $ resize 175  (arbitrary :: Gen (InterGraph () String))
--    let (MkGen g) = arbitrary :: Gen (InterGraph () String)
--    let (InterGraph gr) = g (mkQCGen 49) 175 -- 44, 48,

    let (MkGen g) = arbitrary :: Gen (InterCFG () String)
    let (InterCFG s gr) = g (mkQCGen 49) 40 -- 44, 48,

    start <- getCurrentTime
    let summary = sameLevelSummaryGraphMerged gr
    putStr $ show (summe $ [ ((s,t),Set.size ms) | (s,t,ms) <- labEdges summary ]) ++ "\t\t"
    stop <- getCurrentTime
    print $ diffUTCTime stop start

    start <- getCurrentTime
    let summary = sameLevelSummaryGraph'WithoutBs gr
    putStr $ show (summe $ [ ((s,t),Set.size ms) | (s,t,ms) <- labEdges summary ]) ++ "\t\t"
    stop <- getCurrentTime
    print $ diffUTCTime stop start

    putStrLn "-----------------"

    start <- getCurrentTime
    let summary = sameLevelSummaryGraph gr
    putStr $ show (summe $ [ ((s,t),Set.size ms) | (s,t,ms) <- labEdges summary ]) ++ "\t\t"
    stop <- getCurrentTime
    print $ diffUTCTime stop start

    start <- getCurrentTime
    let summary = sameLevelSummaryGraph' gr
    putStr $ show (summe $ [ ((s,t),Set.size ms) | (s,t,ms) <- labEdges summary ]) ++ "\t\t"
    stop <- getCurrentTime
    print $ diffUTCTime stop start


    -- start <- getCurrentTime
    -- putStr $ show (summe $ Map.toList $ fmap (Set.size) $ simulUnbr summary gr) ++ "\t\t"
    -- stop  <- getCurrentTime
    -- print $ diffUTCTime stop start

    -- start <- getCurrentTime
    -- putStr $ show (summe $ Map.toList $ fmap (Set.size) $ simulUnbl summary gr) ++ "\t\t"
    -- stop  <- getCurrentTime
    -- print $ diffUTCTime stop start



    -- start <- getCurrentTime
    -- putStr $ show (summe $ Map.toList $ fmap (Set.size) $ simulBalancedChop gr) ++ "\t\t"
    -- stop  <- getCurrentTime
    -- print $ diffUTCTime stop start


    -- start <- getCurrentTime
    -- let summary = sameLevelSummaryGraph gr
    -- putStr $ show (summe $ [ ((s,t),Set.size $ balancedChop summary gr s t) | s <- nodes gr, t <- nodes gr])  ++ "\t\t"
    -- stop <- getCurrentTime
    -- print $ diffUTCTime stop start


  where summe l = sum $ fmap (\((a,b),c) -> a+b+c) l







interDom gr s = (gfpFrom)
                     (Map.fromList $ [(n, all) | n <- nodes gr, n/=s] ++ [(s,Set.fromList [s])])
                     (\dom ->
                        Map.fromList [(n,  Set.fromList [n] ⊔ meetFrom all [ (∐) [dom ! n' | n' <- preds] | preds <- predecessors gr ! n]) | n <- nodes gr]
                     )
    where all = Set.fromList $ nodes gr

predecessors gr = Map.fromList [(n, [ [n'] | n' <- [ n' | (n',Nothing)  <- lpre gr n]
                                                ++ [ n' | (n', Just (Open _)) <- lpre gr n]
                                    ] ++
                                    [ [n', n'']   | (n', Just (Close x)) <- lpre gr n,
                                                    n'' <- if null [ n'' | (n'',_, Just (Open x')) <- labEdges gr, x == x'] then [n'] else  [n'' | (n'',_, Just (Open x')) <- labEdges gr, x == x']
                                    ]
                                )
                               | n <- nodes gr
                               ]

interIDom :: (Eq b, Graph gr) =>  gr a (Annotation b) -> Node -> Map Node (Set Node)
interIDom gr s =
    Map.delete s $
    Map.mapWithKey (\n ms -> Set.delete n ms  ) $  trrAcyclicPredMap $  interDom gr s

interDomIsDomOnIntra :: Gr () () -> Bool
interDomIsDomOnIntra gr
    | null (nodes gr) = True
    | otherwise       = doms == interDom (emap (\_ -> Nothing) gr :: Gr () (Annotation ())) s
  where (s:_) = nodes gr
        doms :: Map Node (Set Node)
        doms = Map.fromList $ [(n, Set.fromList ns) | (n,ns) <- dom gr s]

interIDomIsIDomOnIntra :: (Connected Gr () ()) -> Bool
interIDomIsIDomOnIntra (CG s gr) = idoms == interIDom (emap (\_ -> Nothing) gr :: Gr () (Annotation ())) s
  where idoms :: Map Node (Set Node)
        idoms = Map.fromList $ [(n, Set.fromList [i]) | (n,i) <- iDom gr s]



chopsInterIDomAreChops :: InterCFG () String -> Bool
chopsInterIDomAreChops (InterCFG s gr) =
    (∀) (nodes gr) (\n ->
      (∀) (pre interDomsGraph n) (\c -> n == s ∨ c == n ∨
        (∀) (interIDoms ! n) (\i ->  (balancedChop summary gr c n) == (balancedChop summary gr c i) ∪ (balancedChop summary gr i n)
        )
      )
    )
  where interDoms = interDom gr s
        interDomsGraph = fromPredMap interDoms :: Gr () ()
        interIDoms = interIDom gr s -- TODO: performance
        summary = sameLevelSummaryGraph'WithoutBs gr


chopsInterIDomAreChopsCounterExamples :: InterCFG () String -> [(Node,Node,Node)]
chopsInterIDomAreChopsCounterExamples (InterCFG s gr) = [ (c,i,n) | n <- (nodes gr),
                                                     c <- pre interDomsGraph n,
                                                     not $  n == s ∨ c == n,
                                                     i <- Set.toList $ interIDoms ! n,
                                                     not $  (balancedChop summary gr c n) == (balancedChop summary gr c i) ∪ (balancedChop summary gr i n)
                                         ]
  where interDoms = interDom gr s
        interDomsGraph = fromPredMap interDoms :: Gr () ()
        interIDoms = interIDom gr s -- TODO: performance
        summary = sameLevelSummaryGraph'WithoutBs gr


sameLevelSummaryGraphIssameLevelSummaryGraph' :: InterCFG () String -> Bool
sameLevelSummaryGraphIssameLevelSummaryGraph' (InterCFG _ gr) = sameLevelSummaryGraph gr == sameLevelSummaryGraph' gr

sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs :: InterCFG () String -> Bool
sameLevelSummaryGraphMergedIssameLevelSummaryGraph'WithoutBs (InterCFG _ gr) = sameLevelSummaryGraphMerged gr == sameLevelSummaryGraph'WithoutBs gr
