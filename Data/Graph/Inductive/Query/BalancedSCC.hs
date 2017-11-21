{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleInstances, ScopedTypeVariables #-}

module Data.Graph.Inductive.Query.BalancedSCC where
import Data.Time

import Debug.Trace
import Util

import System.Random
import Control.Monad.Random
import Control.Exception.Base (assert)

import Algebra.Lattice hiding (gfpFrom)
import Algebra.PartialOrd (unsafeGfpFrom)

import Unicode

import Data.Maybe(fromJust, isNothing, isJust)

import Data.List(union, intersect, elem, delete, sort, (\\), nub, null)

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

-- for some reason, the gfpFrom in Algebra.Lattice requires functions to be antitone, instead of monotone!!?!?
gfpFrom  = unsafeGfpFrom

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
                     addProcedures [(InterCFG s p,t)] (size `div` 20) (size `div` 20) size
      where
        genProc :: Int -> Gen (Node, Node, Gr () (Annotation String))
        genProc size =
            do (CG s p0  :: Connected Gr () ()) <- resize size arbitrary
               let p = removeDuplicateEdges p0
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
                                                                   gr'' = if (not $ all (∊ nodes gr') [n,ssuc,tsuc,m]) then error (show ([n,ssuc,tsuc,t], gr', p')) else
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
          where candidates = [(n,m,Nothing) | (n,m,Nothing) <- labEdges gr, not $ n ∊ ((fmap fst sts) ++ (fmap snd sts)),
                                                                            not $ m ∊ ((fmap fst sts) ++ (fmap snd sts))
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
          ((n',m):_) -> if (any (m ∊) (fmap sccOf path)) then
                           scc (delete (n',m) uedges) (merge sccs (m:cycle)) prefix
                         else
                           scc (delete (n',m) uedges)  sccs                  (m:path)
            where (cycle, prefix) = span (\n -> not $ m ∊ (sccOf n)) path
         where es = [ (n',m) | n' <- sccOf n, m <- suc gr n', (n',m) ∊ uedges ]
               sccOf m =  the (m ∊) $ sccs




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
               es = [ (n',m,summ) | n' <- Set.toList $ sccs ! n, (m,summ) <- lsuc gr n', (n',m,summ) ∊ uedges ]
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
--                es = [ (n',m,summ) | n' <- Set.toList $ sameLevelSccs ! n, (m,summ) <- lsuc gr n', (n',m,summ) ∊ uedges ]



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
            sameLevel ⊔ (onLevel `restrict` (Map.keysSet sameLevel)),
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



sameLvlNodes'WithBs gr =
    (㎲⊒) (  Map.fromList [ ((n,m), (Set.empty,Set.empty)                       ) | n <- nodes gr, m <- nodes gr],
             Map.fromList [ ((n,m), if n==m then Set.fromList [n] else Set.empty) | n <- nodes gr, m <- nodes gr]
          )
          (\(sameLevel, onLevel) -> (
             sameLevel ⊔ Map.fromList [ ((n,m), (∐) [ (onLevel ! (n',m'), Set.fromList [b]) | (n', Just (Open b ))  <- lsuc gr n,
                                                                                              (m', Just (Close b')) <- lpre gr m,  b' == b,  not $ Set.null $ onLevel ! (n',m')
                                                    ]
                                        )
                                      | n <- nodes gr, m <- nodes gr ]
             ,
             onLevel   ⊔ Map.fromList [ ((n,m),   (∐) [ onLevel ! (n',m)  ⊔  onLevel ! (n,n)                                | n' <- successors           n, not $ Set.null $ onLevel ! (n', m)]
                                                ⊔ (∐) [ onLevel ! (n',m)  ⊔  onLevel ! (n,n)  ⊔  (fst $ sameLevel ! (n,n')) | n' <- samelvlsuc sameLevel n, not $ Set.null $ onLevel ! (n', m)]
                                        )
                                      | n <- nodes gr, m <- nodes gr ]
             )
           )
    where successors n = nub [ n' | (n',Nothing)         <- lsuc gr n]
          samelvlsuc sameLevel
                     n = nub [ n' | (n'',  Just (Open  b))  <- lsuc gr n,
                                    (m,n', Just (Close b')) <- labEdges gr, b' == b, not $ Set.null $  (fst $ sameLevel ! (n,n'))
                             ]


sameLevelNodes :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node,b) (Set Node)
sameLevelNodes = fst . sameLvlNodes

sameLevelNodes' :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node,b) (Set Node)
sameLevelNodes' = fst . sameLvlNodes'

sameLevelNodes'WithoutBs :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node) (Set Node)
sameLevelNodes'WithoutBs = fst . sameLvlNodes'WithoutBs

sameLevelNodes'WithBs :: (Graph gr, Ord b) => gr a (Annotation b) -> Map (Node,Node) (Set Node, Set b)
sameLevelNodes'WithBs = fst . sameLvlNodes'WithBs

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

sameLevelSummaryGraph'WithBs :: (Graph gr, Ord b) => gr a (Annotation b) -> gr a (Set Node, Set b)
sameLevelSummaryGraph'WithBs gr =
    mkGraph (labNodes gr)
            ( [(n,m,(Set.empty, Set.empty)) | (n,m,Nothing) <- labEdges gr] ++
              [(n,m, sameLevel ! (n,m)) | n <- nodes gr, m <- nodes gr,
                                          not $ Set.null $  fst $ sameLevel ! (n,m)
              ]
            )
  where sameLevel = sameLevelNodes'WithBs gr
        parenLabels = Set.toList $ parenLabelsIn gr



krinkeSCC  :: forall gr a b. (DynGraph gr, Ord b) => gr a (Annotation b) -> (gr [Node] (Annotation b), Map Node Node)
krinkeSCC g = (secondPassFolded, nodeMap)
  where firstPassSccs   = scc $ elfilter isFirstPassEdge g
          where isFirstPassEdge l = case l of
                  Nothing        -> True
                  Just (Open  _) -> True
                  Just (Close _) -> False
        sccOfFirst = Map.fromList [ (n0, n1) | n0 <- nodes g,
                                             let (n1,scc0) = the (\(n1,scc0) -> n0 ∊ scc0) (zip [0..] firstPassSccs)
                     ]
        firstPassFolded :: gr [Node] (Annotation b) 
        firstPassFolded = mkGraph [ (n1, scc0)  | (n1, scc0)  <- zip [0..] firstPassSccs]
                                  [ (n1, m1, e) | (n0, m0, e) <- labEdges g,
                                                  let n1 = sccOfFirst ! n0,
                                                  let m1 = sccOfFirst ! m0,
                                                  n1 /= m1
                                  ]

        secondPassSccs  = scc $ elfilter isSecondPassEdge firstPassFolded
          where isSecondPassEdge l = case l of
                  Nothing        -> True
                  Just (Open  _) -> False
                  Just (Close _) -> True
        sccOfSecond = Map.fromList [ (n1, n2) | n1 <- nodes firstPassFolded,
                                               let (n2,scc1) = the (\(n2,scc1) -> n1 ∊ scc1) (zip [0..] secondPassSccs)
                     ]
        secondPassFolded :: gr [Node] (Annotation b)
        secondPassFolded = mkGraph [ (n2, [ n0 | n1 <- scc1, Just scc0 <- [lab firstPassFolded n1], n0 <- scc0]) | (n2, scc1) <- zip [0..] secondPassSccs ]
                                   [ (n2,m2, e) | (n1, m1, e) <- labEdges firstPassFolded,
                                                let n2 = sccOfSecond ! n1,
                                                let m2 = sccOfSecond ! m1,
                                                n2 /= m2
                                   ]

        nodeMap :: Map Node Node
        nodeMap = Map.fromList [ (n0, n2) | n0 <- nodes g, let n1 = sccOfFirst ! n0, let n2 = sccOfSecond ! n1 ]




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
interCFGTest2 :: InterCFG () String
interCFGTest2 = InterCFG 0 graphTest2


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



graphTest10 :: Gr () (Annotation String)
graphTest10 =
    mkGraph [(i,()) | i <- [0..4] ++ [10..12] ++ [20..22] ++ [30..36]]
            [ 
              (0,1, Nothing),
              (1,2, Nothing),
              (2,1, Nothing),
              (2,3, Nothing),
              (4,3, Nothing),

              (30,31, Nothing),
              (31,32, Nothing),
              (32,33, Nothing),
              (33,34, Nothing),
              (35,36, Nothing),
              (36,34, Nothing),
              (36,31, Nothing),

              (11,12, Nothing),
              (21,22, Nothing),

              ( 1,30, Just $ Open  "0,3"),
              (34, 4, Just $ Close "0,3"),
             

              (32, 0, Just $ Open  "3,0"),
              ( 3,35, Just $ Close "3,0"),
    
              (10,30, Just $ Open  "1,3"),
              (34,11, Just $ Close "1,3"),

              (20,30, Just $ Open  "2,3"),
              (34,21, Just $ Close "2,3")
            ]



-- This example shows that two-phase krinkeSCC may lead to graphs in which there is *not* a finite number of contexts.
graphTest11 :: Gr () (Annotation String)
graphTest11 = mkGraph [(-57,()),(-56,()),(-52,()),(-38,()),(-26,()),(-18,()),(-15,()),(-13,()),(-7,()),(-5,()),(3,()),(12,()),(16,()),(23,()),(28,()),(50,()),(55,()),(57,())] [(-57,-56,Just (Close "a")),(-56,-18,Just (Close "b")),(-56,-15,Just (Close "a")),(-56,28,Just (Open "a")),(-56,57,Just (Open "c")),(-52,-56,Nothing),(-52,-18,Just (Close "b")),(-52,-15,Nothing),(-52,-7,Just (Open "b")),(-52,3,Just (Open "b")),(-38,-15,Just (Close "a")),(-38,-13,Nothing),(-38,16,Just (Close "b")),(-38,57,Just (Open "b")),(-26,55,Just (Open "b")),(-18,-18,Nothing),(-18,-15,Just (Close "c")),(-18,12,Just (Close "c")),(-18,16,Just (Close "a")),(-15,55,Just (Open "b")),(-13,-56,Nothing),(-13,-52,Just (Close "a")),(-13,23,Nothing),(-7,55,Nothing),(-5,-13,Just (Open "b")),(-5,3,Just (Close "b")),(-5,57,Nothing),(3,-15,Just (Close "c")),(3,-5,Just (Open "c")),(12,3,Nothing),(16,-57,Just (Open "b")),(16,-57,Just (Open "a")),(16,-5,Just (Close "a")),(16,12,Just (Close "a")),(23,-57,Just (Open "b")),(23,-57,Just (Close "c")),(23,28,Just (Open "a")),(50,3,Just (Open "a")),(50,12,Nothing),(50,28,Just (Close "a")),(50,50,Just (Open "a")),(50,50,Just (Open "c")),(50,55,Just (Open "a")),(55,-57,Just (Open "b")),(55,-38,Nothing),(55,-26,Nothing),(55,-18,Just (Close "a")),(55,-15,Just (Open "b")),(57,-26,Just (Close "a")),(57,-26,Just (Close "c")),(57,16,Just (Open "c"))]

graphTest12 :: Gr () (Annotation String)
graphTest12 =
    mkGraph [(i,()) | i <- [0..5]]
            [ 
              (1,2, Nothing),
              (3,4, Nothing),

              ( 0, 1, Just $ Open  "0,1"),
              ( 2, 3, Just $ Close "0,1"),

              ( 4, 1, Just $ Open  "4,1"),
              ( 2, 5, Just $ Close "4,1")
            ]

graphTest13  :: Gr () (Annotation String)
graphTest13 =  mkGraph [(0,()),(1,()),(2,()),(3,())] [(0,1,Just (Open "(0,1)")),(0,3,Just (Close "(2,0)")),(1,0,Just (Close "(0,1)")),(2,0,Just (Open "(2,0)"))]


graphTest14  :: Gr () (Annotation String)
graphTest14 = mkGraph [(1,()),(2,()),(27,()),(35,()),(36,()),(37,()),(63,()),(64,()),(65,())] [(1,2,Just (Close "(27,1)")),(1,36,Just (Close "(2,1)")),(2,1,Just (Open "(2,1)")),(2,35,Nothing),(27,1,Just (Open "(27,1)")),(27,27,Nothing),(27,35,Nothing),(35,63,Just (Close "(37,36)")),(36,2,Nothing),(36,27,Nothing),(36,35,Nothing),(37,36,Just (Open "(37,36)")),(37,65,Just (Close "(64,63)")),(63,37,Nothing),(64,63,Just (Open "(64,63)"))]

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
 Set.fromList vr ∪ Set.fromList vl ∪ (∐) [ ms | (n,n',ms) <- labEdges summary, not $ Set.null ms, (n ∊ vr && n' ∊ vr) || (n ∊ vl && n' ∊vl)]
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
    let summary = sameLevelSummaryGraph'WithBs gr
    putStr $ show (summe $ [ ((s,t),Set.size ms) | (s,t,(ms,_)) <- labEdges summary ]) ++ "\t\t"
    stop <- getCurrentTime
    print $ diffUTCTime stop start

    putStrLn "-----------------"

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
                        Map.fromList $ [(n,  Set.fromList [n] ⊔ meetFrom all [ (∐) [dom ! n' | n' <- preds] | preds <- predecessors gr ! n]) | n <- nodes gr, n /=s]
                                    ++ [(s, Set.fromList [s])]
                     )
    where all = Set.fromList $ nodes gr
          predecessors gr = Map.fromList
                                    [(n, [ [n'] | n' <- [ n' | (n',Nothing)  <- lpre gr n]
                                                     ++ [ n' | (n', Just (Open _)) <- lpre gr n]
                                         ] ++
                                         [ [n', n'']   | (n', Just (Close x)) <- lpre gr n,
                                                         n'' <- if null [ n'' | (n'',_, Just (Open x')) <- labEdges gr, x == x'] then [n'] else  [n'' | (n'',_, Just (Open x')) <- labEdges gr, x == x']
                                    ]
                                )
                               | n <- nodes gr
                               ]



interDomGeneral summary gr s = (gfpFrom)
                     (Map.fromList $ [(n, all) | n <- nodes gr, n/=s] ++ [(s,Set.fromList [s])])
                     (\dom ->
                        Map.fromList $ [(n,  Set.fromList [n] ⊔ meetFrom all [ (∐) [dom ! n' | n' <- preds] | preds <- predecessors gr ! n]) | n <- nodes gr, n /=s]
                                    ++ [(s, Set.fromList [s])]
                     )
    where all = Set.fromList $ nodes gr
          predecessors gr = Map.fromList
                                    [(n, [ [n'] | n' <- [ n' | (n',Nothing)  <- lpre gr n]
                                                     ++ [ n' | (n', Just (Open _)) <- lpre gr n]
                                         ] ++
                                         [ [n', n'']   | (n', Just (Close x)) <- lpre gr n,
                                                         n'' <- if null [ n'' | (n'', (_,xs)) <- lpre summary n, x ∈ xs] then [n'] else
                                                                        [ n'' | (n'', (_,xs)) <- lpre summary n, x ∈ xs] -- TODO: this should always be a singular list, fix accordingly?!?!
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

sameLevelSummaryGraph'WithBsIssameLevelSummaryGraph'WithoutBs :: InterCFG () String -> Bool
sameLevelSummaryGraph'WithBsIssameLevelSummaryGraph'WithoutBs (InterCFG _ gr) = emap fst (sameLevelSummaryGraph'WithBs gr) == sameLevelSummaryGraph'WithoutBs gr

type AnnotatedPath b = [LEdge (Annotation b)]


samplePathsFor :: (Eq b, Graph gr)             => Int -> Integer -> Integer ->  gr a (Annotation b) ->   [AnnotatedPath b]
samplePathsFor seed k maxlength g = fmap reverse $ evalRand (samplePaths k maxlength g) (mkStdGen seed)

samplePaths :: (MonadRandom m, Graph gr, Eq b) =>        Integer -> Integer ->  gr a (Annotation b) -> m [AnnotatedPath b]
samplePaths         k maxlength g
  | null (nodes g) = return $ take (fromInteger k) $ repeat []
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
              newTrace <- sampleTrace n0 [] 0
              sampleSome (newTrace:sampled) (i+1)
        sampleTrace n trace length
          | length >= maxlength = return trace
          | finished            = return trace
          | otherwise = do
               (m,e) <- sample successors
               sampleTrace m ((n,m,e):trace) (length + 1)
         where finished   = null successors
               successors = lsuc g n


sampleRealizablePathsFor :: (Eq b, Graph gr)             => Int -> Integer -> Integer ->  gr a (Annotation b) ->   [AnnotatedPath b]
sampleRealizablePathsFor seed k maxlength g = fmap reverse $ evalRand (sampleRealizablePaths k maxlength g) (mkStdGen seed)

sampleRealizablePaths :: (MonadRandom m, Graph gr, Eq b) =>        Integer -> Integer ->  gr a (Annotation b) -> m [AnnotatedPath b]
sampleRealizablePaths         k maxlength g
  | null (nodes g) = return $ take (fromInteger k) $ repeat []
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
              newTrace <- sampleTrace n0 [] [] 0
              sampleSome (newTrace:sampled) (i+1)
        sampleTrace n stack trace length
          | length >= maxlength = return trace
          | finished            = return trace
          | otherwise = do
               (m,e,newStack) <- sample successors
               sampleTrace m newStack ((n,m,e):trace) (length + 1)
         where finished   = null successors
               successors = case stack of
                 []     -> [ (m, e, newStack) | (m, e) <- lsuc g n, let (valid, newStack) = step e, valid ]
                   where step Nothing           = (True,   stack)
                         step (Just (Open x))   = (True, x:stack)
                         step (Just (Close x))  = (False,  undefined)
                 (y:ys) -> [ (m, e, newStack) | (m, e) <- lsuc g n, let (valid, newStack) = step e, valid ]
                   where step Nothing           = (True,   stack)
                         step (Just (Open x))   = (True, x:stack)
                         step (Just (Close x))  = ( x == y, ys)


αFor :: (Eq b, DynGraph gr, Ord b) => gr a (Annotation b) -> (gr [Node] (Annotation b), Map Node Node) -> AnnotatedPath b -> AnnotatedPath b
αFor _ _ [] = []
αFor g (folded, nodeMap) path@((n,m,e):_) = abstractPath n (nodeMap ! n) path
  where abstractPath n sccN ((_,m,e):path)
            | sccM == sccN =                 abstractPath m sccM path
            | otherwise    = (sccN, sccM, e):abstractPath m sccM path
          where sccM = nodeMap ! m
        abstractPath n sccN [] = []

α g = αFor g (krinkeSCC g)


hasCycle :: AnnotatedPath b -> Bool
hasCycle   []             = False
hasCycle path@((n,_,e):_) = (Set.size $ Set.fromList $ nodes) /= (length nodes)
  where nodes = n : [ m | (_,m,_) <- path]



traceFrom :: Eq b => [b] -> AnnotatedPath b -> Maybe [b]
traceFrom stack     []                   = Just stack
traceFrom stack     ((n,m,Nothing):path) = traceFrom stack path
traceFrom []        ((n,m,Just (Close y)):path) = Nothing
traceFrom (x:stack) ((n,m,Just (Close y)):path)
  | x == y    = traceFrom stack path
  | otherwise = Nothing
traceFrom stack ((n,m,Just (Open x)):path) = traceFrom (x:stack) path

traceArbitrary :: Eq b => [b] -> [b] -> AnnotatedPath b -> Maybe ([b],  [b])
traceArbitrary    stack     stack'                         []   = Just             (stack,   stack')
traceArbitrary    stack     stack'  ((n,m,Nothing)       :path) = traceArbitrary    stack    stack'  path
traceArbitrary       []     stack'  ((n,m,Just (Close y)):path) = traceArbitrary       [] (y:stack') path
traceArbitrary (x:stack)    stack'  ((n,m,Just (Close y)):path)
  | x == y                                                      = traceArbitrary    stack    stack'  path
  | otherwise                                                   = Nothing
traceArbitrary    stack         []  ((n,m,Just (Open  y)):path) = traceArbitrary (y:stack)      []   path
traceArbitrary    stack  (x:stack') ((n,m,Just (Open  y)):path)
  | x == y                                                      = traceArbitrary    stack    stack'  path
  | otherwise                                                   = Nothing



realizableFrom :: Eq b => [b] -> AnnotatedPath b -> Bool
realizableFrom stack path = isJust $ traceFrom stack path


realizableArtbitrary :: Eq b => AnnotatedPath b -> Bool
realizableArtbitrary path = isJust $ traceArbitrary [] [] path


sameLevelFrom :: Eq b => [b] -> AnnotatedPath b -> Bool
sameLevelFrom stack path = case traceFrom stack path of
  Just newStack -> stack == newStack
  _             -> False


sameLevelArbitrary :: Eq b => AnnotatedPath b -> Bool
sameLevelArbitrary path = case traceArbitrary [] [] path of
  Just ([], []) -> True
  _             -> False


loopsIn :: forall b. (Eq b, Show b) =>  AnnotatedPath b -> [AnnotatedPath b ]
loopsIn               [] = []
loopsIn path@((n,_,_):_) = fmap reverse $ loopsInSeen (Set.fromList [n]) [(n,n,Nothing)] path
  where  loopsInSeen :: Set Node -> AnnotatedPath b -> AnnotatedPath b -> [AnnotatedPath b]
         loopsInSeen seen finished []                  = []
         loopsInSeen seen finished ((le@(n,m,_)):path)
            | m ∈ seen  = prefixes le finished ++ (loopsInSeen               seen  (le:finished) path)
            | otherwise =                          loopsInSeen (Set.insert m seen) (le:finished) path

         prefixes :: (LEdge (Annotation b)) -> AnnotatedPath b -> [AnnotatedPath b]
         prefixes le@(_,x,_)       [] = []
         prefixes le@(_,x,_) finished = case span (\(n,m,_) -> m /= x) finished of
             (left, (_,x',_):right) -> assert (x==x') $
                                       (case (le : left) of
                                          [(1,4,_),(4,5,_),(5,6,_),(0,1,_),(1,2,_),(2,0,_),(0,1,_)] ->
                                               traceShow (le, finished)
                                          _ -> id
                                       ) $ 
                                       (le : left) : (fmap (\r' -> (le:left) ++ r') (prefixes le right))
             (left, [])             -> []


sameLevelAlignable :: Eq b =>  AnnotatedPath b -> Bool
sameLevelAlignable path = (∃) (rotations path) (\path -> sameLevelFrom [] path)

data DynamicContext b = DynamicContext { node :: Node, stack :: [b] }
  deriving (Eq, Ord, Show)
contextsFrom :: (Eq b, DynGraph gr, Ord b) => gr a (Annotation b) -> Node -> Set (DynamicContext b)
contextsFrom g n =
     (㎲⊒) (Set.fromList [ DynamicContext { node = n, stack = [] } ]) f
  where f contexts = contexts
                   ⊔ Set.fromList [  DynamicContext { node = m , stack = stack }
                                           | c@(DynamicContext { node, stack })  <- Set.toList contexts,
                                             (m, Nothing) <- lsuc g node
                     ]
                   ⊔ Set.fromList [  DynamicContext { node = m , stack = x:stack }
                                           | c@(DynamicContext { node, stack })  <- Set.toList contexts,
                                             (m, Just (Open x)) <- lsuc g node
                     ]
                   ⊔ Set.fromList [  DynamicContext { node = m , stack = stack0 }
                                           | c@(DynamicContext { node, stack })  <- Set.toList contexts,
                                             (x:stack0) <- [stack],
                                             (m, Just (Close x')) <- lsuc g node,
                                             x == x'
                     ]


contextGraphFrom :: (Eq b, DynGraph gr, Ord b) =>
   gr a (Annotation b) ->
   Node ->
   Map (DynamicContext b) (Set (DynamicContext b, Annotation b))
contextGraphFrom g n0 =
     (㎲⊒) (Map.fromList [ (c0, Set.empty)]) f
  where c0 = DynamicContext { node = n0, stack = [] } 
        f successors = successors
                -- ⊔ (∐) [ (Set.fromList [c'], Map.fromList [(c, Set.fromList [ (Nothing, c')])]) 
                --                            | c@(DynamicContext { node, stack })  <- Set.toList contexts,
                --                              (m, Nothing) <- lsuc g node,
                --                              let c' = DynamicContext { node = m , stack = stack }
                --       ]
                ⊔  (∐) [    Map.fromList [ (c,  Set.fromList [(c', Nothing)]) ]
                          ⊔ Map.fromList [ (c', Set.empty) ] 
                                   | c@(DynamicContext { node, stack }) <- Map.keys successors,
                                     (m, Nothing) <- lsuc g node,
                                     let c' = DynamicContext { node = m , stack = stack }
                      ]
                ⊔ (∐) [     Map.fromList [ (c,  Set.fromList [(c', Just (Open x))]) ]
                          ⊔ Map.fromList [ (c', Set.empty) ]
                                   | c@(DynamicContext { node, stack })  <- Map.keys successors,
                                     (m, Just (Open x)) <- lsuc g node,
                                     let c' = DynamicContext { node = m , stack = x:stack }
                      ]
                ⊔ (∐) [     Map.fromList [ (c,  Set.fromList [(c', Just (Close x'))] ) ]
                          ⊔ Map.fromList [ (c', Set.empty) ]
                                   | c@(DynamicContext { node, stack })  <- Map.keys successors,
                                     (x:stack0) <- [stack],
                                     (m, Just (Close x')) <- lsuc g node,
                                     x == x',
                                     let c' = DynamicContext { node = m , stack = stack0 }
                     ]
