{-# LANGUAGE FlexibleInstances, ScopedTypeVariables #-}

module Data.Graph.Inductive.Query.BalancedSCC where
import Data.Time

import Debug.Trace
import Util

import Algebra.Lattice

import Unicode

import Data.Maybe(fromJust)

import Data.List(union, intersect, elem, delete, sort, (\\), nub)

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

data Parantheses b = Open b | Close b deriving (Ord, Eq, Show)
type Annotation b = Maybe (Parantheses b)

data   InterGraph a b = InterGraph (Gr a (Annotation b)) deriving (Show)

instance Arbitrary (Parantheses String) where
    arbitrary = sized $ \n ->
                  do p <- elements ["a", "b", "c"]
                     oc <- elements [Open, Close]
                     return $ oc p

instance Arbitrary (InterGraph () String) where
  arbitrary = sized $ \s ->
                 do (g :: Gr () ()) <- resize s arbitrary
                    edges <- mapM (\(n,n',()) ->
                      do (oc :: Maybe (Parantheses String)) <- resize s arbitrary
                         return (n,n',oc)
                     ) (labEdges g)
                    return $ InterGraph $ mkGraph (labNodes g) edges


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
        balancedSccs = sameLevelScc $ sameLevelSummaryGraph $ toBalanced $ gr



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
-- balancedScc :: DynGraph gr => gr a (Annotation b) -> Map Node [Node]
-- balancedScc :: bscc parenstack sccsOf unvisited 

--   w


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
 Set.fromList vr ∪ Set.fromList vl ∪ (∐) [ ms | (n,n',ms) <- labEdges summary, n `elem` (vr ++ vl), n' `elem` (vr ++ vl)]
    where w  = (funbr summary graph [s]) `intersect` (bunbl summary graph [t])
          vr = (funbr summary graph [s]) `intersect` (bunbr summary graph w  )
          vl = (funbl summary graph w  ) `intersect` (bunbl summary graph [t])


simulUnbr summary gr =
    (㎲⊒) (  Map.fromList [ ((n,m),if n==m then Set.fromList [n] else Set.empty) | n <- nodes gr, m <- nodes gr])
          (\ch ->
             ch
           ⊔ Map.fromList [ ((n,m),  (∐) [ if (Set.null $ ch ! (n', m)) then Set.empty else ch ! (n',m) ⊔  ch ! (n,n)   | n' <- successors n]) | n <- nodes gr, m <- nodes gr ]
          )
    where successors n = nub $
                            [n' | (n',Nothing)          <- lsuc gr n]
                         ++ [n' | (n', Just (Close _))  <- lsuc gr n]
                         ++ [n' | (n', ms)              <- lsuc summary n, not $ Set.null ms]


simulUnbl summary gr =
    (㎲⊒) (  Map.fromList [ ((n,m),if n==m then Set.fromList [n] else Set.empty) | n <- nodes gr, m <- nodes gr])
          (\ch ->
             ch
           ⊔ Map.fromList [ ((n,m),  (∐) [ if (Set.null $ ch ! (n', m)) then Set.empty else ch ! (n',m) ⊔  ch ! (n,n)   | n' <- successors n]) | n <- nodes gr, m <- nodes gr ]
          )
    where successors n = nub $
                            [n' | (n',Nothing)          <- lsuc gr n]
                         ++ [n' | (n', Just (Open _))   <- lsuc gr n]
                         ++ [n' | (n', ms)              <- lsuc summary n, not $ Set.null ms]


simulBalancedChop gr =  Map.fromList [((n,m),  updown ! (n,m) ⊔ (∐) [ ms | (n',m',ms) <- labEdges summary, n' ∈ updown ! (n,m), m' ∈ updown ! (n,m)])
                                     | n <- nodes gr, m <- nodes gr]
  where
        updown = Map.fromList [ ((n,m), (∐) [ if ((Set.null $ unbr ! (n,n')) || (Set.null $ unbl ! (n',m))) then Set.empty else unbr ! (n,n') ⊔  unbl ! (n',m)   | n' <- nodes gr]) 
                              | n <- nodes gr, m <- nodes gr ]

        summary = sameLevelSummaryGraph gr
        unbr = simulUnbr summary gr
        unbl = simulUnbl summary gr


simulUnbrIsUnbr ::  Gr () (Annotation String) -> Bool
simulUnbrIsUnbr gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (Set.fromList $ funbr summary gr [s])  ∩
             (Set.fromList $ bunbr summary gr [t])   == (simul ! (s,t))
      )
    )
  where simul = simulUnbr summary gr
        summary = sameLevelSummaryGraph gr


simulUnblIsUnbl ::  Gr () (Annotation String) -> Bool
simulUnblIsUnbl gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (Set.fromList $ funbl summary gr [s])  ∩
             (Set.fromList $ bunbl summary gr [t])   == (simul ! (s,t))
      )
    )
  where simul = simulUnbl summary gr
        summary = sameLevelSummaryGraph gr


balancedChopIsSimulBalancedChop ::  Gr () (Annotation String) -> Bool
balancedChopIsSimulBalancedChop gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (balanced s t) == (simul ! (s,t))
      )
    )
  where simul = simulBalancedChop gr
        balanced = balancedChop summary gr
        summary = sameLevelSummaryGraph gr

rofl = do
    InterGraph gr <- generate $ resize 150  (arbitrary :: Gen (InterGraph () String))

    start <- getCurrentTime
    putStrLn $ show (summe $ Map.toList $ fmap (Set.size) $ simulBalancedChop gr)
    stop  <- getCurrentTime
    print $ diffUTCTime stop start

    start <- getCurrentTime
    let summary = sameLevelSummaryGraph gr
    putStrLn $ show (summe $ [ ((s,t),Set.size ms) | (s,t,ms) <- labEdges summary ])
    stop <- getCurrentTime
    print $ diffUTCTime stop start

    start <- getCurrentTime
    putStrLn $ show (summe $ [ ((s,t),Set.size $ balancedChop summary gr s t) | s <- nodes gr, t <- nodes gr])
    stop <- getCurrentTime
    print $ diffUTCTime stop start


  where summe l = sum $ fmap (\((a,b),c) -> a+b+c) l
