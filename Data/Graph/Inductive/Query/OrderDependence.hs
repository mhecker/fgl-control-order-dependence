{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert
#define PDOMUSESDF
module Data.Graph.Inductive.Query.OrderDependence where

import Control.Exception.Base (assert)

import Control.Monad (forM, forM_)

import Data.List(partition)
import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Control.Monad.ST
import Data.STRef

import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)
import Data.Dequeue.SimpleDequeue (SimpleDequeue)

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd



import Data.Graph.Inductive
import qualified Data.Graph.Inductive.Query.DFS (reachable)

import Unicode
import Util(foldM1, the, fromSet, toSet, invert', invert'', invert''', without, isReachableFromTreeM, reachableFromTree, reachableFrom, fromIdom, fromIdomM, restrict)

import Data.Graph.Inductive.Util (delSuccessorEdges, nextCondNode, toNextCondNode, fromSuccMap, controlSinks)
import Data.Graph.Inductive.Query.LCA(lca)
import Data.Graph.Inductive.Query.PostDominance (MaximalPath (..), inPathFor, onedomOf, isinkdomOfTwoFinger8DownSingleNodeSinks, isinkdomOftwoFinger8Up, isinkdomOfTwoFinger8, imdomOfTwoFinger7, maximalPathsFor, isinkdomOfTwoFinger8ForSinks)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges (idfViaCEdgesFastForCycles)
import Data.Graph.Inductive.Query.PostDominanceFrontiers.Numbered (isinkDFNumberedForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (idomToDFFastForRoots, mDFTwoFinger, isinkDFTwoFinger)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import Data.Graph.Inductive.Query.NTICD (snmF3, snmF3Lfp, isinkdomOfSinkContraction, ntscdF3, nticdF3)




inPathForBefore :: DynGraph gr => gr a b -> Map Node [(Node, [Node])] -> (Node,Node) -> (Node, MaximalPath) -> Bool
inPathForBefore graph' doms (m1,m2) (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  thispath@(MaximalPath []            endScc endNodes@(end:_))
                    | m1 ∊ endScc  = -- traceShow (entries, thispath) $ 
                                          (∀) entries (\entry -> let domsEnd = (doms ! entry) `get` end
                                                                     domsm2   = (doms ! entry) `get` m2 in
                                                                 (entry /= end || m1 == entry) && m1 ∊ domsEnd && ((not $ m2 ∊ endScc) ∨ (m1 ∊ domsm2))
                                          )
                                          ∨ ((m1 ∊ endNodes) ∧
                                             (∀) entries (\entry ->  let domsm2   = (doms ! entry) `get` m2 in ((not $ m2 ∊ endScc) ∨ (m1 ∊ domsm2)))
                                          )

                    | otherwise         = -- traceShow (entries, thispath) $
                                          False
                inPathFromEntries entries  thispath@(MaximalPath (scc:prefix)  endScc endNodes)
                    | m1 ∊ scc = -- traceShow (entries, thispath) $
                                      (∀) entries (\entry ->
                                        (∀) exits (\exit -> let domsexit = (doms ! entry) `get` exit 
                                                                domsm2   = (doms ! entry) `get` m2   in
                                             (entry /= exit || m1 == entry) && m1 ∊ domsexit && ((not $ m2 ∊ scc) ∨ (m1 ∊ domsm2))
                                        )
                                      )
                                      ∨
                                      ((m1 ∊ endNodes) ∧
                                       (∀) entries (\entry ->  let domsm2   = (doms ! entry) `get` m2 in ((not $ m2 ∊ scc) ∨ (m1 ∊ domsm2)))
                                      )
                    | otherwise    =  -- traceShow (entries, thispath) $
                                      (not $ m2 ∊ scc) ∧ inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = case  List.lookup key assocs of
                                   Nothing -> error $ "lookup " ++ (show key) ++ "  " ++ (show assocs)
                                   Just v  -> v



mayInPathForBefore :: DynGraph gr => gr a b -> Map Node [(Node, [Node])] -> (Node,Node) -> (Node, MaximalPath) -> Bool
mayInPathForBefore graph' doms (m1,m2) (s, path) = inPathFromEntries [s] path
          where 
                inPathFromEntries entries  thispath@(MaximalPath []            endScc endNodes@(end:_))
                    | m1 ∊ endScc ∧ m2 ∊ endScc  = -- traceShow (entries, thispath) $
                                      (∃) entries (\entry -> let domsm1 = (doms ! entry) `get` m1 in
                                                             not $ m2 ∊ domsm1
                                      )
                    | m1 ∊ endScc  = -- traceShow (entries, thispath) $
                                          True
                    | otherwise         = -- traceShow (entries, thispath) $
                                          False
                inPathFromEntries entries  thispath@(MaximalPath (scc:prefix)  endScc endNodes)
                    | m1 ∊ scc ∧ m2 ∊ scc = -- traceShow (entries, thispath) $
                                      (∃) entries (\entry -> let domsm1 = (doms ! entry) `get` m1 in
                                                             not $ m2 ∊ domsm1
                                      )
                    | m1 ∊ scc = -- traceShow (entries, thispath) $
                                      True
                    | m2 ∊ scc = -- traceShow (entries, exits, thispath) $
                                      (∃) entries (\entry ->
                                        (∃) exits (\exit -> let domsexit = (doms ! entry) `get` exit in
                                                                not $ m2 ∊ domsexit
                                        )
                                      )
                                    ∧ inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                    | otherwise     = -- traceShow (entries, thispath) $
                                      inPathFromEntries [ n' | (_,n') <- borderEdges ] (MaximalPath prefix endScc endNodes)
                  where next =  if (null prefix) then endScc else head prefix
                        borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
                        exits = [ n | (n,_) <- borderEdges ]
                get assocs key = case  List.lookup key assocs of
                                   Nothing -> error $ "lookup " ++ (show key) ++ "  " ++ (show assocs)
                                   Just v  -> v





mustBeforeMaximalDef :: (DynGraph gr) => gr a b -> Map Node (Set (Node, Node))
mustBeforeMaximalDef graph =
                Map.fromList [ (n, Set.empty) | n <- nodes graph]
              ⊔ Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- nodes graph,
                                                            m2 <- nodes graph,
                                                            n /= m1, n /= m2, m1 /= m2,
                                                            (∀) paths (\path -> (m1,m2) `inPathBefore` (n,path))
                                                ]
                               ) | n <- nodes graph, let paths = maximalPaths ! n ]
  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        inPathBefore = inPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.






type T n = (n, n)

type SmmnFunctional = Map (Node,Node,Node) (Set (T Node)) -> Map (Node,Node,Node) (Set (T Node))
type SmmnFunctionalGen gr a b = gr a b -> [Node] -> (Map Node (Set Node)) -> (Node -> Maybe Node) -> (Node -> [Node]) -> SmmnFunctional


fMust :: DynGraph gr => SmmnFunctionalGen gr a b
fMust graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     m1 ∈ (reachable ! x)
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]


fMustNoReachCheck :: DynGraph gr => SmmnFunctionalGen gr a b
fMustNoReachCheck graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX
                                                                     -- m1 ∊ (reachable x)
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]




fMustBefore :: DynGraph gr => SmmnFunctionalGen gr a b
fMustBefore graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                            m1 ∈ (reachable ! x),
                                                                      not $ m2 ∈ (reachable ! x)
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     Just n <- [nextCond x], 
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     m1 ∈ (reachable ! x),
                                                                     s ! (m1,m2,n) ⊇ Set.fromList [ (n, y) | y <- suc graph n, m2 ∈ (reachable ! y) ]
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]



fMay :: DynGraph gr => SmmnFunctionalGen gr a b
fMay graph condNodes reachable nextCond toNextCond s = 
                   Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- suc graph p,
                                                                      let toNxtCondX = toNextCond x,
                                                                      m1 ∊ toNxtCondX,
                                                                      not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                                                          ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes]
                ⊔ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     let toNxtCondX = toNextCond x,
                                                                     m1 ∈ (reachable ! x),
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) > 0
                                               ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]


fMay' :: DynGraph gr => SmmnFunctionalGen gr a b
fMay' graph condNodes reachable nextCond toNextCond s =
              (∐) [ Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) ])]
                                | p <- condNodes,
                                  x <- suc graph p,
                                  let toNxtCondX = toNextCond x,
                                  m1 <- toNxtCondX,
                                  m2 <- nodes graph,
                                  not $ m2 ∊ (m1 : (takeWhile (/= m1) $ reverse toNxtCondX))
                  ]
           ⊔      Map.fromList [ ((m1,m2,p), Set.fromList  [ (p,x) | x <- (suc graph p),
                                                                     let toNxtCondX = toNextCond x,
                                                                     not $ m2 ∊ toNxtCondX,
                                                                     Just n <- [nextCond x], 
                                                                     (Set.size $ s ! (m1,m2,n)) > 0
                                             ]
                                  ) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes
                  ]



type MustFunctional = Map Node (Set (Node, Node)) -> Map Node (Set (Node, Node))
type MustFunctionalGen gr a b = gr a b -> MustFunctional

mustOfLfp :: DynGraph gr => gr a b -> Map Node (Set (Node, Node))
mustOfLfp graph = (㎲⊒) init (fMustNaive graph)
  where init = Map.fromList [ (n, Set.empty) | n <- nodes graph]


mustOfGfp :: DynGraph gr => gr a b -> Map Node (Set (Node, Node))
mustOfGfp graph = (𝝂) init (fMustNaive graph)
  where init = Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- reachable n graph, m2 <- nodes graph]) | n <- nodes graph ]


fMustNaive :: DynGraph gr => MustFunctionalGen gr a b
fMustNaive graph  must =
                      Map.fromList [ (n, Set.fromList [(n,m2) | m2 <- nodes graph, m2 /= n ])                                             | n <- nodes graph]
                    ⊔ Map.fromList [ (n, Set.fromList [(m1,m2) | (m1,m2) <- Set.toList $ (∏) [ must ! x | x <- suc graph n ], m2 /= n])   | n <- nodes graph, suc graph n /= []]




wodTEIL :: (DynGraph gr) => gr a b -> Map Node (Set (Node,Node))
wodTEIL graph = xodTEIL smmnMustBefore smmnMay graph
  where smmnMustBefore = smmnFMustWodBefore graph
        smmnMay  = smmnFMayWod graph


mmay :: (Graph gr) => gr a b -> Node -> Node -> Node -> Bool
mmay graph m2 m1 x =   (not $ m2 `elem` reachable x graph)
                     ∧ (      m1 `elem` reachable x graph)

mmayOf :: (DynGraph gr) => gr a b -> Node -> Map Node (Set Node)
mmayOf graph = \m2 ->
           let reachM2 = Set.fromList $ reachable m2 g' 
           in Map.fromSet (\x -> Set.empty) reachM2  `Map.union` reach
  where g' = grev graph
        reach = Map.fromList [(x, Set.fromList $ reachable x graph) | x <- nodes graph ]


mmayOf' :: (DynGraph gr) => gr a b -> Node -> Map Node (Set Node)
mmayOf' graph = \m1 ->   Map.fromList [ (x, Set.fromList [ m2 | m2 <- nodes graph, not $ m2 ∈ reach ! x ]) | x <- reachable m1 g' ]
                       ⊔ Map.fromList [ (x, Set.empty) | x <- nodes graph ]
  where g' = grev graph
        reach = Map.fromList [(x, Set.fromList $ reachable x graph) | x <- nodes graph ]


wodTEIL'PDom :: (DynGraph gr) => gr a b -> Map (Node, Node) (Set Node)
wodTEIL'PDom graph  =
     assert (unreachable == unreachableLeftDef ⊔ unreachableRightDef) $
     unreachable ⊔ nticd
  where nticd       = convert [ (n, m1, m2)  | m2 <- nodes graph,
                                               let gM2    = delSuccessorEdges graph m2,
                                               let gToM2  = subgraph (reachable m2 (grev gM2)) gM2,
                                               let nticd' = isinkDFNumberedForSinks [[m2]] gToM2,
                                               (m1, ns) <- Map.assocs nticd', n <- Set.toList ns, n /= m1
                      ]

        unreachable = convert [ (n, m1, m2) | n <- Set.toList condNodes,
                                              m2 <- Set.toList $ reach ! n, m2 /= n,
                                              m1 <- Set.toList $ (Set.unions [ reach ! x | x <- suc graph n, not $ m2 ∈ reach ! x ]) , m1 /= n, m1 /= m2
                      ]
          where reach = Map.fromList [(x, Set.fromList $ reachable x graph) | x <- nodes graph ]
                graph' = grev graph
                condNodes = Set.fromList [ n | n <- nodes graph, length (suc graph n) > 1 ]


        unreachableLeftDef = Map.fromList [ ((m1, m2), Set.fromList [ n | n <- nodes graph,  n /= m1, n /= m2,
                                                              assert ( (not $ m1 ∈ m2may ! n) ↔ (not $ m1 ∈ m2onedom n)) True,
                                                                       (not $ m1 ∈ m2may ! n),
                                                                       (∃) (suc graph n) (\x ->       m1 ∈ m2may ! x)
                                                ]
                                     ) | m2 <- nodes graph,
                                         let m2may = mmay m2,
                                         let m2onedom = onedomOf m2may,
                                         m1 <- nodes graph, m1 /= m2
                    ]
          where mmay = mmayOf graph

        unreachableRightDef = Map.fromList [ ((m2, m1), ns) | ((m1,m2),ns) <- Map.assocs unreachableLeftDef]


        convert :: [(Node, Node, Node)] ->  Map (Node,Node) (Set Node)
        convert triples = runST $ do
            let keys = [ (m1,m2) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2]

            assocs <- forM keys (\(m1,m2) -> do
              ns <- newSTRef Set.empty
              return ((m1,m2),ns)
             )

            let m = assert (List.sort keys == keys)
                  $ Map.fromDistinctAscList assocs

            forM_ triples (\(n,m1,m2) -> do
               let nsRef  = m ! (m1,m2)
               let nsRef' = m ! (m2,m1)
               modifySTRef nsRef  (Set.insert n)
               modifySTRef nsRef' (Set.insert n)
             )

            m' <- forM m readSTRef

            return m'


wodTEIL' :: (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
wodTEIL' graph = Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
               ⊔ (fmap Set.fromList $ invert' $ fmap Set.toList wTEIL )
  where wTEIL = wodTEIL graph



smmnFMustWod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustWod graph = smmnGfp graph fMust

smmnFMustWodBefore :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustWodBefore graph = smmnGfp graph fMustBefore


smmnFMayWod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMayWod graph = smmnLfp graph fMay'


smmnFMustDod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustDod graph = smmnLfp graph fMust

smmnFMustNoReachCheckDod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMustNoReachCheckDod graph = smmnLfp graph fMustNoReachCheck


smmnFMayDod :: (DynGraph gr) => gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnFMayDod graph = smmnLfp graph fMay'




smmnGfp :: (DynGraph gr ) => gr a b -> SmmnFunctionalGen gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnGfp graph f = -- traceShow graph $ 
                  (𝝂) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m1,m2,p), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]
                 ⊔ Map.fromList [ ((m1,m2,p), Set.fromList [ (p,x) | x <- suc graph p]) | m1 <- nodes graph, m2 <- nodes graph, m2 /= m1, p <- condNodes]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable = Map.fromList [(x, Set.fromList $ Data.Graph.Inductive.Query.DFS.reachable x graph) | x <- nodes graph] 
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

smmnLfp :: (DynGraph gr) => gr a b -> SmmnFunctionalGen gr a b -> Map (Node, Node, Node) (Set (T Node))
smmnLfp graph f = -- traceShow graph $ 
                  (㎲⊒) smnInit (f graph condNodes reachable nextCond toNextCond)
  where smnInit =  Map.fromList [ ((m1,m2,p), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, p <- condNodes ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable = Map.fromList [(x, Set.fromList $ Data.Graph.Inductive.Query.DFS.reachable x graph) | x <- nodes graph] 
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

{- a combinator to generate order dependencies in the style of [2]

  [2] Slicing for modern program structures: a theory for eliminating irrelevant loops
      TorbenAmtoft
      https://doi.org/10.1016/j.ipl.2007.10.002
-}
xodTEIL:: DynGraph gr => (Map (Node, Node, Node ) (Set (T Node))) ->
                         (Map (Node, Node, Node ) (Set (T Node))) ->
                         gr a b ->
                         Map Node (Set (Node,Node))
xodTEIL smmnMustBefore smmnMay graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ (m1,m2) | m1 <- nodes graph,
                                                  m2 <- nodes graph,
                                                  Set.size (smmnMay ! (m1,m2,n)) > 0, n /= m2,
                                                  Set.size (smmnMay ! (m2,m1,n)) > 0, n /= m1,
                                                  let s12n = smmnMustBefore ! (m1,m2,n),
                                                  let s21n = smmnMustBefore ! (m2,m1,n),
                                                  Set.size s12n + Set.size s21n > 0
                                      ]
                     ) | n <- condNodes
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


{- a combinator to generate order dependencies in the style of [1] -}
xod smmnMust s graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  Set.size (s ! (m1,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  Set.size (s ! (m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  let s12n = smmnMust ! (m1,m2,n),
                                                  let s21n = smmnMust ! (m2,m1,n),
                                                  Set.size s12n > 0,
                                                  Set.size s21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


myXod smmnMust s graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  Set.size (s ! (m1,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  Set.size (s ! (m2,n)) == (Set.size $ Set.fromList $ suc graph n),
                                                  let s12n = smmnMust ! (m1,m2,n),
                                                  Set.size s12n > 0,
                                                  Set.size s12n < (Set.size $ Set.fromList $ suc graph n)
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



myWod graph = myXod sMust s3 graph
  where sMust = smmnFMustWod graph
        s3    = snmF3 graph

myWodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myWodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- isinkdomCycles,
                                       let conds   = condsIn    cycle,
                                       let entries = entriesFor cycle,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       let color = colorLfpFor graph m1 m2,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entries  ++ cycle,
                                                                   n /= m1 ∧ n /= m2,
                                                           assert (m1 ∊ (suc isinkdomTrc n)) True,
                                                           assert (m2 ∊ (suc isinkdomTrc n)) True,
                                                                   myDependence color n
                                                                  -- let s12n = sMust ! (m1,m2,n),
                                                                  -- Set.size s12n > 0,
                                                                  -- Set.size s12n < (Set.size $ Set.fromList $ suc graph n)
                                                ]
                  ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]
        condsIn cycle    = [ n | n <- cycle, length (suc graph n) > 1]
        myDependence = myDependenceFor graph



rotatePDomAroundNeighbours :: forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> Map Node (Maybe Node) -> (Node, Node) -> Map Node (Maybe Node)
rotatePDomAroundNeighbours  graph condNodes pdom e@(n,m) =
      id
    $ require (n /= m)
    $ require (hasEdge graph e)
    $ require (pdom  ! n == Nothing)
    $ assert  (nodes graphm == (nodes $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (edges graphm == (edges $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (pdom' ! m == Nothing)
    $ pdom'
  where graphm = delSuccessorEdges graph m
        preM = Set.fromList $ pre graph m
        pdom'0   = id
                 $ Map.union (Map.fromSet (const $ Just m) $ Set.delete m preM)
                 $ ipdomM''
        ipdomM'' = Map.insert m Nothing
                 $ pdom
        pdom' = id
              -- $ traceShow pdom'0 
              -- $ traceShow [ (n, sol, pd) | (n,sol) <- Map.assocs $ toSuccMap $ (immediateOf solution :: gr () ()),
              --                              let pd = pdom'0 ! n, pd /= sol]
              $ assert ((∀) (nodes graph) (\x ->
                                   if isReachableFromTreeM ipdomM'' n x   ∧  (not $ x ∈ preM) then
                                             reachableFromTree  (fmap toSet pdom'0) x
                                          ⊇  reachableFromTree             solution x
                                   else 
                                             reachableFromTree  (fmap toSet pdom'0) x
                                         ==  reachableFromTree             solution x
                                       )
                       )
              $ if ((∀) preM (\p -> p == n)) then
                    id
                  $ pdom'0
                else
                    id 
                  $ isinkdomOfTwoFinger8DownSingleNodeSinks graphm (Set.fromList [m]) relevantCondNodesM pdom'0
          where 
                condNodesM = Map.delete m condNodes
                relevantCondNodesM = assert (fromFind == slow) $
                                     fromFind
                  where slow     = Map.filterWithKey (\x _ -> isReachableFromTreeM ipdomM'' n x    ∧   (not $ x ∈ preM)) condNodesM
                        fromFind = findAll (Set.toList $ (Map.keysSet condNodesM) ∖ preM) Map.empty
                          where findAll     [] relevant = relevant
                                findAll (x:xs) relevant = find [x] xs relevant
                                find []         [] relevant = relevant
                                find path@(x:_) xs relevant
                                    | x == n                 = find path'     xs' relevant'
                                    | Map.member x relevant  = find path'     xs' relevant'
                                    | otherwise = case ipdomM'' ! x of
                                                    Nothing -> find path'     xs' relevant
                                                    Just x' -> find (x':path) xs  relevant
                                  where (path', xs') = case xs of
                                                         []     -> ([], [])
                                                         (y:ys) -> ([y], ys)
                                        relevant' = foldr (uncurry Map.insert) relevant [ (y,succs) | y <- path, not $ y ∈ preM, Just succs <- [Map.lookup y condNodesM] ]


                solution = fromIdom m $ iDom (grev graphm) m



rotatePDomAroundArbitrary :: forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> Map Node (Maybe Node) -> (Node, Node) -> Map Node (Maybe Node)
rotatePDomAroundArbitrary  graph condNodes ipdom (n, m) = 
      id
    $ require (n /= m)
    $ require (ipdom  ! n == Nothing)
    $ assert  (nodes graphm == (nodes $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (edges graphm == (edges $ efilter (\(x,y,_) -> x /= m) graph))
    $ assert  (ipdom' ! m == Nothing)
    $ ipdom'

  where ipdomM''  = Map.insert m Nothing ipdom
        succs     = [ x | x <- suc graph n, isReachableFromTreeM ipdomM'' m x]
        graphm = delSuccessorEdges graph m
        condNodesM = Map.delete m condNodes

        ipdom' = assert ((∀) (nodes graph) (\x ->
                                   if isReachableFromTreeM ipdomM'' n x then
                                             reachableFromTree  (fmap toSet ipdomM''') x
                                          ⊇  reachableFromTree                solution x
                                   else 
                                             reachableFromTree  (fmap toSet ipdomM''') x
                                         ==  reachableFromTree                solution x
                                       )
                       )
               $ assert (relevantCondNodesM == Map.filterWithKey (\x _ -> isReachableFromTreeM ipdomM'' n x) condNodesM)
               $ isinkdomOfTwoFinger8DownSingleNodeSinks graphm (Set.fromList [m]) relevantCondNodesM ipdomM'''

        (relevantCondNodesM, ipdomM''') = 
                if List.null succs then
                  let (processed0, relevantCondNodesM) = findProcessedAndRelevant (nodes graphm) (Set.singleton m) Map.empty
                      ipdomM''' = isinkdomOftwoFinger8Up graphm condNodesM worklist0 processed0 imdom0Rev imdom0
                        where nIsCond    = Map.member n condNodes
                              [nx]       = suc graphm n
                              imdom0     = (if nIsCond then id else Map.insert n (Just nx)) $
                                           (fmap (const Nothing) relevantCondNodesM) `Map.union` ipdomM''
                              imdom0Rev  = invert''' imdom0
                              worklist0  = Dequeue.fromList $ Map.assocs relevantCondNodesM
                  in assert (processed0 == Set.fromList [ x | x <- nodes graph, isReachableFromTreeM ipdomM'' m x ]) $
                     (relevantCondNodesM, ipdomM''')
                else
                   let relevantCondNodesM = findRelevant (Map.keys condNodesM) Map.empty
                       ipdomM''' = assert (z /= Nothing) $ Map.insert n z ipdomM''
                         where z = foldM1 (lca ipdomM'') succs
                  in (relevantCondNodesM, ipdomM''')


        findProcessedAndRelevant (x:xs) processed relevant = find [x] xs processed relevant
                  where find []         [] processed relevant =  (processed, relevant)
                        find path@(x:_) xs processed relevant
                            | Map.member x   relevant  = find path'     xs' processed  relevant'
                            |            x ∈ processed = find path'     xs' processed' relevant
                            | otherwise = case ipdomM'' ! x of
                                            Nothing ->   find path'     xs' processed  relevant'
                                            Just x' ->   find (x':path) xs  processed  relevant
                          where (path', xs') = case xs of
                                                []     -> ([], [])
                                                (y:ys) -> ([y], ys)
                                processed' = foldr          Set.insert  processed                    path
                                relevant'  = foldr (uncurry Map.insert) relevant  [ (y,succs) | y <- path, Just succs <- [Map.lookup y condNodesM] ]

        findRelevant     [] relevant =             relevant
        findRelevant (x:xs) relevant = find [x] xs relevant
                  where find []         [] relevant = relevant
                        find path@(x:_) xs relevant
                            | x == n                 = find path'     xs' relevant'
                            | Map.member x relevant  = find path'     xs' relevant'
                            | otherwise = case ipdomM'' ! x of
                                            Nothing -> find path'     xs' relevant
                                            Just x' -> find (x':path) xs  relevant
                          where (path', xs') = case xs of
                                                []     -> ([], [])
                                                (y:ys) -> ([y], ys)
                                relevant' = foldr (uncurry Map.insert) relevant [ (y,succs) | y <- path, Just succs <- [Map.lookup y condNodesM] ]

        solution = fromIdom m $ iDom (grev graphm) m


rotatePDomAround :: forall gr a b. (DynGraph gr) => gr a b -> Map Node [Node] -> Map Node (Maybe Node) -> (Node, Node) -> Map Node (Maybe Node)
rotatePDomAround graph condNodes pdom nm
  | hasEdge graph nm = rotatePDomAroundNeighbours  graph condNodes pdom nm
  | otherwise        = rotatePDomAroundArbitrary   graph condNodes pdom nm



myWodFastPDomForIterationStrategy :: forall gr a b. (DynGraph gr) => (gr a b -> [Node] -> [[Node]]) -> gr a b -> Map (Node,Node) (Set Node)
myWodFastPDomForIterationStrategy strategy graph =
        convert $
        [ (n,m1,m2)  |                                        cycle <- isinkdomCycles, length cycle > 1,
                                                              let cycleS = Set.fromList cycle,
                                                              let entries = entriesFor cycle,
                                                              let nodesTowardsCycle = dfs (head cycle : entries) graph,
                                                              let condsTowardCycle = condsIn nodesTowardsCycle,
                                                              let condsInCycle = restrict condsTowardCycle cycleS,
                                                              let cycleGraph0 = subgraph nodesTowardsCycle graph,
                                                              let nodesFromCycle = rdfs cycle cycleGraph0,
                                                              let cycleGraph = subgraph nodesFromCycle cycleGraph0,
                                                              let paths = strategy graph cycle,
                                                      require ( (∐) [ Set.fromList path | path <- paths] == Set.fromList cycle ) True,
                                                              let (m20:others) = concat paths,
                                                              let pairs = zip (m20:others) others,
                                                              let pdom0 = fromIdomM m20 $ iDom (grev cycleGraph) m20,
                                                              let pdoms = zip (m20:others) (scanl (rotatePDomAround cycleGraph condsTowardCycle) pdom0 pairs),
                                                              (m2, pdom) <- pdoms,
#ifdef PDOMUSESDF
                                                              let graph' = delSuccessorEdges cycleGraph m2,
                                                              (m1, ns) <- Map.assocs $ idomToDFFastForRoots [[m2]] graph' pdom,
                                                              m1 ∈ cycleS,
                                                              n <- Set.toList ns,
                                                              m1 /= n,
#else
                                                              n <- [ n | (n,_) <- Map.assocs condsInCycle] ++ entries,
                                                              let pdom' = fromIdomM m2  $ iDom (grev cycleGraph) m2,
                                                       assert (pdom == pdom') True,
                                                              n /= m2,
                                                              let (z,relevant) = lcaRKnownM pdom n (suc graph n),
                                                       assert (Just z == foldM1 (lca pdom) (suc graph n)) True,
                                                       assert (Set.fromList relevant == Set.fromList [ m1 | x <- suc graph n, m1 <- Set.toList $ (reachableFrom (fmap toSet pdom)  (Set.fromList [x])), isReachableBeforeFromTreeM pdom m1 z x ] ) True,
                                                              m1 <- relevant, m1 /= z,
                                                              m1 /= n,
                                                              m1 ∈ cycleS,
#endif
                                                       assert (m1 /= n) True,
                                                       assert (m2 /= n) True,
                                                       assert (m2 /= m1) True,
                                                       assert (m1 ∊ (suc isinkdomTrc n)) True,
                                                       assert (m2 ∊ (suc isinkdomTrc n)) True
      ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        convert :: [(Node, Node, Node)] ->  Map (Node,Node) (Set Node)
        convert triples = runST $ do
            let keys = [ (m1,m2) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2]

            assocs <- forM keys (\(m1,m2) -> do
              ns <- newSTRef Set.empty
              return ((m1,m2),ns)
             )

            let m = assert (List.sort keys == keys)
                  $ Map.fromDistinctAscList assocs

            forM_ triples (\(n,m1,m2) -> do
               let nsRef = m ! (m1,m2)
               modifySTRef nsRef (Set.insert n)
             )

            m' <- forM m readSTRef

            return m'

        isinkdom = isinkdomOfTwoFinger8 graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]
        condsIn ns    = Map.fromList [ (n, succs) | n <- ns, let succs = suc graph n, length succs > 1]


-- towardsCycle graph cycleS n = dfs [n] graph


myWodFastPDom :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myWodFastPDom graph = myWodFastPDomForIterationStrategy none graph
  where none graph cycle = [ [n] | n <- cycle ]


myWodFastPDomSimpleHeuristic :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myWodFastPDomSimpleHeuristic graph = myWodFastPDomForIterationStrategy simple graph
  where simple :: gr a b -> [Node] -> [[Node]]
        simple graph cycle = from (joinNodes ++ nonJoinNodes) Set.empty []
          where (joinNodes, nonJoinNodes) = partition (\n -> length (pre graph n) > 1) cycle
                joinNodesSet = Set.fromList joinNodes
                from []        seen result = result
                from (n:nodes) seen result = from [ n | n <- nodes, not $ n ∈ seen' ] seen' (app newPath result)
                  where newPath = forward n seenN
                          where seenN   = (Set.insert n seen)
                        seen' = seen ∪ newSeen
                          where newSeen = Set.fromList newPath
                        app []      oldPaths = oldPaths
                        app newPath oldPaths = app' oldPaths
                          where newPathLast  = last newPath
                                app' [] = [newPath]
                                app' (oldPath@(oldPathFirst:oldPathRest) : oldPaths ) 
                                  | hasEdge graph (newPathLast, oldPathFirst) = (newPath ++ oldPath) : oldPaths
                                  | otherwise                                 = oldPath : app' oldPaths
                forward n seen 
                    | List.null succs        = [n]
                    | List.null nonJoinSuccs = let n' = head    joinSuccs in n : (forward n' (Set.insert n' seen))
                    | otherwise              = let n' = head nonJoinSuccs in n : (forward n' (Set.insert n' seen))
                  where succs = [ m | m <- suc graph n, not $ m ∈ seen]
                        (joinSuccs, nonJoinSuccs) = partition (∈ joinNodesSet) succs

dod graph = xod sMust s3 graph
  where sMust = smmnFMustDod graph
        s3    = snmF3Lfp graph

myDod graph = myXod sMust s3 graph
  where sMust = smmnFMustDod graph
        s3    = snmF3Lfp graph


myDodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myDodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- imdomCycles,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       let color = colorLfpFor graph m1 m2,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entriesFor cycle,
                                                           assert (n /= m1 ∧ n /= m2) True,
                                                           assert (m1 ∊ (suc imdomTrc n)) True,
                                                           assert (m2 ∊ (suc imdomTrc n)) True,
                                                                  myDependence color n
                                                ]
                   ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        imdom = imdomOfTwoFinger7 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∊ cycle]
        myDependence = myDependenceFor graph

myDodFastPDom :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myDodFastPDom graph =
        convert $
        [ (n,m1,m2)  |                                        cycle <- imdomCycles, length cycle > 1,
                                                              let cycleS = Set.fromList cycle,
                                                              let entries = entriesFor cycleS, not $ entries == [],
                                                              let nodesTowardsCycle = dfs entries graph,
                                                              let cycleGraph0 = subgraph nodesTowardsCycle graph,
                                                              let nodesFromCycle = rdfs cycle cycleGraph0,
                                                              let cycleGraph = subgraph nodesFromCycle cycleGraph0,
                                                              m2 <- cycle,
                                                              let graph' = delSuccessorEdges cycleGraph m2,
                                                              let pdom = fmap fromSet $ imdomOfTwoFinger7 graph',
#ifdef PDOMUSESDF
                                                              (m1, ns) <- Map.assocs $ idomToDFFastForRoots [[m2]] graph' pdom,
                                                              m1 ∈ cycleS,
                                                              n <- Set.toList ns,
#else
                                                              n <- entries,
                                                              let (z,relevant) = lcaRKnownM pdom n (suc graph n),
                                                       assert (Just z == foldM1 (lca pdom) (suc graph n)) True,
                                                       assert (Set.fromList relevant == Set.fromList [ m1 | x <- suc graph n, m1 <- Set.toList $ (reachableFrom (fmap toSet pdom)  (Set.fromList [x])), isReachableBeforeFromTreeM pdom m1 z x ] ) True,
                                                              m1 <- relevant, m1 /= z,
                                                              m1 ∈ cycleS,
#endif
                                                       assert (m1 /= n) True,
                                                       assert (m2 /= n) True,
                                                       assert (m2 /= m1) True,
                                                       assert (m1 ∊ (suc imdomTrc n)) True,
                                                       assert (m2 ∊ (suc imdomTrc n)) True
      ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        convert :: [(Node, Node, Node)] ->  Map (Node,Node) (Set Node)
        convert triples = runST $ do
            let keys = Set.toList $ Set.fromList [ (m1,m2) | (_,m1,m2) <- triples]

            assocs <- forM keys (\(m1,m2) -> do
              ns <- newSTRef Set.empty
              return ((m1,m2),ns)
             )

            let m = assert (List.sort keys == keys)
                  $ Map.fromDistinctAscList assocs

            forM_ triples (\(n,m1,m2) -> do
               let nsRef = m ! (m1,m2)
               modifySTRef nsRef (Set.insert n)
             )

            m' <- forM m readSTRef

            return m'

        imdom = imdomOfTwoFinger7 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG

        entriesFor cycle = [ n | n <- condNodes, not $ n ∈ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∈ cycle]




dodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
dodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc imdomTrc n),
                                                  m2 ∊ (suc imdomTrc n),
                                                  -- allImdomReachable (Set.fromList [n]) n (Set.fromList [m1,m2]),
                                                  let s12n = sMust ! (m1,m2,n),
                                                  let s21n = sMust ! (m2,m1,n),
                                                  Set.size s12n > 0,
                                                  Set.size s21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where sMust = smmnFMustNoReachCheckDod graph
        imdom = imdomOfTwoFinger7 graph
        -- allImdomReachable seen n ms
        --   | Set.null ms   = True
        --   | n ∈ ms        = allImdomReachable               seen  n (Set.delete n ms)
        --   | Set.null next = False
        --   | n' ∈ seen     = False
        --   | otherwise     = allImdomReachable (Set.insert n seen) n' ms
        --      where next = imdom ! n
        --            [n'] = Set.toList next
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]





data Color = Undefined | White | Black | Uncolored deriving (Show, Ord, Eq, Bounded, Enum)

instance JoinSemiLattice Color where
  Undefined `join` x         = x
  x         `join` Undefined = x

  Uncolored `join` x         = Uncolored
  x         `join` Uncolored = Uncolored

  White     `join` White     = White
  Black     `join` Black     = Black

  x         `join` y         = Uncolored

instance BoundedJoinSemiLattice Color where
  bottom = Undefined


instance PartialOrd.PartialOrd Color where
  c1 `leq` c2 =  c1 ⊔ c2 == c2

dodColoredDag :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDag graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc trcGraph m2),
                                                  m2 ∊ (suc trcGraph m1),
                                                  dependence n m1 m2
                               ]
                      ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                   ]
  where trcGraph = trc graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph


myDependenceFor graph color n = whiteChild ∧ otherChild
          where 
                whiteChild = (∃) (suc graph n) (\x -> color ! x == White)
                otherChild = (∃) (suc graph n) (\x -> assert ( color ! x /= Undefined) 
                                                      color ! x /= White)


dependenceFor graph n m1 m2 = whiteChild ∧ blackChild
          where color = colorFor graph n m1 m2
                whiteChild = (∃) (suc graph n) (\x -> color ! x == White)
                blackChild = (∃) (suc graph n) (\x -> color ! x == Black)

colorFor graph n m1 m2 = color
          where color = fst $ colorFor n (init, Set.fromList [m1,m2])
                  where init =             Map.fromList [ (m1, White), (m2, Black) ]
                               `Map.union` Map.fromList [ (n, Uncolored) | n <- nodes graph]
                colorFor :: Node -> (Map Node Color, Set Node) -> (Map Node Color, Set Node)
                colorFor n (color, visited)
                  | n ∈ visited = (color, visited)
                  | otherwise   = ( Map.insert n ((∐) [ color' ! x | x <- suc graph n ]) color', visited')
                      where (color', visited') = foldr colorFor (color, Set.insert n visited) (suc graph n)



colorFunctionalFor :: forall gr a b. DynGraph gr => gr a b -> Node -> Node -> Map Node Color -> Map Node Color
colorFunctionalFor graph m1 m2 color =
      color
    ⊔ Map.fromList [ (m1, White), (m2, Black) ]
    ⊔ Map.fromList [ (n, (∐) [ color ! x | x <- suc graph n ]) | n <- nodes graph, n /= m1, n /= m2 ]

colorLfpFor graph m1 m2 =  (㎲⊒) (Map.fromList [ (n, Undefined) | n <- nodes graph]) f
  where f = colorFunctionalFor graph m1 m2

dodColoredDagFixed :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDagFixed graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc imdomTrc n),
                                                  m2 ∊ (suc imdomTrc n),
                                                  dependence n m1 m2
                               ]
                      ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                   ]
  where trcGraph = trc graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph
        imdom = imdomOfTwoFinger7 graph
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())


dodColoredDagFixedFast :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodColoredDagFixedFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((mm1,mm2), ns) | cycle <- imdomCycles,
                                       (m1,m2) <- unorderedPairsOf cycle,
                                       assert (length cycle > 1) True,
                                       let ns = Set.fromList [ n | n <- entriesFor cycle,
                                                           assert (n /= m1 ∧ n /= m2) True,
                                                           assert (m1 ∊ (suc imdomTrc n)) True,
                                                           assert (m2 ∊ (suc imdomTrc n)) True,
                                                                   dependence n m1 m2
                                                ],
                                       (mm1,mm2) <- [(m1,m2),(m2,m1)]
                   ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        dependence = dependenceFor graph
        imdom = imdomOfTwoFinger7 graph
        imdomG = fromSuccMap imdom :: gr () ()
        imdomTrc = trc $ imdomG
        imdomCycles = scc imdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ imdom ! n], n' ∊ cycle]

        unorderedPairsOf []     = []
        unorderedPairsOf (x:xs) = [ (x,y) | y <- xs ] ++ unorderedPairsOf xs


wodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
wodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  let sMay12n = sMay ! (m1,m2,n),
                                                  let sMay21n = sMay ! (m2,m1,n),
                                                  ((n /= m2) ∧ (Set.size sMay12n > 0))  ∨  ((n == m1) ∧ (m2 ∊ suc graphTrc n)),
                                                  ((n /= m1) ∧ (Set.size sMay21n > 0))  ∨  ((n == m2) ∧ (m1 ∊ suc graphTrc n)),
                                                  let sMust12n = sMust ! (m1,m2,n),
                                                  let sMust21n = sMust ! (m2,m1,n),
                                                  Set.size sMust12n > 0 ∨ Set.size sMust21n > 0
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where sMust = smmnFMustNoReachCheckDod graph
        sMay  = smmnFMayWod graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        graphTrc = trc $ graph



wodDef :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
wodDef graph = Map.fromList [ ((m1,m2), Set.fromList [ p | p <- condNodes,
                                                           (∃) (maximalPaths ! p) (\path -> (m1,m2) `mayInPathBefore` (p,path)),
                                                           (∃) (maximalPaths ! p) (\path -> (m2,m1) `mayInPathBefore` (p,path)),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m2,m1) `inPathBefore` (x,path))
                                                           ∨ (∀) (maximalPaths ! x) (\path -> (m1,m2) `inPathBefore` (x,path))
                                                           )
                                        ]
                                )
                            | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPathBefore = inPathForBefore graph doms
        mayInPathBefore = mayInPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're ju

dodDef :: DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
dodDef graph = Map.fromList [ ((m1,m2), Set.fromList [ p | p <- condNodes,
                                                           (∀) (maximalPaths ! p) (\path ->   m1 `inPath` (p,path)
                                                                                            ∧ m2 `inPath` (p,path)),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m1,m2) `inPathBefore` (x,path))
                                                           ),
                                                           (∃) (suc graph p) (\x ->
                                                             (∀) (maximalPaths ! x) (\path -> (m2,m1) `inPathBefore` (x,path))
                                                           )
                                        ]
                                )
                            | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
  where sccs = scc graph
        sccOf m =  the (m ∊) $ sccs
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        maximalPaths = maximalPathsFor graph
        inPath = inPathFor graph doms
        inPathBefore = inPathForBefore graph doms
        doms = Map.fromList [ (entry, dom (subgraph (sccOf entry) graph) entry) | entry <- nodes graph ] -- in general, we don't actually need doms for all nodes, but we're just lazy here.



ntscdMyDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = myDod graph

ntscdMyDodFastPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodFastPDomSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = myDodFastPDom graph


ntscdMyDodSliceViaNtscd :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdMyDodSliceViaNtscd graph msS = combinedBackwardSlice graph ntscd' empty msS
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        ntscd' = mDFTwoFinger graph'
        empty = Map.empty


ntscdDodSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdDodSlice graph =  combinedBackwardSlice graph ntscd d
  where ntscd = invert'' $ ntscdF3 graph
        d     = dod graph


nticdMyWodSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = invert'' $ nticdF3 graph
        w     = myWod graph


nticdMyWodFastSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodFastSlice graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFTwoFinger graph
        w     = myWodFast graph

nticdMyWodPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodPDomSimpleHeuristic graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFTwoFinger graph
        w     = myWodFastPDomSimpleHeuristic graph

nticdMyWodPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdMyWodPDom graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFTwoFinger graph
        w     = myWodFastPDom graph


wccSliceViaWodTEILPDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaWodTEILPDom graph = \ms -> let fromMs = (Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m graph ]) in combinedBackwardSlice graph empty w ms ∩ fromMs
  where empty = Map.empty
        w     = wodTEIL'PDom graph


wccSliceViaNticdMyWodPDomSimpleHeuristic :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaNticdMyWodPDomSimpleHeuristic g ms = s ∩ fromMs
  where gRev = grev g
        g'   = subgraph (Set.toList toMs) g
        s    = nticdMyWodPDomSimpleHeuristic g' ms
        toMs   = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m gRev ]
        fromMs = Set.fromList $ [ n | m <- Set.toList ms, n <- reachable m g    ]


wccSliceViaNticd :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaNticd g msS = s
  where ms = Set.toList msS

        g'''   = foldr (flip delSuccessorEdges) g'' ms
          where  toMs   = rdfs ms g
                 g' = subgraph toMs g
                 
                 fromMs =  dfs ms g'
                 g'' = subgraph fromMs g'

        sinks            = fmap (\m -> [m]) ms

        -- sinkS            = fmap Set.fromList sinks
        -- sinkNodes        = msS
        -- nonSinkCondNodes = Map.fromList [ (n, succs) | n <- nodes g''', not $ n ∈ sinkNodes, let succs = suc g''' n, length succs > 1 ]
        -- idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes g'''

        idom = Map.fromList $ iPDomForSinks sinks g'''

        s = Map.keysSet $ Map.filter (== Nothing) idom 




wodTEILSliceViaNticd :: (Show (gr a b),  DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSliceViaNticd g =  \ms ->
    let toMs  = rdfs (Set.toList ms) g
        toMsS = Set.fromList toMs
        g'    = Set.fold (flip delSuccessorEdges) (subgraph toMs g) ms
        msSinks = [ sink | sink <- sinks, (∃) ms (\m -> m `elem` sink) ]
        idom'0 = id
               $ Map.union (Map.fromSet    (\m     -> Nothing) $ ms)
               $ Map.union (Map.mapWithKey (\x _   -> Nothing) $ Map.filterWithKey isEntry $ condNodes')
               $ Map.union (Map.mapWithKey (\x [z] ->                     assert (z /= x) $ Just z                   ) noLongerCondNodes)
               $ Map.union (Map.fromList  [ (x, case suc g' x of { [z] -> assert (z /= x) $ Just z  ; _ -> Nothing  }) | msSink <- msSinks, x <- msSink ])
               $ fmap intoMs
               $ restrict idom toMsS
          where isEntry x _ = case idom ! x of
                  Nothing -> False
                  Just z -> z ∈ sinkNodes
                intoMs n@(Nothing) = n
                intoMs n@(Just x)
                  | x ∈ toMsS = n
                  | otherwise = Nothing
        idom'0Rev   = invert''' idom'0
        processed'0 = reachableFrom idom'0Rev ms
        todo'0      = without nonSinkCondNodes' processed'0
        worklist'0  = Dequeue.fromList $ Map.assocs todo'0
        idom'1 = Map.union (fmap (\x -> Nothing) todo'0)
               $ idom'0
        idom'1Rev = invert''' idom'1
        idom'2 = isinkdomOftwoFinger8Up                  g'                                                               nonSinkCondNodes'   worklist'0  processed'0 idom'1Rev idom'1
        idom'  = isinkdomOfTwoFinger8DownSingleNodeSinks g' sinkNodes' (Map.filterWithKey (\x _ -> idom'2 ! x /= Nothing) nonSinkCondNodes')                                    idom'2
        sinks' = [ [m] | m <- Set.toList ms]
        sinkNodes' = ms
        (condNodes', noLongerCondNodes) =
              Map.partition isCond
            $ fmap (List.filter (∈ toMsS))
            $ restrict condNodes (toMsS ∖ ms)
          where isCond []  = False
                isCond [_] = False
                isCond _   = True
        nonSinkCondNodes' = condNodes'

        sinkS' = fmap Set.fromList sinks'
        cycleOf' =  Map.fromList [ (s, sink) | sink <- sinkS', s <- Set.toList $ sink ]
        
        idom'Direct = Map.fromList $ iPDomForSinks sinks' g'
    in -- (if idom' == idom'Direct then id else traceShow (ms, g, "*****", idom, idom'0, idom'1, idom'2, idom', fmap fromSet $ isinkdomOfTwoFinger8 g')) $ 
       assert (idom' == idom'Direct) $
       -- nticdSliceLazy g' cycleOf' (invert''' idom'Direct) ms
       idfViaCEdgesFastForCycles (cycleOf', sinkS') g' idom'Direct ms
  where
        sinks            = controlSinks g
        sinkNodes        = (∐) [ Set.fromList sink | sink <- sinks]
        condNodes        = Map.fromList [ (n, succs) | n <- nodes g, let succs = suc g n, length succs > 1 ]
        nonSinkCondNodes = without condNodes sinkNodes
        idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes g



myWodFastSlice :: ( DynGraph gr) => gr a b ->  Set Node  -> Set Node
myWodFastSlice graph =  combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = myWodFast graph


myWodFastPDomSimpleHeuristicSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
myWodFastPDomSimpleHeuristicSlice graph =  combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = myWodFastPDomSimpleHeuristic graph



wodTEILSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSlice graph = combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = wodTEIL' graph

wodTEILPDomSlice :: ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILPDomSlice graph = combinedBackwardSlice graph empty w
  where empty = Map.empty
        w     = wodTEIL'PDom graph

cdFromMyWod graph =  (∐) [ Map.fromList [ (n, Set.fromList [m] ) ]  | ((m1,m2),ns) <- Map.assocs $ myWodFast graph, n <- Set.toList ns, m <- [m1,m2] ]
