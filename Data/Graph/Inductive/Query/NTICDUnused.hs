{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.NTICDUnused where

import Debug.Trace (traceShow)
import Control.Exception.Base (assert)

import Data.Maybe(fromJust, isNothing)
import Data.List (nub)
import qualified Data.List as List

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Util (removeDuplicateEdges, delSuccessorEdges, delPredecessorEdges, fromSuccMap, toSuccMap, prevCondNodes, nextCondNode, toNextCondNode)
import Data.Graph.Inductive

import Unicode
import Util(reachableFrom, toSet, fromSet, foldM1, invert'')
import IRLSOD(CFGNode)
import Program (Program)


import Data.Graph.Inductive.Query.LCA(lca, lcaRMyCDForNode)
import Data.Graph.Inductive.Query.PostDominance (DomFunctionalGen, sinkPathsFor, SinkPath(..), cyclesInScc, domOfGfp, domOfLfp, sinkdomOfGfp)
import Data.Graph.Inductive.Query.NTICD.Util (cdepGraph, cdepGraphP)
import Data.Graph.Inductive.Query.NTICD (isinkdomOfSinkContraction, smmnFMustWod, myDependenceFor, colorLfpFor, combinedBackwardSlice, nticdF3, mayNaiveGfp)
import Data.Graph.Inductive.Query.Dependence (Dependence)



{- The definition of ntacd -}
ntacdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntacdDefGraphP = cdepGraphP ntacdDefGraph

ntacdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntacdDefGraph  = cdepGraph ntacdDef

ntacdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntacdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inSinkPathAfter` (ni,nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inSinkPathAfter` (ni,nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where 
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inSinkPathAfter = inSinkPathAfterFor graph


{- The definition of ntbcd -}
ntbcdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntbcdDefGraphP = cdepGraphP ntbcdDefGraph

ntbcdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntbcdDefGraph  = cdepGraph ntbcdDef

ntbcdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntbcdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph,
                                                nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (sinkPaths ! nk) (\path ->       nj `inSinkPathAfter'` (ni,nk,path)),
                                                (∃) (sinkPaths ! nl) (\path -> not $ nj `inSinkPathAfter'` (ni,nl,path))
                                         ]
                       )
                     | ni <- condNodes ]

  where 
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        sinkPaths = sinkPathsFor graph
        inSinkPathAfter' = inSinkPathAfterFor' graph


inSinkPathAfterFor :: DynGraph gr => gr a b -> Node -> (Node, Node, SinkPath) -> Bool
inSinkPathAfterFor graph' n (cond, s, path) = inSinkPathFromEntries [s] path
  where 
    inSinkPathFromEntries _       (SinkPath []           controlSink) = n ∊ controlSink ∧ (
                          (  (not $ cond ∊ controlSink) -- ∧
                             -- ((∀) (cyclesInScc  controlSink graph') (\cycle -> n ∈ cycle))
                          )
                        ∨ (  (cond ∊ controlSink) ∧
                             (s == cond ∨ n ∊ (suc withoutCondTrc s))
                          )
                      )
      where withoutCondTrc = trc $ delNode cond graph'
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n ∊ scc = -- traceShow (s, n, cond, entries, scc, controlSink) $ 
                         (True) ∧ (
--                         (not (cond ∈ scc) ∨ (n ∊ (suc (trc $ delNode cond graph') s)  )  ∨ (s == cond) ) ∧ (
                           (∀) entries (\entry -> let doms = (dom graph' entry) in
                            (∀) exits (\exit -> let domsexit = doms `get` exit in
                                   (entry /= exit || n == entry) && n ∊ domsexit)
                           )
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
            exits = [ n | (n,_) <- borderEdges ]
            get assocs key = fromJust $ List.lookup key assocs


inSinkPathAfterFor' :: DynGraph gr => gr a b -> Node -> (Node, Node, SinkPath) -> Bool
inSinkPathAfterFor' graph' n (cond, s, path) = inSinkPathFromEntries [s] path
  where
    get assocs key = fromJust $ List.lookup key assocs
    inSinkPathFromEntries entries (SinkPath []           controlSink) = n ∊ controlSink ∧ (
                          (  (not $ cond ∊ controlSink) ∧ (
                              ((∀) entries (\entry -> let doms = dom graph' entry in
                                (∀) cycles  (\cycle -> let c = head cycle in
                                  (n ∊ cycle) ∨ (n ∊ (doms `get` c))
                                )
                               )
                              )
                             )
                          )
                        ∨ (  (cond ∊ controlSink) ∧ (∀) entries (\entry -> 
                             (entry == cond ∨ n ∊ (suc withoutCondTrc entry))
                          ))
                      )
      where withoutCondTrc = trc $ delNode cond graph'
            cycles = (cyclesInScc  controlSink graph')
--     inSinkPathFromEntries entries (SinkPath []           controlSink) =
--                              (∀) entries (\entry -> 
--                                (∀) (nrPaths (initial entry) entry ) (\path ->  (n ∈ path))
--                              )
-- -- (Set.fromList path == Set.fromList controlSink) →
--       where cycles = (cyclesInScc  controlSink graph')
--             initial entry = Map.fromList [ (m, Set.empty) | m <- controlSink ]
--                           ⊔ Map.fromList [ (x, Set.fromList [(x,entry)]) | x <- controlSink, x ∈ pre graph' entry ]
--             nrPaths :: Map Node (Set (Node,Node)) -> Node -> [[Node]]
--             nrPaths taken n
--              | Set.null allowedEdges      = [[n]]
--              | otherwise                  = -- traceShow taken $
--                                             [ n:p | m <- Set.toList $ Set.map snd $ allowedEdges,
--                                                     p <- nrPaths (Map.adjust (\taken -> Set.insert (n,m) taken ) n taken) m  ]
--                where allowedEdges = (Set.fromList $ [(n,m) | m <- suc graph' n]) ∖ (taken ! n)

            
    -- inSinkPathFromEntries entries (SinkPath []           controlSink) =
    --                          (∀) entries (\entry -> (entry == cond) ∨
    --                            n ∈ (suc (trc $ delEdges ([(cond, x) | x <- suc graph' cond]) graph') entry)
    --                          )
    --   where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries entries  (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) entries (\entry -> let doms = dom graph' entry in
    --                            (∀) cycles  (\cycle -> let c = head cycle in
    --                              (s ∈ cycle) ∨ (n ∈ cycle) ∨ (n ∊ (doms `get` c))
    --                            )
    --                           )
    --                          )
    --                         )
    --   where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries entries  (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) entries (\entry -> let doms = dom graph' entry in
    --                            (∀) cycles  (\cycle -> let c = head cycle in
    --                               (s == cond) ∨ ((cond ∈ cycle) → (n ∈ cycle) ∨ (n ∊ (doms `get` c)))
    --                            )
    --                           )
    --                          )
    --                         )
    --  where cycles = (cyclesInScc  controlSink graph')
    -- inSinkPathFromEntries _       (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) (cyclesInScc  controlSink graph') (\cycle -> (s ∈ cycle) ∨ (n ∈ cycle)))
    --                       )
    -- inSinkPathFromEntries entries       (SinkPath []           controlSink) = n ∊ controlSink ∧ (
    --                          ((∀) (cyclesInScc  controlSink graph') (\cycle ->
    --                            ((∃) entries (∈ cycle)) → (s ∈ cycle) ∨ (n ∈ cycle)))
    --                       )
    inSinkPathFromEntries entries (SinkPath (scc:prefix) controlSink)
        | n ∊ scc = -- traceShow (s, n, cond, entries, scc, controlSink) $ 
                         (True) ∧ (
--                         (not (cond ∈ scc) ∨ (n ∊ (suc (trc $ delNode cond graph') s)  )  ∨ (s == cond) ) ∧ (
                           (∀) entries (\entry -> let doms = (dom graph' entry) in
                            (∀) exits (\exit -> let domsexit = doms `get` exit in
                                   (entry /= exit || n == entry) && n ∊ domsexit)
                           )
                         )
        | otherwise    =  inSinkPathFromEntries [ n' | (_,n') <- borderEdges ] (SinkPath prefix controlSink)
      where next = if (null prefix) then controlSink else head prefix
            borderEdges = [ (n,n') | n <- scc, n' <- suc graph' n, n' ∊ next ]
            exits = [ n | (n,_) <- borderEdges ]



{- The definition of ntnrcd -}
ntnrcdDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
ntnrcdDefGraphP = cdepGraphP ntnrcdDefGraph

ntnrcdDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
ntnrcdDefGraph  = cdepGraph ntnrcdDef

ntnrcdDef :: DynGraph gr => gr a b ->  Map Node (Set Node)
ntnrcdDef graph =
        Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔   Map.fromList [ (ni, Set.fromList [ nj | nj <- nodes graph, nj /= ni,
                                                nk <- suc graph ni, nl <- suc graph ni, nk /= nl,
                                                (∀) (nrPaths ! (ni,nk)) (\path ->       nj `inPath` path),
                                                (∃) (nrPaths ! (ni,nl)) (\path -> not $ nj `inPath` path)
                                         ]
                       )
                     | ni <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        nrPaths = nrPathsFor graph
        inPath n (NrPath { path }) = n ∊ path

data NrPath = NrPath { path :: [Node] } deriving Show

nrPathsFor :: DynGraph gr => gr a b -> Map (Node,Node) [NrPath]
nrPathsFor graph = Map.fromList [ ((n,m), fmap (\p -> NrPath { path = p }) $ nrPathsFor (n,m)) | n <- nodes graph, m <- suc graph n ]
    where
      nrPathsFor :: (Node,Node) -> [[Node]]
      nrPathsFor (n,m) = nrPaths (forbidden (n,m)) (initial (n,m)) m
      initial (n,m)   = Map.fromList [(n, Set.empty) | n <- nodes graph]
--                  ⊔ Map.fromList [(n, Set.fromList $ [ (n,m) ]) ]
      forbidden (n,m) = Set.fromList $ [ (n,m) ] 
--      forbidden (n,m) = Map.fromList [(x, Set.fromList $ [ (x,n) ]) |  x <- pre graph n ]
--      nrPathsF taken ns = concat $ fmap (nrPaths taken) ns
      nrPaths :: Set (Node, Node) -> Map Node (Set (Node,Node)) -> Node -> [[Node]]
      nrPaths forbidden taken n
--       | Set.null allowedEdges  ∧  (not $ Set.null $ (Set.fromList  [(n,m) | m <- suc graph n]) ⊓ forbidden)  = []
       | Set.null allowedEdges  ∧  (not $ Set.null $ (Set.fromList  [(n,m) | m <- suc graph n]) ⊓ (forbidden ∖ (taken ! n)))  = []
       | Set.null allowedEdges                                                                                                = [[n]]
       | otherwise                  = -- traceShow taken $
                                      [ n:p | m <- Set.toList $ Set.map snd $ allowedEdges,
                                              p <- nrPaths forbidden (Map.adjust (\taken -> Set.insert (n,m) taken ) n taken) m  ]
        where allowedEdges = (Set.fromList $ [(n,m) | m <- suc graph n]) ∖ (taken ! n)



roflDomDef graph = Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                                                        -- (∀) (nodes graph) (\n ->
                                                        --                             y ∈                                       doms ! n               ! m
                                                        --                           ∨ m ∈ (reachableFrom (                      doms ! n) (Set.fromList [y]) Set.empty)
                                                        -- )
                                                        (∀) (nodes graph) (\n ->
                                                                                    y ∈ (reachableFrom (                      doms ! n) (Set.fromList [m]))
                                                                                  ∨ m ∈ (reachableFrom (                      doms ! n) (Set.fromList [y]))
                                                        )
                                                        -- (∃) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)),
                                                        -- (∀) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)   ∨  (n == m)   ∨   y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty))
                                                        -- (∃) (nodes graph) (\n -> m ∈ doms ! n ! y),
                                                        -- (∀) (nodes graph) (\n -> m ∈ doms ! n ! y   ∨   y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ doms ! n ! y )
                                                        -- (∃) (nodes graph) (\n -> n /= m   ∧   m ∈ doms ! n ! y ),
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ (reachableFrom (doms ! n) (Set.fromList [y]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨     (not $ y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty)))
                                      ]
                                  ) | y <- nodes graph ]
   where doms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]
         pdoms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]

lolDomDef graph0 = Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,

                                                        -- (∀) (nodes graph) (\n ->
                                                        --                             n ∈ (reachableFrom (                      doms ! y) (Set.fromList [m]) Set.empty)
                                                        --                           ∨ m ∈                                       doms ! y               ! n
                                                        -- )
                                                        (∀) (nodes graph) (\n ->
                                                                                    n ∈ (reachableFrom (                      doms ! y) (Set.fromList [m]))
                                                                                  ∨ m ∈ (reachableFrom (                      doms ! y) (Set.fromList [n]))
                                                        )
                                                     -- (∀) (nodes graph) (\n ->
                                                     --                                (                                m ∈ (reachableFrom (                      pdoms ! n) (Set.fromList [y]) Set.empty))
                                                     --                              ∨ ( (∃) (suc graph y) (\x -> not $ n ∈ (reachableFrom (                      pdoms ! y) (Set.fromList [x]) Set.empty)))
                                                     --                                 ∧                  (      not $ n ∈ (reachableFrom (                      pdoms ! m) (Set.fromList [y]) Set.empty))
                                                     --                              ∨ ( y == n)
                                                     -- )
                                                        -- (∀) (nodes graph) (\n ->
                                                        --                             n ∈ (reachableFrom (                      pdoms ! m) (Set.fromList [y]) Set.empty)
                                                        --                             -- y ∈ (reachableFrom (fmap (Set.delete n) $ doms ! n) (Set.fromList [m]) Set.empty)
                                                        --                           ∨ m ∈ (reachableFrom (                      pdoms ! n) (Set.fromList [y]) Set.empty)
                                                        --                           -- ∨ m ∈ (reachableFrom (fmap (Set.delete n) $ doms ! n) (Set.fromList [y]) Set.empty)
                                                        -- )
                                                        -- (∃) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)),
                                                        -- (∀) (nodes graph) (\n -> traceIfFalse (y,m,n, doms ! n) $ (n /= m   ∧   m ∈ doms ! n ! y)   ∨   ( n == y )  ∨    m ∈ (reachableFrom (doms ! n) (Set.fromList [y]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ doms ! n ! y )
                                                        -- (∃) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)),
                                                        -- (∀) (nodes graph) (\n -> (n /= m   ∧   m ∈ doms ! n ! y)   ∨  (n == m)   ∨   y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty))
                                                        -- (∃) (nodes graph) (\n -> n /= m   ∧   m ∈ doms ! n ! y ),
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨   m ∈ (reachableFrom (doms ! n) (Set.fromList [y]) Set.empty))
                                                        -- (∀) (nodes graph) (\n -> y == n   ∨     (not $ y ∈ (reachableFrom (doms ! n) (Set.fromList [m]) Set.empty)))
                                      ]
                                  ) | y <- nodes graph ]
   where  graph = grev graph0
          pdoms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]
          doms  = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph0 n)
                               )
                             | n <- nodes graph ]


omegaLulDomDef graph = Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                                                             -- (∃) (nodes graph) (\m' -> m ∈ doms ! y ! m')
                                                              (∀) (suc graph y) (\x -> 
                                                                                    m ∈ (reachableFrom (                      pdoms ! y) (Set.fromList [x]))
                                                              )
                                      ]
                                  ) | y <- nodes graph ]
   where  pdoms = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graphRev n)
                               )
                             | n <- nodes graph ]
            where graphRev = grev graph
          doms  = Map.fromList [ (n,  (Map.fromList [(n, Set.empty)])
                                  ⊔ (fmap (\m -> Set.fromList [m]) $ Map.fromList $ iDom graph n)
                               )
                             | n <- nodes graph ]


fRoflDomNaive graph _ _ nextCond toNextCond = f 
  where f rofldomOf =
                      Map.fromList [ (y, Set.fromList [y])                           | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                                                            before m  (Set.fromList $ pre graph y) (Set.fromList $ pre graph y ++ [y])
                                                      ]
                                     )
                                   | y <- nodes graph, pre graph y/= []]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,
                    --                                         (∀) (pre graph y) (\x ->   (x == y)
                    --                                                                  ∨ (m ∈ rofldomOf ! x   ∧  (m == x   ∨   (not $ x `elem` pre graph m)))
                    --                                                           )
                    --                                   ]
                    --                  )
                    --                | y <- nodes graph, pre graph y/= []]
                    -- ⊔ Map.fromList [ (x,  (∏) [ rofldomOf ! p | p <- pre graph x])   | x <- nodes graph, pre graph x/= []]
                     ⊔ Map.fromList [ (x, Set.fromList [p] ) | x <- nodes graph, [p] <- [nub $ pre graph x]]
                    -- ⊔ Map.fromList [ (x,  (∏) [ rofldomOf ! p | p <- pre graph x, p ∈ rofldomOf ! x ]) | x <- nodes graph, [ p | p <- pre graph x, p ∈ rofldomOf ! x ] /= []]
        before m xs seen = traceShow  (m, xs, seen, bef xs seen) $ bef xs seen
          where bef xs seen
                    | Set.null xs = True
                    | m ∈ xs      = False
                    | otherwise = bef new (seen ∪ new) 
                  where new = Set.fromList [ x' | x <- Set.toList xs, x' <- suc graph x,  not  $ x' ∈ seen]

rofldomNaiveGfp graph = domOfGfp graph fRoflDomNaive
rofldomNaiveLfp graph = domOfLfp graph fRoflDomNaive



rofldomOfTwoFinger7 :: forall gr a b. (DynGraph gr, Eq b) => gr a b -> Map Node (Set Node)
rofldomOfTwoFinger7 graph0 = Map.mapWithKey (\n ms -> Set.delete n ms) $
                          fmap toSet $ twoFinger 0 worklist0 rofldom0
  where graph = removeDuplicateEdges $ delEdges [ e | e@(n,m) <- edges graph0, n == m] $ graph0
        rofldom0   =           Map.fromList [ (x, Just z   ) | x <- nodes graph, [z] <- [pre graph x], z /= x]
                   `Map.union` Map.fromList [ (x, Nothing  ) | x <- nodes graph]
        worklist0   = condNodes
        condNodes   = Set.fromList [ x | x <- nodes graph, length (pre graph x) > 1 ]
        prevConds   = prevCondNodes graph
        nextCond    = nextCondNode graph

        twoFinger :: Integer -> Set Node ->  Map Node (Maybe Node) -> Map Node (Maybe Node)
        twoFinger i worklist rofldom
            |   Set.null worklist = -- traceShow ("x", "mz", "zs", "influenced", worklist, rofldom) $
                                    -- traceShow (Set.size worklist0, i) $ 
                                    rofldom
            | otherwise           = -- traceShow (x, mz, zs, influenced, worklist, rofldom) $
--                                    traceShow (x, influenced, influenced', rofldom) $
                                    if (not $ new) then twoFinger (i+1)                worklist'                                   rofldom
                                    else                twoFinger (i+1) (influenced' ⊔ worklist')  (Map.insert x zs                rofldom)
          where (x, worklist')  = Set.deleteFindMin worklist
                mz = foldM1 (lca rofldom) [ y | y <- pre graph x]
                -- mz = foldM1 lca (pre graph x)
                zs = case mz of
                      Just z  -> if z/= x then
                                   find z (Set.fromList [z])
                                 else
                                   Nothing
                      Nothing ->  Nothing
                  where find z seen
                          | (∀) (pre graph x) (\y -> not $ y `elem` pre graph z) = Just z
                          | otherwise = let z' = rofldom ! z in case z' of
                              Nothing -> Nothing
                              Just z' -> if z' ∈ seen then Nothing else find z' (Set.insert z' seen)
                          
                new     = assert (isNothing $ rofldom ! x) $
                          (not $ isNothing zs)
                influenced' = Set.fromList [ n | (n,Nothing) <- Map.assocs rofldom, n /= x]


fLolDomNaive graph _ _ nextCond toNextCond = f 
  where f loldomOf =
                         Map.fromList [ (x, Set.fromList [ m | m <- nodes graph, (∃) (pre graph x) (\p -> p /= m   ∧   m ∈ loldomOf ! p)] ) | x <- nodes graph ]
                    -- ⊔ Map.fromList [ (x,  (∏) [ loldomOf ! p | p <- pre graph x])   | x <- nodes graph, pre graph x/= []]
                    -- ⊔ Map.fromList [ (x, Set.fromList [p] ) | x <- nodes graph, [p] <- [nub $ pre graph x]]
                    -- ⊔ Map.fromList [ (x,  (∏) [ loldomOf ! p | p <- pre graph x, p ∈ loldomOf ! x ]) | x <- nodes graph, [ p | p <- pre graph x, p ∈ loldomOf ! x ] /= []]
loldomNaiveGfp graph = domOfGfp graph fLolDomNaive
loldomNaiveLfp graph = domOfLfp graph fLolDomNaive


myCD :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
myCD graph = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
           ⊔ Map.fromList [ (n, myCDForNode graph n) | cycle <- isinkdomCycles, length cycle > 1, n <- cycle, n `elem` condNodes ]
  where condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]

myCDForNode :: forall gr a b. DynGraph gr => gr a b -> Node -> (Set Node)
myCDForNode graph n = Set.fromList [ m |       -- m <- Set.toList $ reachableFrom isinkdom (Set.fromList [n]) Set.empty,
                                                  let gn  = delSuccessorEdges graph n,
                                                  let isinkdomN  = isinkdomOfSinkContraction gn,
                                                  -- let (z,relevant) = foldr1 (lcaR (fmap fromSet isinkdomN)) [(x, Set.empty) | x <- suc graph n],
                                                  -- m <- Set.toList relevant, m /= z
                                                  m <- nodes graph,
                                                  (∃) (suc graph n) (\x ->       m ∈ reachableFrom isinkdomN (Set.fromList [x])),
                                                  (∃) (suc graph n) (\x -> not $ m ∈ reachableFrom isinkdomN (Set.fromList [x]))
                                   ]
  where lcaR = lcaRMyCDForNode


myEntryWodFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
myEntryWodFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), ns)   | cycle <- isinkdomCycles,
                                       let entries = entriesFor cycle,
                                       m1 <- cycle,
                                       m2 <- cycle,
                                       m1 /= m2,
                                       assert (length cycle > 1) True,
                                       let color = colorLfpFor graph m1 m2,
                                       let ns = Set.fromList [ n | n <- entries,
                                                                   n /= m1 ∧ n /= m2,
                                                           assert (m1 ∊ (suc isinkdomTrc n)) True,
                                                           assert (m2 ∊ (suc isinkdomTrc n)) True,
                                                                   myDependence color n
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


mySinkWodFast  :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
mySinkWodFast graph = (∐) [ Map.fromList [ ((m1, m2), Set.fromList [ n ] ) ] |
                                                                           cycle <- isinkdomCycles, length cycle > 1, n <- cycle, n `elem` condNodes,
                                                                           xl <- suc graph n,
                                                                           xr <- suc graph n,
                                                                           m1 <- Set.toList $ dom ! xl,
                                                                           m1 /= n,
                                                                           m2 <- cycle,
                                                                           m2 /= n,
                                                                           m2 /= m1,
                                                                           not $ m2 ∈ dom ! xr
                                                                           -- not $ m2 `elem` (suc cdG n)
                      ]
  where condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n, x /= n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        dom = myDom graph
        cd  = myCD graph
        cdG = fromSuccMap cd :: gr () ()
        cdGTrc = trc cdG

-- fMyDom graph _ _ nextCond toNextCond = f 
--   where f sinkdomOf =
--                       Map.fromList [ (y, Set.fromList [y])                          | y <- nodes graph]
--                     ⊔ Map.fromList [ (y, Set.fromList $ toNextCond y)               | y <- nodes graph]
--                     ⊔ Map.fromList [ (y,  (∏) [ sinkdomOf ! x | x <- suc graph n ]) | y <- nodes graph, Just n <- [nextCond y]]
-- myDomOfGfp graph = domOfGfp graph fMyDom


fAllDomNaive graph all = f 
  where f alldomOf =
                      Map.fromList [ (y, Map.fromList [ (y, all) ]             )  | y <- nodes graph]
                    ⊔ Map.fromList [ (y, fmap (Set.delete y) $ (∏) [ alldomOf ! x | x <- suc graph y ])  | y <- nodes graph, suc graph y /= []]

allDomNaiveGfp graph = (𝝂) init (fAllDomNaive graph all)
  where init = Map.fromList [ (y, Map.empty                                  ) | y <- nodes graph]
             ⊔ Map.fromList [ (y, Map.fromList [ (m, all) | m <- reachable y]) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph
        all = Set.fromList $ nodes graph

myDomNaiveGFP graph =
                      Map.fromList [ (y, Set.fromList [ m | m <- nodes graph, (∀) (suc graph y) (\x -> Map.member m (allDom ! x)  ∧  y ∈ allDom ! x ! m ) ]) | y <- nodes graph ]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- toNextCond y])                                                                              | y <- nodes graph, not $ y `elem` condNodes]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,                          Map.member m (allDom ! y)  ∧  y ∈ allDom ! x ! m   ]) | y <- nodes graph,
                    --                                                                                                                                      not $ y `elem` condNodes,
                    --                                                                                                                                           [x] <- [suc graph y]
                    --   ]

  where allDom = allDomNaiveGfp graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        -- nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph

fMyDomNaive' graph = f 
  where f mydomOf = -- traceShow mydomOf $
                      Map.fromList [ (y, Set.fromList [y])                                               | y <- nodes graph]
                    -- ⊔ Map.fromList [ (y, mydomOf ! m ) | y <- nodes graph, [m] <- [nub $ suc graph y] ]
                    -- ⊔ Map.fromList [ (y, mydomOf ! m ) | y <- nodes graph, [m] <- [nub $ pre graph y] ]
                    ⊔ Map.fromList [ (y, Set.fromList [ m |  m <- nodes graph,
                                                             let inner = [ x | x <- suc graph y,       y ∈ allMay ! x ! m ],
                                                             let outer = [ x | x <- suc graph y, not $ y ∈ allMay ! x ! m ],
                                                             (∀) (suc graph y) (\x ->
                                                                  m ∈ mydomOf ! x
                                                               -- ∧ y ∈ allMay ! x ! m
                                                               -- ∧  (m `elem` (suc graph y)) → ((∀) (suc graph y) (\x' -> (not $ x' `elem` (suc graph m))))
                                                               -- -- ∧  (m `elem` (pre graph y)) → ((length $ nub $ pre graph y) == 1)
                                                             )
                                                          -- ∧  (∀) inner (\i ->
                                                          --      (∀) outer (\o -> not $ y ∈ allMay ! i ! o)
                                                          --    )
                                                          ∧  (∀) inner (\i ->
                                                               (∀) outer (\o -> not $ y ∈ allMay ! i ! o)
                                                             )
                                                      ])  | y <- nodes graph, suc graph y /= []]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m |  m <- nodes graph, (∀) (suc graph y) (\x -> m ∈ mydomOf ! x   ∧   (∀) (pre graph x) (\y' -> m ∈ mydomOf ! y') ) ])  | y <- nodes graph, suc graph y /= []]
        allMay = allMayNaiveLfp graph

myDomNaive'Gfp graph = (𝝂) init (fMyDomNaive' graph)
  where init = Map.fromList [ (y, all)       | y <- nodes graph]
        all =  Set.fromList $ nodes graph



fAllMayNaive graph all = f 
  where f alldomOf =
                      Map.fromList [ (y, Map.fromList [ (y, all) ]             )  | y <- nodes graph]
                    ⊔ Map.fromList [ (y, fmap (Set.delete y) $ (∐) [ alldomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]

allMayNaiveLfp graph =  -- (𝝂) init (fAllMayNaive graph all)
                       (㎲⊒) empty (fAllMayNaive graph all)
  where empty = Map.fromList [ (y, Map.fromList [ (m, Set.empty) | m <- nodes graph ]) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph
        all = Set.fromList $ nodes graph


myMayNaiveLfp graph =
                      Map.fromList [ (y, Set.fromList [ m | m <- nodes graph, (∀) (suc graph y) (\x -> Map.member m (allMay ! x)  ∧  y ∈ allMay ! x ! m ) ]) | y <- nodes graph ]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- toNextCond y])                                                                              | y <- nodes graph, not $ y `elem` condNodes]
                    -- ⊔ Map.fromList [ (y, Set.fromList [ m | m <- nodes graph,                          Map.member m (allDom ! y)  ∧  y ∈ allDom ! x ! m   ]) | y <- nodes graph,
                    --                                                                                                                                      not $ y `elem` condNodes,
                    --                                                                                                                                           [x] <- [suc graph y]
                    --   ]

  where allMay = allMayNaiveLfp graph

fMayNotNaive graph _ _ nextCond toNextCond = f 
  where f maynotdomOf = Map.fromList [ (y, Set.delete y $ all)                                        | y <- nodes graph, suc graph y == []]
                      ⊔ Map.fromList [ (y, Set.delete y $ (∏) [ maynotdomOf ! x | x <- suc graph y ]) | y <- nodes graph, suc graph y /= []]
        all = Set.fromList $ nodes graph

notOfGfp :: DynGraph gr => gr a b -> DomFunctionalGen gr a b -> Map Node (Set Node)
notOfGfp graph f = (𝝂) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Set.empty) | y <- nodes graph]
             ⊔ Map.fromList [ (y, all ∖ (Set.fromList $ reachable y)) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph
        all = Set.fromList $ nodes graph

        
mayNotNaiveGfp graph = notOfGfp graph fMayNotNaive






-- fMyDomNaive graph my = f 
--   where f mydomOf =
--                       Map.fromList [ (y, Map.fromList [ (y, my) ]             )  | y <- nodes graph]
--                     ⊔ Map.fromList [ (y, fmap (Set.delete y) $ (∏) [ mydomOf ! x | x <- suc graph y ])  | y <- nodes graph, suc graph y /= []]

-- myDomNaiveGfp graph = (𝝂) init (fMyDomNaive graph my)
--   where init = Map.fromList [ (y, Map.empty                                  ) | y <- nodes graph]
--              ⊔ Map.fromList [ (y, Map.fromList [ (m, my) | m <- reachable y]) | y <- nodes graph]
--         condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
--         reachable x = suc trncl x
--         trncl = trc graph
--         my = Set.fromList $ nodes graph


myDom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
myDom graph =
              toSuccMap $
              (trc :: gr () () -> gr () ()) $
              fromSuccMap $
              Map.fromList [ (n, Set.empty)        | n <- nodes graph ]
            ⊔ Map.fromList [ (n, Set.fromList [m]) | n <- nodes graph, not $ n `elem` condNodes, [m] <- [suc graph n] ]
            ⊔ (∐) [ Map.fromList [ (n, Set.fromList [ m ] ) ]
            | n <- condNodes,
            -- | cycle <- isinkdomCycles,
            --   length cycle > 1,
            --   n <- cycle,
            --   n `elem` condNodes,
              -- let gn   = delPredecessorEdges graph n,
              -- let domn = (fmap Set.singleton$ Map.fromList $ iDom gn n) `Map.union` Map.fromList [ (m, Set.empty) | m <- nodes graph],
              -- Just m <- [foldM1 (lca domn) (suc graph n)]
              let gn  = delSuccessorEdges graph n,
              let isinkdomN  = fmap fromSet $ isinkdomOfSinkContraction gn,
              Just m <- [foldM1 (lca isinkdomN) (suc graph n)]
 ]
  where condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]


cdFromDom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node)
cdFromDom graph dom = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
                    ⊔ Map.fromList [ (n, Set.fromList [ m |                xl <- suc graph n,
                                                                           xr <- suc graph n,
                                                                           m <- Set.toList $ dom ! xl,
                                                                           m /= n,
                                                                           not $ m ∈ dom ! xr
                                         ]
                                      )
                                    | n <- condNodes ]
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]

someprop g =  smmnmay' == smmnmay
  where trcg = trc g
        smmnmay  = Set.fromList [ ((m1,m2,n),(nn,x)) | ((m1,m2,n),nx) <- Map.assocs $ smmnFMustWod g, m1 /= m2, m1 /= n, m2 /= n, (nn,x) <- Set.toList nx, m2 `elem` suc trcg m1 ]
        smmnmay' = Set.fromList [ ((m1,m2,n),(n,x))  | n <- nodes g, (length $ suc g n) > 1,
                                                       let gn  =        delSuccessorEdges   g n,
                                                       let gn' = grev $ delPredecessorEdges g n,
                                                          
                                                       let pdom = sinkdomOfGfp gn,
                                                       let pmay = mayNaiveGfp  gn,

                                                       let dom  = sinkdomOfGfp gn',
                                                       let may  = mayNaiveGfp  gn',
                                                       m1 <- nodes g,  x <- suc g n, m2 <- suc trcg m1, m1 /= m2, n /= m1, n /= m2,
                                                       ((m1 ∈ pdom ! x) ∧ (not $ m1 ∈ pmay ! m2))
                                                 ∨     ((m1 ∈ dom ! m2) ∧ (not $ m2 ∈ pmay ! x))
                                                 ∨     ((m1 ∈ pdom ! m2) ∧ (m1 ∈ dom ! m2))
                   ]

        -- pr = exampleSimpleNoUniqueEndNodeWithChoice2
        -- g0 = tcfg pr
        -- g = insEdge (10,1,NoOp)  $ insEdge (6,9,NoOp) g0

myWodFromMay :: forall gr a b. (DynGraph gr) =>  gr a b -> Map (Node, Node) (Set Node)
myWodFromMay graph =  --      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
                      myEntryWodFast graph
                   ⊔ (∐) [ Map.fromList [ ((m1,m2), Set.fromList [n]) ] | (n, m1, m2) <- mywod ]
  where mywod =  [ (n, m1, m2) | cycle <- isinkdomCycles,
                                 length cycle > 1,
                                 let condsInCycle     = condsIn cycle,
                                 let cycleGraph = subgraph cycle graph,
                                 n <- condsInCycle,
                                 let gn   = delSuccessorEdges cycleGraph n,
                                 let pdom = sinkdomOfGfp gn,
                                 let pmay = mayNaiveGfp gn,
                                 let zs = (∏) [ pdom ! x | x <- suc cycleGraph n ],
                                 let ys = (∏) [ pmay ! x | x <- suc cycleGraph n ],
                                 -- traceShow (n, cycleGraph, pdom, pmay, zs, ys) True,
                                 x <- suc cycleGraph n,
                                 m1 <- Set.toList $ pdom ! x,
                                 m1 `elem` cycle,
                                 m1 /= n,
                                 m2 <- cycle,
                                 m2 /= m1, m2 /= n,
                                 (not $ m2 ∈ pmay ! x)  ∨  ((not $ m1 ∈ zs)  ∧  (m2 ∈ ys))
                 ]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG
        entriesFor cycle = [ n | n <- condNodes, not $ n ∊ cycle, [n'] <- [Set.toList $ isinkdom ! n], n' ∊ cycle]
        condsIn cycle    = [ n | n <- cycle, length (suc graph n) > 1]

myCDFromMyDom :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
myCDFromMyDom graph = Map.fromList [ (n, Set.empty) | n <- nodes graph ]
                    ⊔ Map.fromList [ (n, Set.fromList [ m |                xl <- suc graph n,
                                                                           xr <- suc graph n,
                                                                           m <- Set.toList $ dom ! xl,
                                                                           m /= n,
                                                                           not $ m ∈ dom ! xr
                                         ]
                                      )
                                    |  cycle <- isinkdomCycles, length cycle > 1, n <- cycle, n `elem` condNodes ]
  where dom       = myDom graph
        condNodes = [ n | n <- nodes graph, length [ x | x <-  suc graph n] > 1 ]
        isinkdom = isinkdomOfSinkContraction graph
        isinkdomG = fromSuccMap isinkdom :: gr () ()
        isinkdomTrc = trc $ isinkdomG
        isinkdomCycles = scc isinkdomG

wodMyEntryWodMyCDSlice :: forall gr a b. ( DynGraph gr) => gr a b ->  Set Node -> Set Node
wodMyEntryWodMyCDSlice graph = (if cdEdges == cdFromDomEdges then
                                   -- traceShow (length $ nodes graph, Set.size cdFromDomEdges, Set.size cdEdges, foldl (+) 0 (fmap Set.size cdFromDom), foldl (+) 0 (fmap Set.size cd))
                                  id
                                else
                                   -- traceShow (length $ nodes graph, Set.size cdFromDomEdges, Set.size cdEdges, foldl (+) 0 (fmap Set.size cdFromDom), foldl (+) 0 (fmap Set.size cd), graph)
                                  id
                               ) $
                               combinedBackwardSlice graph (invert'' $ nticdF3 graph ⊔ cd) w
  where cdFromDom    = myCDFromMyDom graph
        cd           = myCD graph
        w     = myEntryWodFast graph
        cdEdges        = Set.fromList $ edges $ trc $ (fromSuccMap cd        :: gr () ())
        cdFromDomEdges = Set.fromList $ edges $ trc $ (fromSuccMap cdFromDom :: gr () ())

