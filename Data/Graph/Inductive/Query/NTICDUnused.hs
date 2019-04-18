module Data.Graph.Inductive.Query.NTICDUnused where

import Data.Maybe(fromJust)
import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive

import Unicode
import IRLSOD(CFGNode)
import Program (Program)

import Data.Graph.Inductive.Query.NTICD (cdepGraph, cdepGraphP, sinkPathsFor, inSinkPathAfterFor, SinkPath(..), cyclesInScc)
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
