{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}

module Program.TransitionSystem where


-- import Algebra.Lattice

import Unicode

import Program
-- import Program.CDom
-- import Program.MHP
import IRLSOD

-- -- import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph

-- import Data.Util

import Data.Maybe (fromJust)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- import Data.Bool.Unicode
-- import Data.Eq.Unicode

-- -- import Data.Graph.Inductive.Basic
-- import Data.Graph.Inductive.Graph
-- -- import Data.Graph.Inductive.Util
-- -- import Data.Graph.Inductive.Query.Dataflow
-- import Data.Graph.Inductive.Query.Dominators
-- import Data.Graph.Inductive.Query.TransClos

-- import Data.Graph.Inductive.Query.ProgramDependence
-- import Data.Graph.Inductive.Query.DataConflict
-- import Data.Graph.Inductive.Query.TimingDependence

-- import IRLSOD
-- -- import Unicode


data Dependent               = InitialVar Var
                             | Edge (LEdge Bool) (Set Dependent) -- For total generality, one might have to use "Edge (LEdge CFGEdge) (Set Dependent)" Instead

                               deriving (Eq,Ord,Show)
type SymbolicDefUseNode      = (Map Var (Set Dependent), Node, Set Dependent)
type SymbolicDefUseSystem gr = gr SymbolicDefUseNode ()


fromSimpleProgram :: DynGraph gr => Program gr -> SymbolicDefUseSystem gr
fromSimpleProgram p@(Program { tcfg, staticThreads, mainThread, entryOf, exitOf })
    | Set.size staticThreads /= 1 = error "not simple: more than one thread"
    | otherwise                   = unrollFrom tcfg (mkGraph [(entry, initial)] [])
  where entry   = entryOf mainThread
        exit    = exitOf  mainThread
        cfg     = tcfg
        initial = (Map.fromList [ (v, Set.fromList [InitialVar v] ) | v <- Set.toList $ vars p ], entry, Set.empty)


unrollFrom :: DynGraph gr => gr CFGNode CFGEdge -> SymbolicDefUseSystem gr -> SymbolicDefUseSystem gr
unrollFrom cfg system
    | noNodes newSystem == noNodes system &&
      noEdges newSystem == noEdges system     = system
    | otherwise                               = unrollFrom cfg newSystem
  where noEdges g = length $ edges g
        newSystem = mkGraph allNodes [ (fromJust $ lookup nl  allNodes',
                                            fromJust $ lookup nl' allNodes',
                                            ()
                                           ) | (nl,nl',()) <- allEdges
                                     ]
        allEdges = [ (nl,nl',()) | (i,nl@(varDeps, nCfg, controlDeps)) <- labNodes system,
                                   (nCfg',eCfg) <- lsuc cfg nCfg,
                                   let nl' = case eCfg of
                                               Guard  b _ -> (varDeps,
                                                              nCfg',
                                                              controlDeps ∪
                                                              Set.fromList [ Edge (nCfg,nCfg',b)
                                                                                  (Set.fromList [ d | v <- Set.toList $ useE eCfg,
                                                                                                      d <- Set.toList $ varDeps ! v ])
                                                                           ]
                                                             )
                                               Assign _ _ -> ((Map.fromList [ (d, (Set.map InitialVar $ useE eCfg)
                                                                                  ∪
                                                                                  controlDeps
                                                                              )
                                                                            | d <- Set.toList $ defE eCfg ]
                                                              ) `Map.union` varDeps,
                                                              nCfg',
                                                              controlDeps)
                                               NoOp       -> (varDeps, nCfg', controlDeps)
                                               _          -> error "not simple"

                   ]
        allNodes = zip [1..]
                       (Set.toList $ (Set.fromList [ nl  | (nl,_  ,_) <- allEdges ])
                                   ∪ (Set.fromList [ nl' | (_ ,nl',_) <- allEdges ]))
        allNodes' = fmap (\(a,b) -> (b,a)) allNodes


varsIn :: Dependent -> Set Var
varsIn (InitialVar v)                       = Set.fromList [v]
varsIn (Edge _ deps)  = Set.unions $ Set.toList $ Set.map varsIn deps

secureSymbolicDefUseSystem :: Graph gr => Node -> Set Var -> Set Var -> SymbolicDefUseSystem gr -> Bool
secureSymbolicDefUseSystem exit low high system = (∀) exitstates (\(varDeps, _,_) ->
                                (∀) low (\l -> (Set.unions $ Set.toList $ Set.map varsIn (varDeps ! l)) ⊆ low)
                              )
  where exitstates = [ nl | (i,nl@(_,nCfg,_)) <- labNodes system,
                            nCfg == exit
                     ]


secureSimple :: DynGraph gr => Set Var -> Set Var -> Program gr -> Bool
secureSimple low high p@(Program { mainThread, exitOf }) = secureSymbolicDefUseSystem exit low high system
  where system  = fromSimpleProgram p
        exit    = exitOf  mainThread

rofl :: Ord a => a -> a
rofl = id
