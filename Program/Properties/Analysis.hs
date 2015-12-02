{-# LANGUAGE NamedFieldPuns #-}

module Program.Properties.Analysis where

import Algebra.Lattice
import Unicode

import IRLSOD(SecurityLattice(..))

import Program
import Program.MHP
import Program.Analysis

import Program.Examples
import Program.Generator

import Program.CDom


import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.Dominators

import Data.Graph.Inductive.Query.DataConflict (dataConflictGraphP)
import Data.Graph.Inductive.Query.TimingDependence (timingDependenceGraphP)


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set



instance Show (Program gr) where
  show p = "rofl"

isAtLeastAsPreciseAs :: (Program Gr -> Bool) -> (Program Gr -> Bool) -> GeneratedProgram -> Bool
isAtLeastAsPreciseAs a1 a2 generated = a2 p ⊑ a1 p
  where p = toProgram generated


timingDDomPathsIsTiming :: Program Gr => Bool
timingDDomPathsIsTiming p@(Program{ tcfg, entryOf, mainThread }) =
            (cl   == cl')
          ∧ (clt  == Map.fromList [((n,m), clt' (n,m)) | n <- nodes tcfg,
                                                         m <- nodes tcfg,
                                                         mhp ! (n,m) ])
  where (cl , clt) = timingClassification p
        (cl', cle) = timingClassificationDomPaths p
        clt' = cltFromCle dom idom cle

        dom :: Map Node Node
        dom = Map.fromList $ iDom tcfg (entryOf mainThread)

        idom = idomChef p
        mhp = mhpFor p


jürgenConjecture p@(Program{ tcfg, observability }) =
        (∀) (Set.fromList [(n,m) | n <- nodes tcfg, observability n == Just Low,
                                   m <- nodes tcfg, observability m == Just Low,
                                   mhp ! (n,m)
                          ]
            )
            (\(n,m) -> (((clt ! n == Low) ∧ (clt ! m == High))
                        →
                        ((∐) [ cl ! c' | let c = idom ! (n,m), c' <- Set.toList $ ((chop c m) ∩ (Set.fromList (pre timing m))) ] == High)
                       )
                    && (((clt ! n == High) ∧ (clt ! m == Low))
                        →
                        ((∐) [ cl ! c' | let c = idom ! (n,m), c' <- Set.toList $ ((chop c n) ∩ (Set.fromList (pre timing n))) ] == High)
                       )
            )
  where (cl,clt) = timingClassificationSimple p
        idom = idomChef p
        mhp = mhpFor p
        trnsclos = trc tcfg
        dataConflictGraph = dataConflictGraphP p
        timing = timingDependenceGraphP p
        chop :: Node -> Node -> Set Node
        chop s t =  (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance
