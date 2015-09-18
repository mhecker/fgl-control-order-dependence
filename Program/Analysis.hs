{-# LANGUAGE NamedFieldPuns #-}
module Program.Analysis where


import Algebra.Lattice

import Unicode

import Program
import Program.CDom
import Program.MHP
-- import IRLSOD

-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Graph


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Set.Unicode
import Data.Bool.Unicode

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Query.Dataflow
import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Query.TransClos

import Data.Graph.Inductive.Query.ProgramDependence
import Data.Graph.Inductive.Query.DataConflict
import Data.Graph.Inductive.Query.TimingDependence

import IRLSOD




minimalClassification p@(Program { tcfg, clInit }) =
  (㎲⊒) (Map.fromList [ (n, clInit n) | n <- nodes tcfg ])
    (\cl -> cl ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre pdg n])
                               | n <- nodes tcfg])
               ⊔ (Map.fromList [ (n,(∐) [ cl ! c' | m <- Set.toList $ mhp ! n, let c = idom ! (n,m),  c' <- Set.toList $ chop c n])
                               | n <- nodes tcfg])
    )

 where pdg = programDependenceGraphP p
       idom = idomChef p
       trnsclos = trc tcfg
       mhp :: Map Node (Set Node)
       mhp = Map.fromList [ (n, Set.fromList [ m | ((n',m), True) <- Map.assocs mhpSet, n' == n])
                          | n <- nodes tcfg ]
         where mhpSet = mhpFor p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance


timingClassification p@(Program { tcfg, clInit }) =
  (㎲⊒) (Map.fromList [ (n, clInit n)      | n <- nodes tcfg ],
         Map.fromList [ ((n,m), Undefined) | ((n,m), True) <- Map.assocs mhp ])
    (\(cl,clt) -> (cl  ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre pdg n])
                                       | n <- nodes tcfg])
                       ⊔ (Map.fromList [ (n,(∐) [ (cl ! m) ⊔ (clt ! (m,n)) | m <- pre dataConflictGraph n])
                                       | n <- nodes tcfg]),
                   clt ⊔ (Map.fromList [ ((n,m), (∐) [ cl ! c' | let c = idom ! (n,m),
                                                                  c' <- Set.toList $ ((chop c n) ∩ (Set.fromList (pre timing n)))
                                                                                   ∪ ((chop c m) ∩ (Set.fromList (pre timing m)))
                                                     ])
                                       |  ((n,m),True) <- Map.assocs mhp])
                  )
    )
 where pdg = programDependenceGraphP p
       idom = idomChef p
       mhp = mhpFor p
       trnsclos = trc tcfg
       dataConflictGraph = dataConflictGraphP p
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance




timingClassificationSimple p@(Program { tcfg, clInit }) =
  (㎲⊒) (Map.fromList [ (n, clInit n)  | n <- nodes tcfg ],
         Map.fromList [ (n, Undefined) | n <- nodes tcfg ])
    (\(cl,clt) -> (cl  ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre pdg n])
                                       | n <- nodes tcfg])
                       ⊔ (Map.fromList [ (n,(∐) [ (cl ! m) ⊔ (clt ! m) ⊔ (clt ! n) | m <- pre dataConflictGraph n])
                                       | n <- nodes tcfg]),
                   clt ⊔ (Map.fromList [ (n,(∐) [ (cl ! m) | m <- pre timing n])
                                       | n <- nodes tcfg])
                  )
    )

 where pdg = programDependenceGraphP p
       idom = idomChef p
       trnsclos = trc tcfg
       dataConflictGraph = dataConflictGraphP p
       timing = timingDependenceGraphP p




isSecureTimingClassification  p@(Program{ tcfg, clInit }) =
       ((∀) (Set.fromList [ n    | n <- nodes tcfg, clInit n == Low])
            (\n -> clInit n == cl ! n)
       )
    && ((∀) (Set.fromList [(n,m) | n <- nodes tcfg, clInit n == Low,
                                   m <- nodes tcfg, clInit m == Low,
                                   mhp ! (n,m)
                          ]
            )
            (\(n,m) -> (clt ! (n,m) == Low)) -- TODO: via ⊑ formulieren
       )
  where (cl,clt) = timingClassification p
        mhp = mhpFor p

isSecureTimingClassificationSimple p = isSecureTimingClassificationFor cl clt
  where (cl,clt) = timingClassificationSimple p

isSecureTimingClassificationFor cl clt p@(Program{ tcfg, clInit }) =
       ((∀) (Set.fromList [ n    | n <- nodes tcfg, clInit n == Low])
            (\n -> clInit n == cl ! n) -- TODO: via ⊑ formulieren
       )
    && ((∀) (Set.fromList [(n,m) | n <- nodes tcfg, clInit n == Low,
                                   m <- nodes tcfg, clInit m == Low,
                                   mhp ! (n,m)
                           ]
            )
            (\(n,m) -> (clt ! m == Low) ∧ (clt ! m == Low)) -- TODO: via ⊑ formulieren
       )
  where mhp = mhpFor p
