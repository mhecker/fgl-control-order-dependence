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

import Data.Bool.Unicode
import Data.Eq.Unicode

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
-- import Unicode


clInitFrom :: (Node -> Maybe SecurityLattice) -> (Node -> SecurityLattice)
clInitFrom observability n
  | Nothing <- observability n = (⊥)
  | Just l  <- observability n = l

minimalClassification p@(Program { tcfg, observability }) =
  (㎲⊒) (Map.fromList [ (n, clInitFrom observability n) | n <- nodes tcfg ])
    (\cl -> cl ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre cpdg n])
                               | n <- nodes tcfg])
               ⊔ (Map.fromList [ (n,(∐) [ cl ! c' | m <- Set.toList $ mhp ! n, let c = idom ! (n,m),  c' <- Set.toList $ chop c n])
                               | n <- nodes tcfg])
    )

 where cpdg = concurrentProgramDependenceGraphP p
       idom = idomChef p
       trnsclos = trc tcfg
       mhp :: Map Node (Set Node)
       mhp = Map.fromList [ (n, Set.fromList [ m | ((n',m), True) <- Map.assocs mhpSet, n' == n])
                          | n <- nodes tcfg ]
         where mhpSet = mhpFor p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance


timingClassification p@(Program { tcfg, observability }) =
  (㎲⊒) (Map.fromList [ (n, clInitFrom observability n) | n <- nodes tcfg ],
         Map.fromList [ ((n,m), (⊥))  | ((n,m), True) <- Map.assocs mhp ])
    (\(cl,clt) -> (cl  ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre cpdg n])
                                       | n <- nodes tcfg])
                       ⊔ (Map.fromList [ (n,(∐) [ (clt ! (m,n)) | m <- pre dataConflictGraph n])
                                       | n <- nodes tcfg]),
                   clt ⊔ (Map.fromList [ ((n,m), (∐) [ cl ! c' | let c = idom ! (n,m),
                                                                  c' <- Set.toList $ ((chop c n) ∩ (Set.fromList (pre timing n)))
                                                                                   ∪ ((chop c m) ∩ (Set.fromList (pre timing m)))
                                                     ])
                                       |  ((n,m),True) <- Map.assocs mhp])
                  )
    )
 where cpdg = concurrentProgramDependenceGraphP p
       idom = idomChef p
       mhp = mhpFor p
       trnsclos = trc tcfg
       dataConflictGraph = dataConflictGraphP p
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance




timingClassificationSimple p@(Program { tcfg, observability }) =
  (㎲⊒) (Map.fromList [ (n, clInitFrom observability n)  | n <- nodes tcfg ],
         Map.fromList [ (n, (⊥))       | n <- nodes tcfg ])
    (\(cl,clt) -> (cl  ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre cpdg n])
                                       | n <- nodes tcfg])
                       ⊔ (Map.fromList [ (n,(∐) [ (clt ! m) ⊔ (clt ! n) | m <- pre dataConflictGraph n])
                                       | n <- nodes tcfg]),
                   clt ⊔ (Map.fromList [ (n,(∐) [ (cl ! m) | m <- pre timing n])
                                       | n <- nodes tcfg])
                  )
    )

 where cpdg = concurrentProgramDependenceGraphP p
       idom = idomChef p
       trnsclos = trc tcfg
       dataConflictGraph = dataConflictGraphP p
       timing = timingDependenceGraphP p




isSecureMinimalClassification  p@(Program{ tcfg, observability }) =
       ((∀) (Set.fromList [ n    | n <- nodes tcfg, observability n == Just Low])
            (\n -> cl ! n == Low)
       )
  where cl = minimalClassification p

-- TODO: via ⊑ formulieren
isSecureTimingClassification  p@(Program{ tcfg, observability }) =
       ((∀) (Set.fromList [ n    | n <- nodes tcfg, observability n == Just Low])
            (\n -> cl ! n == Low)
       )
    && ((∀) (Set.fromList [(n,m) | n <- nodes tcfg, observability n == Just Low,
                                   m <- nodes tcfg, observability m == Just Low,
                                   mhp ! (n,m)
                          ]
            )
            (\(n,m) -> (clt ! (n,m) == Low)) 
       )
  where (cl,clt) = timingClassification p
        mhp = mhpFor p

isSecureTimingClassificationSimple p = isSecureTimingClassificationFor cl clt p
  where (cl,clt) = timingClassificationSimple p

-- TODO: via ⊑ formulieren
isSecureTimingClassificationFor cl clt p@(Program{ tcfg, observability }) =
       ((∀) (Set.fromList [ n    | n <- nodes tcfg, observability n == Just Low])
            (\n -> cl ! n == Low)
       )
    && ((∀) (Set.fromList [(n,m) | n <- nodes tcfg, observability n == Just Low,
                                   m <- nodes tcfg, observability m == Just Low,
                                   mhp ! (n,m)
                          ]
            )
            (\(n,m) -> (clt ! m == Low) ∧ (clt ! m == Low))
       )
  where mhp = mhpFor p

 -- TODO: via ⊑ formulieren
isSecureTimingCombinedTimingClassification p@(Program{ tcfg, observability }) =
       ((∀) (Set.fromList [ n    | n <- nodes tcfg, observability n == Just Low])
            (\n -> cl ! n == Low)
       )
    && ((∀) (Set.fromList [(n,m) | n <- nodes tcfg, observability n == Just Low,
                                   m <- nodes tcfg, observability m == Just Low,
                                   mhp ! (n,m)
                          ]
            )
            (\(n,m) ->   (  (clt ! n == Low ) ∧ (clt ! m == Low ))
                      ∨  (  (clt ! n == Low ) ∧ (clt ! m == High) ∧ False) -- Jürgen sagt: in diesem fall würde ein check nix bringen, siehe "jürgenConjecture
                      ∨  (  (clt ! n == High) ∧ (clt ! m == Low ) ∧ False) -- Jürgen sagt: in diesem fall würde ein check nix bringen, siehe "jürgenConjecture"
                      ∨  (  (clt ! m == High) ∧ (clt ! m == High) ∧
                            (∐) [ cl ! c' | let c = idom ! (n,m),
                                        c' <- Set.toList $ ((chop c n) ∩ (Set.fromList (pre timing n)))
                                                         ∪ ((chop c m) ∩ (Set.fromList (pre timing m)))
                                ] == Low
                         )
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



giffhornLSOD p@(Program{ tcfg, observability }) =
    ((∀) [ (n,n')     | n   <- nodes tcfg, observability n  == Just Low,
                        n'  <- nodes tcfg, observability n' == Just High ] (\(n,n') ->
         (¬) (n' ∈ pre bs n)
    ))
    ∧
    ((∀) [ (n,n',n'') | n   <- nodes tcfg,
                        n'  <- nodes tcfg,
                        mhp ! (n,n'),
                        n'' <- nodes tcfg, observability n == Just Low   ] (\(n,n',n'') ->
         ((∃) (def_ n) (\v -> v ∈ (def_ n') ∪ (use_ n')))
         →
         (((¬) (n' ∈ pre bs n'')) ∧
          ((¬) (n  ∈ pre bs n''))
         )
    ))
    ∧
    ((∀) [ (n,n')     | n   <- nodes tcfg,
                        n'  <- nodes tcfg,
                        mhp ! (n,n')                                     ] (\(n,n') ->
         (¬) (observability n  == Just Low) ∨
         (¬) (observability n' == Just Low)
    ))
  where
       def_ = def tcfg
       use_ = use tcfg
       cpdg = concurrentProgramDependenceGraphP p
       bs = trc cpdg -- TODO: name :)
       mhp = mhpFor p
