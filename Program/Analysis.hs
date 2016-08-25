{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}

module Program.Analysis where


import Algebra.Lattice

import Unicode

import Program
import Program.CDom
import Program.MHP
-- import IRLSOD

-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Graph

import Data.Util

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

import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.ProgramDependence
import Data.Graph.Inductive.Query.DataConflict
import Data.Graph.Inductive.Query.TimingDependence

import IRLSOD
-- import Unicode

type SecurityAnalysis gr =  DynGraph gr => Program gr -> Bool

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
       idom = idomMohrEtAl p
       mhp = mhpFor p
       trnsclos = trc tcfg
       dataConflictGraph = dataConflictGraphP p
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance



timingClassificationAtUses p@(Program { tcfg, observability }) =
  (㎲⊒) (Map.fromList [ (n, clInitFrom observability n) | n <- nodes tcfg ],
         Map.fromList [ ((n,m), (⊥))  | ((n,m), True) <- Map.assocs mhp ])
    (\(cl,clt) -> (cl  ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre cpdg n])
                                       | n <- nodes tcfg])
                       ⊔ (Map.fromList [ (n,(∐) [ (clt ! (m,m')) | m  <- ideps n x,
                                                                    m' <- ideps n x,
                                                                   mhp ! (m,m')
                                                 ]
                                         )
                                       | n <- nodes tcfg, x <- Set.toList (use tcfg n)   ])
                       ⊔ (Map.fromList [ (n,(∐) [ (clt ! (m,m')) | m  <- ideps n x,
                                                                    m' <- ddeps n x,
                                                                   mhp ! (m,m')
                                                 ]
                                         )
                                       | n <- nodes tcfg, x <- Set.toList (use tcfg n)   ])
                   ,
                   clt ⊔ (Map.fromList [ ((n,m), (∐) [ cl ! c' | let c = idom ! (n,m),
                                                                  c' <- Set.toList $ ((chop c n) ∩ (Set.fromList (pre timing n)))
                                                                                   ∪ ((chop c m) ∩ (Set.fromList (pre timing m)))
                                                     ])
                                       |  ((n,m),True) <- Map.assocs mhp])
                  )
    )
 where ddeps n x = [ m | (m,DataDependence)        <- lpre cpdg n, x `Set.member` def tcfg m ]
       ideps n x = [ m | (m,InterThreadDependence) <- lpre cpdg n, x `Set.member` def tcfg m ]
       cpdg = concurrentProgramDependenceGraphP p
       idom = idomMohrEtAl p
       mhp = mhpFor p
       trnsclos = trc tcfg
       dataConflictGraph = dataConflictGraphP p
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance



timingClassificationDomPaths p@(Program { tcfg, observability, entryOf, mainThread }) =
  (㎲⊒) (Map.fromList [ (n, clInitFrom observability n) | n <- nodes tcfg ],
         Map.fromList [ ((a,b), (⊥))  | n <- nodes tcfg,
                                        (a,b) <- if (n `Map.member` dom) then [ (n,n), (dom ! n, n) ]
                                                                         else [ (n,n) ]
                      ])
    (\(cl,cle) -> (cl  ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre cpdg n])
                                       | n <- nodes tcfg])
                       ⊔ (Map.fromList [ (n,(∐) [ cltFromCle dom idom cle (n,m)  | m <- pre dataConflictGraph n ])
                                       | n <- nodes tcfg]),
                   cle ⊔ (Map.fromList [ ((a,b), (∐) [ cl ! c' | c' <- Set.toList $ chop a b ∩ (Set.fromList (pre timing b)) ] )
                                       |  n <- nodes tcfg,
                                          (a,b) <- if (n `Map.member` dom) then [ (n,n), (dom ! n, n) ]
                                                                           else [ (n,n) ]
                                       ])
                  )
    )
 where dom :: Map Node Node
       dom = Map.fromList $ iDom tcfg (entryOf mainThread)

       cpdg = concurrentProgramDependenceGraphP p
       idom = idomMohrEtAl p
       mhp = mhpFor p
       trnsclos = trc tcfg
       dataConflictGraph = dataConflictGraphP p
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance


cltFromCle dom idom cle (n,m) = (∐) [ cle ! (a,b)
                                  | (a,b) <-   (consecutive $ [ y |  x <- domPathBetween dom n c , y <- [x,x] ])
                                           ++  (consecutive $ [ y |  x <- domPathBetween dom m c , y <- [x,x] ])
                                  ]
  where c = idom ! (n,m)


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



isSecureMinimalClassification :: SecurityAnalysis gr
isSecureMinimalClassification  p@(Program{ tcfg, observability }) =
       ((∀) (Set.fromList [ n    | n <- nodes tcfg, observability n == Just Low])
            (\n -> cl ! n == Low)
       )
  where cl = minimalClassification p

-- TODO: via ⊑ formulieren


isSecureTimingClassificationAtUses :: SecurityAnalysis gr
isSecureTimingClassificationAtUses p   = isSecureTimingClassificationFor cl clt p
  where (cl,clt) = timingClassificationAtUses p


isSecureTimingClassification :: SecurityAnalysis gr
isSecureTimingClassification p         = isSecureTimingClassificationFor cl clt p
  where (cl,clt) = timingClassification p

isSecureTimingClassificationDomPaths :: SecurityAnalysis gr
isSecureTimingClassificationDomPaths p = isSecureTimingClassificationFor cl clt p
  where (cl,cle) = timingClassificationDomPaths p
        clt      = Map.fromList [((n,m), cltFromCle dom idom cle (n,m)) | n <- nodes $ tcfg p,
                                                                          m <- nodes $ tcfg p,
                                                                          mhp ! (n,m) ]
          where dom :: Map Node Node
                dom = Map.fromList $ iDom (tcfg p) (entryOf p $ mainThread p)

                idom = idomMohrEtAl p
                mhp = mhpFor p

isSecureTimingClassificationFor ::  Map Node SecurityLattice -> Map (Node, Node) SecurityLattice  -> SecurityAnalysis gr
isSecureTimingClassificationFor cl clt  p@(Program{ tcfg, observability }) =
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
  where mhp = mhpFor p


-- TODO: via ⊑ formulieren
isSecureTimingClassificationSimple :: SecurityAnalysis gr
isSecureTimingClassificationSimple p@(Program{ tcfg, observability }) =
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
        (cl,clt) = timingClassificationSimple p

 -- TODO: via ⊑ formulieren
isSecureTimingCombinedTimingClassification :: SecurityAnalysis gr
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


giffhornClassification p@(Program { tcfg, observability }) = (cl, inf)
  where cl  = (㎲⊒)  (Map.fromList [ (n, clInitFrom observability n)  | n <- nodes tcfg ])
                        (\cl -> cl      ⊔ (Map.fromList [ (n,(∐) [ cl ! m  | m <- pre cpdg n])
                                                                            | n <- nodes tcfg])
                        )
        inf = (㎲⊒) ((Map.fromList [ (n, False) | n  <- nodes tcfg ]) ⊔
                     (Map.fromList [ (m, True)  | n  <- nodes tcfg,
                                                  n' <- nodes tcfg,
                                                  mhp ! (n,n'),
                                                  (∃) (def_ n) (\v -> v ∈ (def_ n') ∪ (use_ n')),
                                                  m <- [n,n'] ] )
                    )
                    (\clData -> clData  ⊔ (Map.fromList [ (n,(∐) [ clData ! m  | m <- pre cpdg n])
                                                                               | n <- nodes tcfg])
                    )
        def_ = def tcfg
        use_ = use tcfg
        cpdg = concurrentProgramDependenceGraphP p
        mhp = mhpFor p


isSecureGiffhornClassification :: SecurityAnalysis gr
isSecureGiffhornClassification p@(Program{ tcfg, observability }) =
    ((∀) (Set.fromList [ n    | n <- nodes tcfg, observability n == Just Low])
            (\n -> cl  ! n == Low)
    )
    ∧
    ((∀) (Set.fromList [ n    | n <- nodes tcfg, observability n == Just Low])
            (\n -> inf ! n == False)
    )
    ∧
    ((∀) (Set.fromList [(n,m) | n <- nodes tcfg, observability n == Just Low,
                                m <- nodes tcfg, observability m == Just Low,
                                mhp ! (n,m)
                          ]
         )
         (\(n,m) -> False)
    )
  where (cl, inf) = giffhornClassification p
        mhp = mhpFor p



giffhornLSOD :: SecurityAnalysis gr
giffhornLSOD p@(Program{ tcfg, observability }) =
    ((∀) [ (n,n')     | n   <- nodes tcfg, observability n  == Just Low,
                        n'  <- nodes tcfg, observability n' == Just High ] (\(n,n') ->
         (¬) (n' ∈ pre bs n)
    ))
    ∧
    ((∀) [ (n,n',n'') | n   <- nodes tcfg,
                        n'  <- nodes tcfg,
                        mhp ! (n,n'),
                        n'' <- nodes tcfg, observability n'' == Just Low   ] (\(n,n',n'') ->
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

observableNodes p@(Program{ tcfg, observability }) =
    [ n  | n   <- nodes tcfg, observability n  == Just Low ]

conflictinObservableNodes p@(Program{ tcfg, observability }) =
    [(n,m) | n <- nodes tcfg, observability n == Just Low,
             m <- nodes tcfg, observability m == Just Low,
             mhp ! (n,m)
    ]
  where  mhp = mhpFor p
