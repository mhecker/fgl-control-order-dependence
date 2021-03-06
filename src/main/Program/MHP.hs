{-# LANGUAGE NamedFieldPuns #-}
module Program.MHP where


import Algebra.Lattice

import Unicode

import Program
import Program.MultiThread
import IRLSOD

-- import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS (reachable)


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Query.Dataflow
import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Query.TransClos




-- data MhpInformation = MhpInformation (Set (Node,Node))
type MhpInformation = Set (Node,Node)

-- instance JoinSemiLattice MhpInformation where
--  join  (MhpInformation mhp )
--        (MhpInformation mhp') = MhpInformation (mhp ⊔ mhp')

-- instance BoundedJoinSemiLattice MhpInformation where



mhpSetFor :: DynGraph gr => Program gr -> Set (Node,Node)
mhpSetFor p@(Program { tcfg }) =
     Set.fromList [ (n1,n2) | n1 <- nodes tcfg, n2 <- nodes tcfg, sameThread n1 n2, isInMulti ! n1 ]
   ⊔ Set.filter (\(n1,n2) -> not $ sameThread n1 n2) mhpDiff
  where sameThread n1 n2 = (threads1 == threads2) ∧ (Set.size threads1 == 1)
          where threads1 = threadsOfMap ! n1 
                threads2 = threadsOfMap ! n2
        isInMulti = isInMultiThread p
        mhpDiff   = mhpDifferent p
        threadsOfMap = threadsOf p


mhpDifferentOld p@(Program { tcfg }) =
  (㎲⊒)  (Set.fromList $ concat $ [ [(a,b),(b,a)] | a <- nodes tcfg, (b,Spawn) <- lsuc tcfg a ])
       (\mhp -> mhp ⊔ (Set.fromList $ concat [ [(a',b), (b,a')]  | a  <- nodes tcfg,
                                                                   a' <- DFS.reachable a tcfg,
                                                                   b  <- [ b | (rofl,b) <- Set.toList mhp, rofl == a] -- TODO: Performance
                                             ]
                      )
       )

 where
       threadsOfMap = threadsOf p


mhpDifferentSlow p@(Program { tcfg }) =
  (㎲⊒)  (Set.fromList $ concat $ [ if (e /= NoOp) then (error $ "invalid spawn-node successor " ++ show (b,e)) else
                                    [(a,b),(b,a)] | n <- nodes tcfg, (a,Spawn) <- lsuc tcfg n, (b,e) <- lsuc tcfg n, e /= Spawn ])
       (\mhp -> mhp ⊔ (Set.fromList $ concat [ [(a',b), (b,a')]  | a  <- nodes tcfg,
                                                                   a' <- DFS.reachable a tcfg,
                                                                   b  <- [ b | (rofl,b) <- Set.toList mhp, rofl == a] -- TODO: Performance
                                             ]
                      )
       )

 where
       threadsOfMap = threadsOf p

mhpDifferent p@(Program { tcfg }) = left ∪ right
  where left  = Set.fromList [ (a',b') | (n,a,Spawn) <- labEdges tcfg, (b,e) <- lsuc tcfg n, e /= Spawn, a' <- DFS.reachable a tcfg, b' <- DFS.reachable b tcfg ]
        right = Set.map (\(n,m) -> (m,n)) left
