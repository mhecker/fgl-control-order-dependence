{-# LANGUAGE NamedFieldPuns #-}
module Program.MHP where


import Algebra.Lattice

import Unicode

import Program
import Program.MultiThread
import IRLSOD

-- import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph


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




simonMhpFor :: DynGraph gr => Program gr -> Map (Node,Node) Bool
simonMhpFor p@(Program { tcfg }) = Map.fromList [ ((n1,n2), mhp n1 n2) | n1 <- nodes tcfg, n2 <- nodes tcfg ]
  where mhp n1 n2
           | (threads1 == threads2) ∧ (Set.size threads1 == 1) = isInMulti ! n1  -- == isInMulti ! n2
           | otherwise                                         = (n1,n2) ∈ mhpDiff
          where threads1 = threadsOfMap ! n1 
                threads2 = threadsOfMap ! n2
        isInMulti = isInMultiThread p
        mhpDiff   = mhpDifferentSimon p
        threadsOfMap = threadsOf p


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


mhpFor :: DynGraph gr => Program gr -> Map (Node,Node) Bool
mhpFor p@(Program { tcfg }) = Map.fromList [ ((n1,n2), mhp n1 n2) | n1 <- nodes tcfg, n2 <- nodes tcfg ]
  where mhp n1 n2
           | (threads1 == threads2) ∧ (Set.size threads1 == 1) = isInMulti ! n1  -- == isInMulti ! n2
           | otherwise                                         = (n1,n2) ∈ mhpDiff
          where threads1 = threadsOfMap ! n1 
                threads2 = threadsOfMap ! n2
        isInMulti = isInMultiThread p
        mhpDiff   = mhpDifferent p
        threadsOfMap = threadsOf p



mhpDifferent p@(Program { tcfg }) =
  (㎲⊒)  (Set.fromList $ concat $ [ [(a,b),(b,a)] | a <- nodes tcfg, (b,Spawn) <- lsuc tcfg a ])
       (\mhp -> mhp ⊔ (Set.fromList $ concat [ [(a',b), (b,a')]  | a  <- nodes tcfg,
                                                                   b  <- [ b | (rofl,b) <- Set.toList mhp, rofl == a], -- TODO: Performance
                                                                   a' <- suc trnsclos a,
                                                                   not $ Set.null $ (threadsOfMap ! a') ⊓ (threadsOfMap ! a) 
                                             ]
                      )
       )

 where trnsclos = trc tcfg
       threadsOfMap = threadsOf p


mhpDifferentSimon p@(Program { tcfg }) =
  (㎲⊒)  (Set.fromList $ concat $ [ if (e /= NoOp) then (error $ "invalid spawn-node successor " ++ show (b,e)) else
                                    [(a,b),(b,a)] | n <- nodes tcfg, (a,Spawn) <- lsuc tcfg n, (b,e) <- lsuc tcfg n, e /= Spawn ])
       (\mhp -> mhp ⊔ (Set.fromList $ concat [ [(a',b), (b,a')]  | a  <- nodes tcfg,
                                                                   b  <- [ b | (rofl,b) <- Set.toList mhp, rofl == a], -- TODO: Performance
                                                                   a' <- suc trnsclos a,
                                                                   not $ Set.null $ (threadsOfMap ! a') ⊓ (threadsOfMap ! a) 
                                             ]
                      )
       )

 where trnsclos = trc tcfg
       threadsOfMap = threadsOf p
