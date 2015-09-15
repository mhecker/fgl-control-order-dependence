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
import Data.Set.Unicode

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


mhpFor :: DynGraph gr => Program gr -> Map (Node,Node) Bool
mhpFor p@(Program { tcfg, staticThreadOf }) = Map.fromList [ ((n1,n2), mhp n1 n2) | n1 <- nodes tcfg, n2 <- nodes tcfg ]
  where mhp n1 n2
         | staticThreadOf n1 == staticThreadOf n2 = isInMulti ! n1  -- == isInMulti ! n2
         | otherwise                              = (n1,n2) ∈ mhpDiff

        isInMulti = isInMultiThread p
        mhpDiff   = mhpDifferent p
--      lca = lowestCommonAncestor n1 n2


mhpDifferent p@(Program { tcfg }) =
  (㎲⊒)  (Set.fromList $ concat $ [ [(a,b),(b,a)] | a <- nodes tcfg, (b,Spawn) <- lsuc tcfg a ])
       (\mhp -> mhp ⊔ (Set.fromList $ concat [ [(a',b), (b,a')]  | a  <- nodes tcfg,
                                                                   b  <- [ b | (rofl,b) <- Set.toList mhp, rofl == a], -- TODO: Performance
                                                                   a' <- suc trnsclos a])
       )

 where trnsclos = trc tcfg
