{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}


module Data.Graph.Inductive.Query.DataDependence where




import Unicode
import IRLSOD

import Algebra.Lattice

import Data.Char

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.Dataflow


{- Es passt schon die default Instanziierung:
   instance BoundedJoinSemiLattice (Map Var (Set Node))
-}

-- instance Enum Var where
--   toEnum x
--    | ord 'a' <= x && x <= ord 'z' = [chr x]
--    | otherwise = undefined
--   fromEnum [x]
--    | 'a' <= x && x <= 'z' = ord x
--   fromEnum _   = undefined
-- instance Bounded Var where
--   minBound = "a"
--   maxBound = "z"

-- allValues :: (Bounded t, Enum t) =>  [t]
-- allValues = [minBound..maxBound]

-- -- Achtung: funktioniert nicht für (Set CFGEdge), nur für (Set (LEdge CFGEdge))
-- instance Ord CFGEdge where
--   (Guard  b1 _) <= (Guard  b2 _) = b1 <= b2
--   (Assign x1 _) <= (Assign x2 _) = x1 <= x2
--   (Spawn)       <= (Spawn)       = True

--   (Guard  _ _)  <= e2            = True
--   (Assign _ _)  <= (Guard  _ _)  = False
--   (Assign _ _)  <= e2            = True

--   (Spawn)       <= (Guard  _ _)  = False
--   (Spawn)       <= (Assign _ _)  = False
--   (Spawn)       <= e2            = True

-- instance Ord CFGEdge where
--   e1@(n1,n1',Guard  b1 _) <= e2@(n2,n2',Guard  b2 _) = (n1,n2,b1) <= (n1',n2',b2)
--   e1@(n1,n1',Assign x1 _) <= e2@(n2,n2',Assign x2 _) = (n1,n2,x1) <= (n1',n2',x2)
--   e1@(n1,n1',Spawn)      <= e2@(n2,n2',Spawn)        = (n1,n2)    <= (n1',n2')

--   e1@(n1,n1',Guard  _ _)  <= e2                      = True
--   e1@(n1,n1',Assign _ _)  <= e2                      = True

instance InitialInformation (Map Var (Set (LEdge CFGEdge))) where
  initial = Map.fromList []

instance DataflowAnalysis (Map Var (Set (LEdge CFGEdge))) CFGEdge where
  transfer e@(_,_,Guard _ sf)  reachingDefs = reachingDefs
  transfer e@(_,_,Assign x sf) reachingDefs = Map.insert x (Set.singleton e) reachingDefs
  transfer e@(_,_,Spawn)       _            = undefined



dataDependence :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
dataDependence graph entry = Map.fromList [
      (n, Set.fromList $
          [ reachedFromN | reachedFromN <- nodes graph,
                           let edges :: Map Var (Set (LEdge CFGEdge))
                               edges = reaching ! reachedFromN,
                           let nodes :: Map Var (Set (Node))
                               nodes = fmap (\set -> Set.map (\(n,_,_) -> n) set) edges,
                           var <- Set.toList $ use graph reachedFromN,
                           n `Set.member` (nodes ! var)]
      )
     | n <- nodes graph
    ]
  where reaching :: Map Node (Map Var (Set (LEdge CFGEdge)))
        reaching = analysis graph entry






-- dataDependence graph entry label exit =
--     Map.fromList
--     [ (n, Set.fromList $
--           [ controlledByN | controlledByN <- nodes graph,
--                             n `Set.member` (postDomFronts ! controlledByN),
--                             n /= controlledByN])
--      | n <- nodes graph
--     ]
--   where postDomFronts = domFront (grev $ insEdge (entry, exit, label) graph) exit
