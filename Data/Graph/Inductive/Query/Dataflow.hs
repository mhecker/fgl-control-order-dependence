{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Graph.Inductive.Query.Dataflow where



import Unicode

import Algebra.Lattice

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph



-- class (BoundedJoinSemiLattice l) => InitialInformation  l where
--   initial :: l -- initiale Information am Startpunkt
class (BoundedJoinSemiLattice l) => DataflowAnalysis l b where
  transfer :: LEdge b -- Kanten
           -> (l -> l) -- Transfer Funktion



analysis :: forall l b a gr. (Eq l, DataflowAnalysis l b, Graph gr) => gr a b -> l -> Node -> Map Node l
analysis gr initial start = analysisWith (labEdges gr) initialInformation

  where  -- initialInformation :: Map Node l
         initialInformation = Map.fromList $ [(n, (⊥)) | n <- nodes (gr :: gr a b)] ++ [(start, initial)]

         analysisWith :: [LEdge b] -> Map Node l -> Map Node l
         analysisWith []                  information = information
         analysisWith (e@(u,v,label):edges) information
           | t ⊑ (information ! v) = analysisWith edges
                                                  information
           | otherwise             = analysisWith ([ (v,w,label') | (w,label') <- lsuc gr v] ++ edges)
                                                  (Map.insert v ((information ! v) ⊔ t) information)
           where f = transfer e
                 t = f $ (information ! u)
