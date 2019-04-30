{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
module Data.Graph.Inductive.Query.NTICD.Util where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.Graph.Inductive.Graph


import Unicode





combinedBackwardSliceSlow :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map (Node, Node) (Set Node) -> Set Node -> Set Node
combinedBackwardSliceSlow graph cd od = \ms -> (㎲⊒) ms f
  where f slice = slice
                ⊔ Set.fromList [ n | m <- Set.toList slice, n <- Set.toList $ cd ! m ]
                ⊔ Set.fromList [ n | m1 <- Set.toList slice, m2 <- Set.toList slice, m1 /= m2, n <- Set.toList $ Map.findWithDefault Set.empty (m1,m2) od ]

combinedBackwardSlice :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map (Node, Node) (Set Node) -> Set Node -> Set Node
combinedBackwardSlice graph cd od = \ms ->
     let result = slice Set.empty ms 
         slice s workset
             | Set.null workset = s
             | otherwise        = slice s' workset'
           where (m, workset0) = Set.deleteFindMin workset
                 s'  = Set.insert m s
                 new = (fromOD ∪ fromCD) ∖ s'
                 workset' = workset0 ∪ new

                 fromCD = Map.findWithDefault Set.empty m cd
                 fromOD
                   | Map.null od  = Set.empty
                   | otherwise    = (∐) [ (Map.findWithDefault Set.empty (m,m') od ) ∪ (Map.findWithDefault Set.empty (m', m) od) | m' <- Set.toList s ]
     in result
