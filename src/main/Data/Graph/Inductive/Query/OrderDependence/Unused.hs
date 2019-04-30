{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.OrderDependence.Unused where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive


import Unicode


import Data.Graph.Inductive.Util (fromSuccMap)
import Data.Graph.Inductive.Query.PostDominance (imdomOfTwoFinger7)
import Data.Graph.Inductive.Query.NTICDUnused (possibleIntermediateNodesFromiXdom)


{- this algorithm does *not* work, see: Program.Examples.dodSuperFastCounterExample6 -}
dodSuperFast :: forall gr a b. (DynGraph gr) => gr a b -> Map (Node,Node) (Set Node)
dodSuperFast graph =
      Map.fromList [ ((m1,m2), Set.empty) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2 ]
    ⊔ Map.fromList [ ((m1,m2), Set.fromList [ n | n <- condNodes,
                                                  n /= m1, n /= m2,
                                                  m1 ∊ (suc imdomTrc n),
                                                  m2 ∊ (suc imdomTrc n),
                                                  (∃) (suc graph n) (\x -> mustBeforeAny (m1,m2,x)),
                                                  (∃) (suc graph n) (\x -> mustBeforeAny (m2,m1,x))
                                      ]
                     ) | m1 <- nodes graph, m2 <- nodes graph, m1 /= m2
                  ]
  where imdom = imdomOfTwoFinger7 graph
        pis   = possibleIntermediateNodesFromiXdom graph imdom
        imdomTrc = trc $ (fromSuccMap imdom :: gr () ())
        mustBeforeAny (m1,m2,x) = mustBeforeAnySeen (Set.fromList [x]) x
          where mustBeforeAnySeen seen n
                  | n == m2 = False
                  | n == m1 = True
                  | Set.null next = False
                  | m2 ∈ toNext = False
                  | otherwise = mustBeforeAnySeen (Set.insert n seen) n'
                      where next = imdom ! n
                            toNext   = pis ! n
                            [n']     = Set.toList next
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
