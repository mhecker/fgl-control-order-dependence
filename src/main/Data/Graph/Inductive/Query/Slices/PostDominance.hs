module Data.Graph.Inductive.Query.Slices.PostDominance where

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive


import Unicode
import Util(fromSet)

import Data.Graph.Inductive.Util (delSuccessorEdges, controlSinks)
import Data.Graph.Inductive.Query.PostDominance (isinkdomOfTwoFinger8ForSinks, isinkdomOfTwoFinger8, imdomOfTwoFinger7)


ntscdNTSODSliceViaIMDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdNTSODSliceViaIMDom graph msS =  Set.fromList [ n | n <- rdfs ms graph', imdom' ! n == Nothing]
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        imdom' = fmap fromSet $ imdomOfTwoFinger7 graph'


nticdNTIODSliceViaISinkDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODSliceViaISinkDom graph msS =  Set.fromList [ n | n <- rdfs ms graph', isinkdom' ! n == Nothing]
  where ms = Set.toList msS
        graph' = foldr (flip delSuccessorEdges) graph ms
        isinkdom' = isinkdomOfTwoFinger8ForSinks sinks' sinkNodes' nonSinkCondNodes' graph'
          where sinks'     =  controlSinks graph'
                sinkNodes' = (∐) [ Set.fromList sink | sink <- sinks']
                nonSinkCondNodes' = Map.fromList [ (n, succs) | n <- nodes graph', not $ n ∈ sinkNodes', let succs = suc graph' n, length succs > 1 ]

wodTEILSliceViaISinkDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wodTEILSliceViaISinkDom g msS =  Set.fromList [ n | n <- nodes g'', isinkdom'' ! n == Nothing]
  where ms = Set.toList msS
        g''   = foldr (flip delSuccessorEdges) g' ms
          where  toMs   = rdfs ms g
                 g' = subgraph toMs g

        isinkdom'' = fmap fromSet $ isinkdomOfTwoFinger8 g''

wccSliceViaISinkDom :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
wccSliceViaISinkDom g msS =  Set.fromList [ n | n <- nodes g''', isinkdom''' ! n == Nothing]
  where ms = Set.toList msS
        g'''   = foldr (flip delSuccessorEdges) g'' ms
          where  toMs   = rdfs ms g
                 g' = subgraph toMs g
                 fromMs =  dfs ms g'
                 g'' = subgraph fromMs g'

        isinkdom''' = fmap fromSet $ isinkdomOfTwoFinger8 g'''
