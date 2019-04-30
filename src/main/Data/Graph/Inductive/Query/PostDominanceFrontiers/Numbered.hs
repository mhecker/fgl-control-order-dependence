{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert
module Data.Graph.Inductive.Query.PostDominanceFrontiers.Numbered where


import Control.Exception.Base (assert)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive


import Data.Graph.Inductive.Util (controlSinks)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (idomToDFFastForRoots)



isinkDFNumberedForSinks :: forall gr a b. DynGraph gr => [[Node]] -> gr a b ->  Map Node (Set Node)
isinkDFNumberedForSinks sinks graph =
    require (Set.fromList sinks == Set.fromList (controlSinks graph)) $
    idomToDFFastForRoots roots graph idom
  where idom = Map.fromList $ iPDomForSinks sinks graph
        roots = go (Map.assocs idom) [ sink | sink@(_:_:_) <- sinks ]
          where go []     roots = roots
                go ((n, m):as) roots = case m of 
                  Nothing -> go as ([n]:roots)
                  _       -> go as      roots

isinkDFNumbered :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkDFNumbered graph = isinkDFNumberedForSinks sinks graph
  where sinks = controlSinks graph


nticdSliceNumbered :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdSliceNumbered graph =  combinedBackwardSlice graph nticd w
  where nticd = isinkDFNumbered graph
        w     = Map.empty
