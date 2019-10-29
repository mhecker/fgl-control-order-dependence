{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Abstract where

import Debug.Trace (traceShow, trace)
import Control.Exception.Base (assert)

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map, (!))

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Runners.AntXML


import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, lsuc, Node, labNodes, labEdges, )
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Arbitrary

import Unicode
import Program.Properties.Util
import Util(sampleFrom, invert'', moreSeeds)
import qualified Data.Graph.Inductive.Query.Slices.NTICD as SLICE.NTICD (wodTEILSliceViaNticd)
import qualified Data.Graph.Inductive.Query.PostDominance.Abstract as Abstract

abstract     = defaultMain                               $ testGroup "abstract"    [ mkTest [abstractTests], mkProp [abstractProps]]
abstractX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "abstract"    [ mkTest [abstractTests], mkProp [abstractProps]]


abstractProps = testGroup "(concerning abstract postdominance)" [
    testPropertySized 50 "abstract postdominance slices are sound"
      $ \(ARBITRARY(generatedGraph)) seed seed1 seed2 ->
          let g = generatedGraph
              n = length $ nodes g
              ms
                  | n == 0 = Set.empty
                  | n /= 0 = Set.fromList [ nodes g !! (s `mod` n) | s <- moreSeeds seed2 (seed1 `mod` n)]

              available = Set.toList $ (Set.fromList (nodes g) ∖ ms)
              takes = [ t `mod` (1 + n' `div` 4) + 1 | t <- moreSeeds seed n' ]
                where n' = length available
              abstractionM =  Map.fromList [ (n, ns) | ns <- go takes available, n <- Set.toList ns ]
                           ⊔  Map.fromList [ (m, Set.fromList [m]) | m <- Set.toList ms ]
                where go _      [] = []
                      go (t:ts) ns = (Set.fromList $ take t ns) : go ts (drop t ns)

              msAbstract = Set.fromList [ Set.fromList [ m ] | m <- Set.toList ms ]

              slicePerfect  = SLICE.NTICD.wodTEILSliceViaNticd g ms
              
              sliceAbs = Abstract.abstractSlice g abstractionM msAbstract
              sliceAbsPerfect = Set.fromList [ abstractionM ! n | n <- Set.toList slicePerfect]

              slice = (∐) [ ns | ns <- Set.toList sliceAbs ]
              ok = assert (ok1 == ok2) $ ok1 ∧ ok2
                where ok1 = slicePerfect    ⊆ slice
                      ok2 = sliceAbsPerfect ⊆ sliceAbs
          in (if Set.null ms then id else traceShow (Set.size ms, Set.size sliceAbs, Set.size sliceAbsPerfect)) $
             if ok then ok else traceShow g $ traceShow abstractionM $ traceShow ms $ traceShow msAbstract $ traceShow (slicePerfect, slice) $ ok
  ]

abstractTests = testGroup "(concerning abstract postdominance)" []
