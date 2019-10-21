{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Reducible where


import Debug.Trace (traceShow, trace)
import Control.Exception.Base (assert)
import Control.Monad.Random (randomR, getStdRandom)

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map, (!))


import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Runners.AntXML

import Data.Graph.Inductive (mkGraph, nodes, edges, pre, suc, lsuc, emap, nmap, Node, labNodes, labEdges, grev, efilter, subgraph, delEdges, insEdge, newNodes)
import Data.Graph.Inductive.PatriciaTree (Gr)

import Program.Properties.Util
import Data.Graph.Inductive.Arbitrary.Reducible

reducible  = defaultMain                               $ testGroup "reducible" [                      mkProp [reducibleProps]]
reducibleX = defaultMainWithIngredients [antXMLRunner] $ testGroup "reducible" [                      mkProp [reducibleProps]]

reducibleProps = testGroup "(concerning the generator for reducible graphs)" [
    testProperty  "every generated reducible graph is reducible"
                $ \(REDUCIBLE(g)) -> isReducible g
   ]
