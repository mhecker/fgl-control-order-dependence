{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Misc where


import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Runners.AntXML

import Program.Properties.Util

import Data.Graph.Inductive.Arbitrary

import Data.Graph.Inductive.Util (trcOfTrrIsTrc)

misc       = defaultMain                               $ testGroup "misc"      [ mkProp [miscProps] ]
miscX      = defaultMainWithIngredients [antXMLRunner] $ testGroup "misc"      [ mkProp [miscProps] ]

miscProps = testGroup "(misc)" [
    testProperty  "trcOfTrrIsTrc"                     $ trcOfTrrIsTrc
  ]
