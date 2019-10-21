{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "Util.cpp"

module Program.Properties.ValidProperties where

import Program.Properties.ValidProperties.Balanced
import Program.Properties.ValidProperties.Cache
import Program.Properties.ValidProperties.Cdom
import Program.Properties.ValidProperties.Color
import Program.Properties.ValidProperties.Crypto
import Program.Properties.ValidProperties.Delay
import Program.Properties.ValidProperties.Dod
import Program.Properties.ValidProperties.Giffhorn
import Program.Properties.ValidProperties.Indeps
import Program.Properties.ValidProperties.Insensitivedom
import Program.Properties.ValidProperties.Long
import Program.Properties.ValidProperties.Misc
import Program.Properties.ValidProperties.Newcd
import Program.Properties.ValidProperties.Nticd
import Program.Properties.ValidProperties.Ntscd
import Program.Properties.ValidProperties.Preccex
import Program.Properties.ValidProperties.Reducible
import Program.Properties.ValidProperties.Sensitivedom
import Program.Properties.ValidProperties.Simon
import Program.Properties.ValidProperties.Soundness
import Program.Properties.ValidProperties.Timingdep
import Program.Properties.ValidProperties.Timing
import Program.Properties.ValidProperties.Wod


import Prelude hiding (all)

import Program.Properties.Util

import Test.Tasty
import Test.Tasty.Providers (singleTest)
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)

import Test.Tasty.Runners.AntXML
import Test.Tasty.Ingredients.Basic

import Test.QuickCheck (Testable, property)
import Test.QuickCheck.Property (Property(..))



main      = all

all        = defaultMain                               $ tests
allX       = defaultMainWithIngredients [antXMLRunner] $ tests

tests :: TestTree
tests = testGroup "Tests" [unitTests, properties]


properties :: TestTree
properties = testGroup "Properties" [ timingClassificationDomPathsProps, giffhornProps, cdomProps, cdomCdomProps, balancedParanthesesProps, soundnessProps                              , nticdProps, ntscdProps, insensitiveDomProps, sensitiveDomProps, timingDepProps, dodProps, wodProps, colorProps, reducibleProps, indepsProps, simonClassificationProps, newcdProps, delayProps, cryptoProps]
  where missing = [longProps]
unitTests :: TestTree
unitTests  = testGroup "Unit tests" [ timingClassificationDomPathsTests, giffhornTests, cdomTests, cdomCdomTests, balancedParanthesesTests, soundnessTests, precisionCounterExampleTests, nticdTests, ntscdTests, insensitiveDomTests, sensitiveDomTests, timingDepTests, dodTests, wodTests, colorTests                , indepsTests, simonClassificationTests, newcdTests, delayTests]
  where missing = [longTests]
