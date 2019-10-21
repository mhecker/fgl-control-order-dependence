module Program.Properties.Util where

import Control.Monad.Random (randomR, getStdRandom)

import System.IO.Unsafe(unsafePerformIO)
import Control.Monad.Random(evalRandIO)
import Control.Exception.Base (assert)

import Test.Tasty
import Test.Tasty.Providers (singleTest)
import Test.Tasty.QuickCheck

import Test.Tasty.Ingredients.Basic

import Test.QuickCheck (Testable, property)
import Test.QuickCheck.Property (Property(..))



testPropertySized :: Testable a => Int -> TestName -> a -> TestTree
testPropertySized n name prop = singleTest name $ QC $ (MkProperty $ scale (min n) gen)
   where MkProperty gen = property prop


mkTest = testGroup "Unit tests"
mkProp = testGroup "Properties"
