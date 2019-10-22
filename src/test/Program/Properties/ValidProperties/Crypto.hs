{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#include "../Util.cpp"

module Program.Properties.ValidProperties.Crypto where

import Debug.Trace (traceShow, trace)
import Control.Exception.Base (assert)
import Control.Monad.Random (randomR, getStdRandom)

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map, (!))
import Data.Word

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Runners.AntXML

import Unicode
import Util( moreSeeds)

import Program.Properties.Util


import qualified ReferenceCrypto (runAES256)
import qualified Program.ExamplesCrypto (runAES256, runAES256_ct, runAES256_ct_precache)

crypto     = defaultMain                               $ testGroup "crypto"    [                      mkProp [cryptoProps]]
cryptoX    = defaultMainWithIngredients [antXMLRunner] $ testGroup "crypto"    [                      mkProp [cryptoProps]]


cryptoProps = testGroup "(concerning crypto example)" [
    testProperty "aes256_ct example is correct"
                $ \seed1 seed2 ->
                    let key = moreSeeds seed1 32 :: [Word8]
                        msg = moreSeeds seed2 16 :: [Word8]
                    in    ReferenceCrypto.runAES256            key msg
                       == Program.ExamplesCrypto.runAES256_ct  key msg,
    testProperty "aes256_ct_precache example is correct"
                $ \seed1 seed2 ->
                    let key = moreSeeds seed1 32 :: [Word8]
                        msg = moreSeeds seed2 16 :: [Word8]
                    in    ReferenceCrypto.runAES256            key msg
                       == Program.ExamplesCrypto.runAES256_ct_precache
                                                               key msg,
    testProperty "aes256 example is correct"
                $ \seed1 seed2 ->
                    let key = moreSeeds seed1 32 :: [Word8]
                        msg = moreSeeds seed2 16 :: [Word8]
                    in    ReferenceCrypto.runAES256         key msg
                       == Program.ExamplesCrypto.runAES256  key msg
 ]
