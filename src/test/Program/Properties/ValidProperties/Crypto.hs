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

import Data.Graph.Inductive.PatriciaTree (Gr)

import Unicode
import Util( moreSeeds)

import IRLSOD(GlobalState(..), arrayEmpty)

import Program(Program(..))
import Program.Properties.Util

import Program.For (compileAllToProgram, For(..), twoAddressCode)

import CacheExecution(initialCacheState, CacheSize, cacheExecution)

import qualified ReferenceCrypto (runAES256)

import Program.ExamplesCrypto(for2Program, br_aes_small_cbcenc_main, br_aes_small_cbcenc_main_ct, br_aes_small_cbcenc_main_ct_precache)
import qualified Program.ExamplesCrypto (runAES256, runAES256_ct, runAES256_ct_precache, state, key)




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
                       == Program.ExamplesCrypto.runAES256  key msg,
    testProperty "aes256             execution times  4" $ isConstant br_aes_small_cbcenc_main             "main"              4 (Nothing),
    testProperty "aes256             execution times 16" $ isConstant br_aes_small_cbcenc_main             "main"             16 (Nothing),
    testProperty "aes256             execution times 30" $ isConstant br_aes_small_cbcenc_main             "main"             30 (Just 31378),
    testProperty "aes256             execution times 32" $ isConstant br_aes_small_cbcenc_main             "main"             32 (Just 31378),
    testProperty "aes256             execution times 99" $ isConstant br_aes_small_cbcenc_main             "main"             99 (Just 31378),
    testProperty "aes256_ct          execution times  4" $ isConstant br_aes_small_cbcenc_main_ct          "main_ct"           4 (Just 194245),
    testProperty "aes256_ct          execution times 16" $ isConstant br_aes_small_cbcenc_main_ct          "main_ct"          16 (Just 127757),
    testProperty "aes256_ct_precache execution times  4" $ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache"  4 (Nothing),
    testProperty "aes256_ct_precache execution times  6" $ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache"  6 (Nothing),
    testProperty "aes256_ct_precache execution times  8" $ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache"  8 (Just  46578),
    testProperty "aes256_ct_precache execution times 10" $ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache" 10 (Just  43762),
    testProperty "aes256_ct_precache execution times 16" $ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache" 16 (Just  36770),
    testProperty "print aes256_ execution times" $ \seed1 seed2 -> ( True ∨ (
         isConstant br_aes_small_cbcenc_main "main"  2 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main "main"  4 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main "main"  6 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main "main"  8 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main "main" 10 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main "main" 12 Nothing seed1 seed2
       
       ∧ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache"  2 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache"  4 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache"  6 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache"  8 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache" 10 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct_precache "main_ct_precache" 12 Nothing seed1 seed2
       
       ∧ isConstant br_aes_small_cbcenc_main_ct "main_ct"  2 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct "main_ct"  4 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct "main_ct"  6 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct "main_ct"  8 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct "main_ct" 10 Nothing seed1 seed2
       ∧ isConstant br_aes_small_cbcenc_main_ct "main_ct" 12 Nothing seed1 seed2
     ))
 ]


isConstant main name cacheSize expected = \seed1 seed2 ->
                    let key = moreSeeds seed1 32 :: [Word8]
                        msg = moreSeeds seed2 16 :: [Word8]
                        initialFullState = ((global, Map.empty, ()), initialCacheState, 0)
                          where global = GlobalState { σv = Map.empty, σa = Map.fromList [
                                  (Program.ExamplesCrypto.state,  (Map.fromList $ zip [0..15] msg)  `Map.union` arrayEmpty),
                                  (Program.ExamplesCrypto.key,    (Map.fromList $ zip [0..31] key)  `Map.union` arrayEmpty)] }
                        [execution] = cacheExecution cacheSize graph initialFullState n0
                        pr = for2Program $ twoAddressCode $ main Skip Skip :: Program Gr
                        graph = tcfg pr
                        n0 = entryOf pr $ procedureOf pr $ mainThread pr
                        (nx, time) = List.last execution
                        print = traceShow (show cacheSize ++ "," ++ name ++ "," ++ show time)
                    in case expected of
                        Nothing -> print $ True
                        Just ex -> print $ time == ex
