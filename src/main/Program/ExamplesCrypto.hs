{-# LANGUAGE TemplateHaskell #-}
module Program.ExamplesCrypto where


import Program
import Program.For
import Program.Defaults
import Program.Generator (Generated(..), GeneratedProgram(..), IntraGeneratedProgram(..), toProgram, toProgramIntra)

import IRLSOD

import Unicode

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Util

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode


import Control.Exception.Base (assert)

example42 :: Program Gr
example42 = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main")])
    (Map.fromList [("main", Generated (
                      Ass (Global "a") (Val 1)
               `Seq`  Ass (Global "b") (Val 2)
               `Seq`  Ass (Global "c") (Val 3)
               `Seq`  Ass (Global "d") (Val 4)
               `Seq`  Ass (Global "x") (Val 24)
               `Seq`  If ((Var (Global "x")) `Leq` (Val 0))
                          (Ass (Global "y") ((Var (Global "b")) `Plus` (Var (Global "c"))))
                       {-else-}
                          (Ass (Global "y") ((Var (Global "d")) `Plus` (Var (Global "d"))))
               `Seq`  Ass (Register 1) (Var (Global "b"))
               `Seq`  Ass (Register 2) (Var (Global "y"))
               `Seq`  If ((Var (Register 2)) `Leq` (Val 3))
                          (Ass (Register 3) (Var (Global "a")))
                       {-else-}
                          (Ass (Register 3) (Var (Global "b")))
               `Seq`  Ass (Register 4) (Var (Global "c"))
                     ) undefined undefined undefined)])


exampleMerge :: Program Gr
exampleMerge = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main")])
    (Map.fromList [("main", Generated (
                      Skip
               `Seq`  Skip
               `Seq`  Ass (Register 0) (Var (Global "d"))
               `Seq`  Ass (Register 1) (Var (Global "e"))
               `Seq`  Ass (Global "d") (Var (Register 0) `Plus` (Var (Register 1)))
               `Seq`  Ass (Register 0) (Var (Global "c"))
               `Seq`  If ((Val 0) `Leq` (Var (Register 0))) (
                          Ass (Register 0) (Var (Global "z"))
               `Seq`      Ass (Global "d") (Neg $ (Var (Register 0)))
                      ) {-else-} (
                          Skip
                      )
               `Seq`  Ass (Register 0) (Var (Global "z"))
               `Seq`  Ass (Register 1) (Var (Global "a"))
               `Seq`  If ((Val 0) `Leq` ((Var (Register 0)) `Times` (Var (Register 1)))) (
                          Skip
                      ) {-else-} (
                          Ass (Register 0) (Var (Global "a"))
               `Seq`      Ass (Register 1) (Var (Global "x"))
               `Seq`      Ass (Global "a") ((Var (Register 0)) `Plus` (Var (Register 1)))
                      )
               `Seq` Skip
               `Seq` Ass (Register 0) (Var (Global "x"))
               `Seq` Ass (Global "d") (Neg $ (Var (Register 0)))
                     ) undefined undefined undefined)])


simpleArray :: Program Gr
simpleArray = toProgramIntra $ IntraGeneratedProgram
    (Map.fromList [(1,"main")])
    (Map.fromList [("main", Generated (
                      AssArr (Array "a") (Val a) (Val 1)
               `Seq`  AssArr (Array "a") (Val b) (Val 2)
               `Seq`  AssArr (Array "a") (Val c) (Val 3)
               `Seq`  AssArr (Array "a") (Val d) (Val 4)
               `Seq`  AssArr (Array "a") (Val x) (Val 24)
               `Seq`  If ((ArrayRead (Array "a") (Val x)) `Leq` (Val 0))
                          (Ass (Global "y") ((ArrayRead (Array "a") (Val b)) `Plus` (ArrayRead (Array "a") (Val c))))
                       {-else-}
                          (Ass (Global "y") ((ArrayRead (Array "a") (Val d)) `Plus` (ArrayRead (Array "a") (Val d))))
               `Seq`  Ass (Register 1) (ArrayRead (Array "a") (Val b))
               `Seq`  Ass (Register 2) (Var (Global "y"))
               `Seq`  If ((Var (Register 2)) `Leq` (Val 3))
                          (Ass (Register 3) (ArrayRead (Array "a") (Val a)))
                       {-else-}
                          (Ass (Register 3) (ArrayRead (Array "a") (Val b)))
               `Seq`  Ass (Register 4) (ArrayRead (Array "a") (Val c))
                     ) undefined undefined undefined)])
  where a = 0
        b = 32
        c = 64
        d = 255
        x = 128


subBytesIteratorIndex   = Global "subBytesIteratorIndex"
addRoundIteratorIndex   = Global "addRoundIteratorIndex"

mixColumnsS = [ Global $ "mixColumnsS" ++ (show i) | i <- [0 .. 3] ]
mixColumnsT = [ Global $ "mixColumnsT" ++ (show i) | i <- [0 .. 3] ]

expandKeyT = [ Global $ "expandKeyT" ++ (show i) | i <- [0 .. 3] ]


shiftRowsTmp          = Global "shiftRowsTmp"


allVars = assert (length vars == (Set.size $ Set.fromList vars)) vars
  where vars = [subBytesIteratorIndex, addRoundIteratorIndex] ++ mixColumnsS ++ mixColumnsT


addRound :: Array -> Array -> For
addRound roundkey state = 
                       Ass i (Val 0)
                 `Seq` ForC 16 (
                                 AssArr state (Var i) (ArrayRead state (Var i) `Xor` (ArrayRead roundkey (Var i)))
                           `Seq` Ass i (Var i `Plus` (Val 1))
                       )
  where i = addRoundIteratorIndex

subBytes :: Array -> Array -> For
subBytes sbox state =
                       Ass i (Val 0)
                 `Seq` ForC 16 (
                                 AssArr state (Var i) (ArrayRead sbox (ArrayRead state (Var i)))
                           `Seq` Ass i (Var i `Plus` (Val 1))
                       )
  where i = subBytesIteratorIndex

shiftRows :: Array -> For
shiftRows state =
                       Ass tmp (ArrayRead state (Val 5))
                `Seq`  AssArr state (Val  1) (ArrayRead state (Val  5))
                `Seq`  AssArr state (Val  5) (ArrayRead state (Val  9))
                `Seq`  AssArr state (Val  9) (ArrayRead state (Val 13))
                `Seq`  AssArr state (Val 13) (Var tmp)

                `Seq`  Ass tmp (ArrayRead state (Val 2))
                `Seq`  AssArr state (Val  2) (ArrayRead state (Val 10))
                `Seq`  AssArr state (Val 10) (Var tmp)
                `Seq`  Ass tmp (ArrayRead state (Val 6))
                `Seq`  AssArr state (Val  6) (ArrayRead state (Val 14))
                `Seq`  AssArr state (Val 14) (Var tmp)

                `Seq`  Ass tmp (ArrayRead state (Val 15))
                `Seq`  AssArr state (Val 15) (ArrayRead state (Val 11))
                `Seq`  AssArr state (Val 11) (ArrayRead state (Val  7))
                `Seq`  AssArr state (Val  7) (ArrayRead state (Val  3))
                `Seq`  AssArr state (Val  3) (Var tmp)
  where tmp = shiftRowsTmp




mixColumns :: Array -> For
mixColumns state = 
                       for  0
                 `Seq` for  4
                 `Seq` for  8
                 `Seq` for 12
  where s0 = mixColumnsS !! 0
        s1 = mixColumnsS !! 1
        s2 = mixColumnsS !! 2
        s3 = mixColumnsS !! 3

        t0 = mixColumnsT !! 0
        t1 = mixColumnsT !! 1
        t2 = mixColumnsT !! 2
        t3 = mixColumnsT !! 3

        for i = 
                       Ass s0 (ArrayRead state (Val $ i + 0))
                 `Seq` Ass s1 (ArrayRead state (Val $ i + 1))
                 `Seq` Ass s2 (ArrayRead state (Val $ i + 1))
                 `Seq` Ass s3 (ArrayRead state (Val $ i + 1))

                 `Seq` Ass t0 (  (Var s0 `Shl` (Val 1)) `Xor` (Var s1) `Xor` (Var s1 `Shl` (Val 1)) `Xor` (Var s2) `Xor` (Var s3)   )
                 `Seq` Ass t1 (  (Var s0) `Xor` (Var s1 `Shl` (Val 1)) `Xor` (Var s2) `Xor` (Var s2 `Shl` (Val 1)) `Xor` (Var s3)   )
                 `Seq` Ass t2 (  (Var s0) `Xor` (Var s1) `Xor` (Var s2 `Shl` (Val 1)) `Xor` (Var s3) `Xor` (Var s3 `Shl` (Val 1))   )
                 `Seq` Ass t3 (  (Var s0) `Xor` (Var s0 `Shl` (Val 1)) `Xor` (Var s1) `Xor` (Var s2) `Xor` (Var s3 `Shl` (Val 1))   )

                 `Seq` AssArr state (Val $ i + 0) (Var t0 `Xor` ((Neg (Var t0 `Shr` (Val 8))) `BAnd` (Val 0x11b))) -- TODO: overflow/shr/wordsize
                 `Seq` AssArr state (Val $ i + 1) (Var t1 `Xor` ((Neg (Var t1 `Shr` (Val 8))) `BAnd` (Val 0x11b)))
                 `Seq` AssArr state (Val $ i + 2) (Var t2 `Xor` ((Neg (Var t2 `Shr` (Val 8))) `BAnd` (Val 0x11b)))
                 `Seq` AssArr state (Val $ i + 3) (Var t3 `Xor` ((Neg (Var t3 `Shr` (Val 8))) `BAnd` (Val 0x11b)))


expandKey :: Array -> For
expandKey keySchedule =
                       Ass i (Val 0)
                 `Seq` ForC 240 (
                                 AssArr state (Var i) (ArrayRead state (Var i) `Xor` (ArrayRead roundkey (Var i)))
                           `Seq` Ass i (Var i `Plus` (Val 1))
                       )

  where for size =
                       Ass t0 (ArrayRead keySchedule (Val 0 + size - 4)
                 `Seq` Ass t1 (ArrayRead keySchedule (Val 1 + size - 4)
                 `Seq` Ass t2 (ArrayRead keySchedule (Val 2 + size - 4)
                 `Seq` Ass t3 (ArrayRead keySchedule (Val 3 + size - 4)
          
      while (size < schedule_size) {
        for (uint8_t i = 0; i < 4; i++) {
            t[i] = in[i + size - 4];
        }

        if ((size % (keysize / 8)) == 0) {
            schedule_core(t, n);
            n++;
        }

        /* 256 bit keys get an extra S-Box operation */
        if (keysize == 256 && size % (keysize / 8) == 16) {
            for (uint8_t i = 0; i < 4; i++) {
                t[i] = SBOX[t[i]];
            }
        }

        for (uint8_t i = 0; i < 4; i++) {
            in[size] = in[size - (keysize / 8)] ^ t[i];
            size++;
        }
    }







cryptoTestSuit = [
                $(withName 'simpleArray)
            ]
