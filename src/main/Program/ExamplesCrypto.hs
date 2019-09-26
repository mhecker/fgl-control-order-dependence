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

import Data.Bits

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode


import Control.Exception.Base (assert)


for2Program :: For -> Program Gr
for2Program for = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram (Map.fromList [ (1, "1") ]) (Map.fromList [("1", for) ])


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



sbox                    = Array  "sbox"
sboxConst = [
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B,
    0xFE, 0xD7, 0xAB, 0x76, 0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0,
    0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0, 0xB7, 0xFD, 0x93, 0x26,
    0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2,
    0xEB, 0x27, 0xB2, 0x75, 0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0,
    0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84, 0x53, 0xD1, 0x00, 0xED,
    0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F,
    0x50, 0x3C, 0x9F, 0xA8, 0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5,
    0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2, 0xCD, 0x0C, 0x13, 0xEC,
    0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14,
    0xDE, 0x5E, 0x0B, 0xDB, 0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C,
    0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79, 0xE7, 0xC8, 0x37, 0x6D,
    0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F,
    0x4B, 0xBD, 0x8B, 0x8A, 0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E,
    0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E, 0xE1, 0xF8, 0x98, 0x11,
    0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F,
    0xB0, 0x54, 0xBB, 0x16
 ]

rcon                    = Array "rcon"
rconConst = [
    0x01, 0x02, 0x04, 0x08, 0x10, 0x20,
    0x40, 0x80, 0x1B, 0x36
 ]




subBytesIteratorIndex   = Global "subBytesIteratorIndex"
addRoundIteratorIndex   = Global "addRoundIteratorIndex"
cbcEncRunIndex          = Global "cbcEncRunIndex"
encryptIndex            = Global "encryptIndex"
encryptIndexU           = Global "encryptIndexU"
encryptState            = Array  "encryptState"

aesKeySchedI            = Global "aesKeySchedI"
aesKeySchedJ            = Global "aesKeySchedJ"
aesKeySchedK            = Global "aesKeySchedK"
aesKeySchedNK           = Global "aesKeySchedNK"
aesKeySchedNKF          = Global "aesKeySchedNKF"


mainSkey                = Array  "skey"
mainKey                 = Array  "key"
mainBuf                 = Array  "buf"


mixColumnsS = [ Global $ "mixColumnsS" ++ (show i) | i <- [0 .. 3] ]
mixColumnsT = [ Global $ "mixColumnsT" ++ (show i) | i <- [0 .. 3] ]

expandKeyT = [ Global $ "expandKeyT" ++ (show i) | i <- [0 .. 3] ]
expandKeyIndex          = Global "expandKeyIndex"
expandKeyN            = Global "expandKeyN"

shiftRowsTmp          = Global "shiftRowsTmp"

rotateTmp             = Global "rotateTmp"


allNames = assert (length vars == (Set.size $ Set.fromList vars))
         $ assert (length arrs == (Set.size $ Set.fromList arrs))
  where vars =   [subBytesIteratorIndex, addRoundIteratorIndex, shiftRowsTmp, cbcEncRunIndex, encryptIndex, encryptIndexU, expandKeyN] ++ mixColumnsS ++ mixColumnsT ++ expandKeyT
             ++  [aesKeySchedI, aesKeySchedJ, aesKeySchedK, aesKeySchedNK, aesKeySchedNKF]
        arrs = [mainSkey, mainKey, mainBuf]

br_aes_S :: For
br_aes_S = assert (length sboxConst == 256) $ 
  foldr Seq Skip [ AssArr sbox (Val i) (Val sval) | (i,sval) <- zip [0..255] sboxConst]


simpleRcon :: For
simpleRcon = assert (length sboxConst == 10) $ 
  foldr Seq Skip [ AssArr rcon (Val i) (Val rcval) | (i,rcval) <- zip [0..9] rconConst]





addRound :: Array -> Array -> VarFunction -> For
addRound state skey offset = 
                       Ass i (Val 0)
                 `Seq` ForC 16 (
                                 AssArr state (Var i) (ArrayRead state (Var i) `Xor` (ArrayRead skey (Var i `Plus` offset)))
                           `Seq` Ass i (Var i `Plus` (Val 1))
                       )
  where i = addRoundIteratorIndex

sub_bytes :: Array -> For
sub_bytes state =
                       Ass i (Val 0)
                 `Seq` ForC 16 (
                                 AssArr state (Var i) (ArrayRead sbox (ArrayRead state (Var i)))
                           `Seq` Ass i (Var i `Plus` (Val 1))
                       )
  where i = subBytesIteratorIndex


shift_rows :: Array -> For
shift_rows state =
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


scheduleSize256 = 240
keySize = 256
num_rounds = 14
key_len = 32 -- 32 * 8 == 256


scheduleCore :: Var -> Var -> Var -> Var -> Var -> For
scheduleCore t0 t1 t2 t3 n =
                       rotate
                 `Seq` Ass t0 (ArrayRead sbox (Var t0))
                 `Seq` Ass t1 (ArrayRead sbox (Var t1))
                 `Seq` Ass t2 (ArrayRead sbox (Var t2))
                 `Seq` Ass t3 (ArrayRead sbox (Var t3))
                 `Seq` Ass t0 (Var t0 `Xor` (ArrayRead rcon (Var n)))
  where rotate =
                       Ass tmp (Var t0)
                 `Seq` Ass t0  (Var t1)
                 `Seq` Ass t1  (Var t2)
                 `Seq` Ass t2  (Var t3)
                 `Seq` Ass t3  (Var tmp)
          where tmp = rotateTmp


expandKey :: Array -> Array -> For
expandKey skey key =
                       Ass n (Val 1)
                 `Seq` Ass i (Val 0)
                 `Seq` ForC 32 (
                                 AssArr skey (Var i) (ArrayRead key (Var i))
                           `Seq` Ass i (Var i `Plus` (Val 1))
                       )
                 `Seq` foldr Seq Skip [ for size | size <- [keySize `div` 8 .. scheduleSize256 - 1] ]
  where for size =
                       Ass t0 (ArrayRead skey (Val $ 0 + size - 4))
                 `Seq` Ass t1 (ArrayRead skey (Val $ 1 + size - 4))
                 `Seq` Ass t2 (ArrayRead skey (Val $ 2 + size - 4))
                 `Seq` Ass t3 (ArrayRead skey (Val $ 3 + size - 4))

                 `Seq` If ( (Val $ size `mod` (keySize `div` 8)) `eeq` (Val 0)) (
                           scheduleCore t0 t1 t2 t3 n
                 `Seq`     Ass n (Var n `Plus` (Val 1))
                       ) {- else -} (
                           Skip
                       )
                 `Seq` If ((Val keySize `eeq` (Val 256)) `And` ((Val $ size `mod` (keySize `div` 8)) `eeq` (Val 16))) (
                           Ass t0 (ArrayRead sbox (Var t0))
                 `Seq`     Ass t1 (ArrayRead sbox (Var t1))
                 `Seq`     Ass t2 (ArrayRead sbox (Var t2))
                 `Seq`     Ass t3 (ArrayRead sbox (Var t3))
                       ) {- else -} (
                           Skip
                       )
                 `Seq` AssArr skey (Val $ size + 0) (ArrayRead skey ((Val $ size - (keySize `div` 8)) `Xor` (Var t0)))
                 `Seq` AssArr skey (Val $ size + 1) (ArrayRead skey ((Val $ size - (keySize `div` 8)) `Xor` (Var t1)))
                 `Seq` AssArr skey (Val $ size + 2) (ArrayRead skey ((Val $ size - (keySize `div` 8)) `Xor` (Var t2)))
                 `Seq` AssArr skey (Val $ size + 3) (ArrayRead skey ((Val $ size - (keySize `div` 8)) `Xor` (Var t3)))

        i = expandKeyIndex 
        t0 = expandKeyT !! 0
        t1 = expandKeyT !! 1
        t2 = expandKeyT !! 2
        t3 = expandKeyT !! 3
        n = expandKeyN
 


br_aes_small_cbcenc_run :: Array -> Array -> Array -> For
br_aes_small_cbcenc_run skey buf iv =
                        Ass i (Val 0)
                 `Seq` ForC 16 (
                                 AssArr buf (Var i) (  (ArrayRead buf (Var i)) `Xor` (ArrayRead iv (Var i)))
                           `Seq` Ass i (Var i `Plus` (Val 1))
                       )
                 `Seq` (br_aes_small_encrypt skey buf)
  where i = cbcEncRunIndex 

br_aes_small_encrypt :: Array -> Array -> For
br_aes_small_encrypt skey buf =
                       Ass i (Val 0)
                 `Seq` ForC 16 (
                                 AssArr state (Var i) (ArrayRead buf (Var i))
                 `Seq`           Ass i (Var i `Plus` (Val 1))
                       )
                 `Seq` addRound buf skey (Val 0)
                 `Seq` Ass u (Val 1)
                 `Seq` ForC (num_rounds - 1) (
                                 sub_bytes state
                 `Seq`           shift_rows state
                 `Seq`           addRound state skey (Var u `Shl` (Val 2))
                 `Seq`           Ass u (Var u `Plus` (Val 1))
                       )
                 `Seq` sub_bytes state
                 `Seq` shift_rows state
                 `Seq` addRound state skey (Val num_rounds `Shl` (Val 2))
                 `Seq` Ass i (Val 0)
                 `Seq` ForC 16 (
                                 AssArr buf (Var i) (ArrayRead state (Var i))
                 `Seq`           Ass i (Var i `Plus` (Val 1))
                       )
  where i = encryptIndex
        u = encryptIndexU
        state = encryptState


{-
br_aes_keysched :: Array -> Array -> For
br_aes_keysched skey key =
                       Ass nk  (Val key_len `Shr` (Val 2))
                 `Seq` Ass nkf (Val (num_rounds + 1) `Shl` (Val 2))
                 `Seq` Ass i (Val 0)
                 `Seq` ForC key_len (
                                 AssArr skey (Var i) (ArrayRead key (Var i))
                 `Seq`           Ass i (Var i `Plus` (Val 1))
                       )


  where i   = aesKeySchedI
        j   = aesKeySchedJ
        k   = aesKeySchedK
        nk  = aesKeySchedNK
        nkf = aesKeySchedNKF
-}
{-
unsigned
br_aes_keysched(uint32_t *skey, const void *key, size_t key_len)
{
	unsigned num_rounds;
	int i, j, k, nk, nkf;

	nk = (int)(key_len >> 2);
	nkf = (int)((num_rounds + 1) << 2);
	for (i = 0; i < nk; i ++) {
		skey[i] = br_dec32be((const unsigned char *)key + (i << 2));
	}
	for (i = nk, j = 0, k = 0; i < nkf; i ++) {
		uint32_t tmp;

		tmp = skey[i - 1];
		if (j == 0) {
			tmp = (tmp << 8) | (tmp >> 24);
			tmp = SubWord(tmp) ^ Rcon[k];
		} else if (nk > 6 && j == 4) {
			tmp = SubWord(tmp);
		}
		skey[i] = skey[i - nk] ^ tmp;
		if (++ j == nk) {
			j = 0;
			k ++;
		}
	}
	return num_rounds;
}br_aes_keysched skey key = undefined
-}












br_aes_small_cbcenc_init :: Array -> Array -> For
br_aes_small_cbcenc_init skey key =
                       -- br_aes_keysched skey key
                       expandKey skey key

br_aes_small_cbcenc_main :: For
br_aes_small_cbcenc_main =
                       br_aes_S
                 `Seq` br_aes_small_cbcenc_init skey key
                 `Seq` br_aes_small_encrypt skey buf

  where key = mainKey
        skey = mainSkey
        buf = mainBuf


cryptoTestSuit = [
                $(withName 'simpleArray)
            ]
