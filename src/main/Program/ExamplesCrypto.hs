{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
#define require assert
module Program.ExamplesCrypto where


import Program
import Program.For
import Program.Defaults
import Program.Generator (Generated(..), GeneratedProgram(..), IntraGeneratedProgram(..), toProgram, toProgramIntra)

import IRLSOD
import Execution(allFinishedExecutionTraces)

import Unicode

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Util

import Data.Word
import Data.Bits

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode


import Control.Exception.Base (assert)

unrolledFor unrolls n command =
    require (n >         0)
  $ require (n >=  unrolls)
  $ if (unrolls == n) then
      foldr1 Seq                              commands
     else
      foldr  Seq (ForC (n - unrolls) command) commands
  where commands = take (fromIntegral unrolls) $ repeat command

for  = unrolledFor 1

unrolledForFromToStepUsing unrolls from to step ix command = 
    require (from <= to)
  $ require (n >         0)
  $ require (n >=  unrolls)
  $ if (unrolls == n) then
      foldr1 Seq commands
     else
      foldr1 Seq commands `Seq` ForFromToStepUsing first to step ix command
  where n = ((to - from) `div` step) + 1
        first = from + (unrolls * step)
        commands = [ command' i | i <- take (fromIntegral unrolls) $ [from, from+step .. ] ]
          where command' i = Ass ix (Val i) `Seq` (vfMapF constFold $ vfMapF (subst i) $ command)

                subst i v@(Var x)
                  | x == ix   = Val i
                  | otherwise = v
                subst i (Plus  a b) = Plus  (subst i a) (subst i b)
                subst i (Minus a b) = Minus (subst i a) (subst i b)
                subst i (Mod   a b) = Mod   (subst i a) (subst i b)
                subst i (Xor   a b) = Xor   (subst i a) (subst i b)
                subst i (ArrayRead a ix) = ArrayRead a (subst i ix)
                subst i vf = vf -- TODO: more cases

                constFold (a `Plus` b) =
                  let a' = constFold a
                      b' = constFold b
                  in folded a' b' (+) Plus
                constFold (a `Minus` b) =
                  let a' = constFold a
                      b' = constFold b
                  in folded a' b' (-) Minus
                constFold (a `Mod` b) =
                  let a' = constFold a
                      b' = constFold b
                  in folded a' b' mod Mod
                constFold (a `Xor` b) =
                  let a' = constFold a
                      b' = constFold b
                  in folded a' b' xor Xor
                constFold (ArrayRead a ix) = 
                  let ix' = constFold ix
                  in ArrayRead a ix'
                constFold vf = vf -- TODO: more cases

                folded (Val a) (Val b) op _ = Val $ a `op` b
                folded      a       b  _ op =       a `op` b

forFromToStepUsing = ForFromToStepUsing




for2Program :: For -> Program Gr
for2Program for = p { observability = defaultObservabilityMap (tcfg p) }
  where p = compileAllToProgram (Map.fromList [ (1, "1") ]) (Map.fromList [("1", for) ])


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
    0x00,
    0x01, 0x02, 0x04, 0x08, 0x10, 0x20,
    0x40, 0x80, 0x1B, 0x36
 ]



{-
subBytesIteratorIndex   = Global "subBytesIteratorIndex"
addRoundIteratorIndex   = Global "addRoundIteratorIndex"
cbcEncRunIndex          = Global "cbcEncRunIndex"
encryptIndex            = Global "encryptIndex"
encryptIndexU           = Global "encryptIndexU"
-}
subBytesIteratorIndex   = Register 1
addRoundIteratorIndex   = Register 2
cbcEncRunIndex          = Register 3
encryptIndex            = Register 4
encryptIndexU           = Register 5
addRoundTmp             = Register 6
subBytesTmp             = Register 7
subBytesTmp2            = Register 8
addRoundTmp2            = Register 9
addRoundTmp3            = Register 10
ioTmp                   = Register 11
subBytesPreTmp          = Register 12
orderSkeyCacheTmp       = Register 13
orderVarCacheTmp        = Register 14

state                   = Array  "state"

aesKeySchedI            = Global "aesKeySchedI"
aesKeySchedJ            = Global "aesKeySchedJ"
aesKeySchedK            = Global "aesKeySchedK"
aesKeySchedNK           = Global "aesKeySchedNK"
aesKeySchedNKF          = Global "aesKeySchedNKF"


skey                    = Array  "skey"
key                     = Array  "key"

mixColumnsS = [ Global $ "a" ++ (show i) | i <- [0 .. 3] ]
mixColumnsB = [ Global $ "b" ++ (show i) | i <- [0 .. 3] ]
mixColumnsR = [ Global $ "r" ++ (show i) | i <- [0 .. 3] ]

subBytesCtX = [ Global $ "x" ++ (show i) | i <- [0 ..  7] ]
subBytesCtY = [ Global $ "y" ++ (show i) | i <- [1 .. 21] ]
subBytesCtZ = [ Global $ "z" ++ (show i) | i <- [0 .. 17] ]
subBytesCtT = [ Global $ "t" ++ (show i) | i <- [0 .. 67] ]
subBytesCtS = [ Global $ "s" ++ (show i) | i <- [0 .. 7] ]


expandKeyT = [ Global $ "w" ++ (show i) | i <- [0 .. 3] ]
expandKeyIndex          = Global "i"
expandKeyN            = Global "n"
expandKeySize         = Global "skey_offset"


shiftRowsTmp          = Global "shiftRowsTmp"

rotateTmp             = Global "rotateTmp"


allNames = assert (length vars == (Set.size $ Set.fromList vars))
         $ assert (length arrs == (Set.size $ Set.fromList arrs))
  where vars =   [subBytesIteratorIndex, addRoundIteratorIndex, shiftRowsTmp, cbcEncRunIndex, encryptIndex, encryptIndexU, expandKeyN] ++ mixColumnsS ++ mixColumnsR ++ mixColumnsB ++ expandKeyT
             ++  [aesKeySchedI, aesKeySchedJ, aesKeySchedK, aesKeySchedNK, aesKeySchedNKF]
        arrs = [skey, key]

br_aes_S :: For
br_aes_S = assert (length sboxConst == 256) $ 
  foldr Seq Skip [ AssArr sbox (Val i) (Val sval) | (i,sval) <- zip [0..255] sboxConst]


simpleRcon :: For
simpleRcon = assert (length rconConst == 11) $ 
  foldr Seq Skip [ AssArr rcon (Val i) (Val rcval) | (i,rcval) <- zip [0..10] rconConst]


mainInput :: For
mainInput = 
        (foldr Seq Skip [ AssArr state (Val i) (Val i) | i <- [0..15]])
  `Seq` (foldr Seq Skip [ AssArr key   (Val i) (Val i) | i <- [0..31]])




type AddRound = VarFunction -> For

addRoundFor :: SubPrograms -> AddRound
addRoundFor (SubPrograms { precacheArray }) offset =
                       precacheArray wholeArray skey
                `Seq`  forFromToStepUsing 0 15 1 i (
                                 Ass tmp  (ArrayRead state (AssertRange 0 15 $ Var i))
                           `Seq` Ass tmp3 (Var i `Plus` offset)
                           `Seq` Ass tmp2 (ArrayRead skey (Var tmp3))
                           `Seq` Ass tmp (Var tmp `Xor` (Var tmp2))
                           `Seq` AssArr state (AssertRange 0 15 $ Var i) (Var tmp)
                       )
                `Seq`  precacheArray wholeArray skey
  where i = addRoundIteratorIndex
        tmp  = addRoundTmp
        tmp2 = addRoundTmp2
        tmp3 = addRoundTmp3 



type SubBytes = For
sub_bytes_ :: SubBytes
sub_bytes_ =
                       forFromToStepUsing 0 15 1 i (
                                 Ass tmp1 (ArrayRead state (AssertRange 0 15 $ Var i))
                           `Seq` Ass tmp2 (ArrayRead sbox (Var tmp1))
                           `Seq` AssArr state (AssertRange 0 15 $ Var i) (Var tmp2)
                       )
  where i = subBytesIteratorIndex
        tmp1 = subBytesTmp
        tmp2 = subBytesTmp2


sub_bytes_ct_precache :: For
sub_bytes_ct_precache =
                           Ass tmp (ArrayRead sbox (Val   0))
                 `Seq`     Ass tmp (ArrayRead sbox (Val  64))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 128))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 192))
                 `Seq` forFromToStepUsing 0 15 1 i (
                                 Ass tmp1 (ArrayRead state (AssertRange 0 15 $ Var i))
                           `Seq` Ass tmp2 (ArrayRead sbox (Var tmp1))
                           `Seq` AssArr state (AssertRange 0 15 $ Var i) (Var tmp2)
                       )
                 `Seq`     Ass tmp (ArrayRead sbox (Val   0))
                 `Seq`     Ass tmp (ArrayRead sbox (Val  64))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 128))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 192))
  where i = subBytesIteratorIndex
        tmp1 = subBytesTmp
        tmp2 = subBytesTmp2
        tmp  = subBytesPreTmp

type SubBytes4 = Var -> Var -> Var -> Var -> For
sub_bytes_4_ :: SubBytes4
sub_bytes_4_ v0 v1 v2 v3 = 
                           Ass v0 (ArrayRead sbox (Var v0))
                 `Seq`     Ass v1 (ArrayRead sbox (Var v1))
                 `Seq`     Ass v2 (ArrayRead sbox (Var v2))
                 `Seq`     Ass v3 (ArrayRead sbox (Var v3))


sub_bytes_4_ct_precache :: SubBytes4
sub_bytes_4_ct_precache v0 v1 v2 v3 =
                           Ass tmp (ArrayRead sbox (Val   0))
                 `Seq`     Ass tmp (ArrayRead sbox (Val  64))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 128))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 192))
                 `Seq`     Ass v0 (ArrayRead sbox (Var v0))
                 `Seq`     Ass v1 (ArrayRead sbox (Var v1))
                 `Seq`     Ass v2 (ArrayRead sbox (Var v2))
                 `Seq`     Ass v3 (ArrayRead sbox (Var v3))
                 `Seq`     Ass tmp (ArrayRead sbox (Val   0))
                 `Seq`     Ass tmp (ArrayRead sbox (Val  64))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 128))
                 `Seq`     Ass tmp (ArrayRead sbox (Val 192))
  where tmp = subBytesPreTmp


sub_bytes_ct :: For
sub_bytes_ct =
          sub_bytes_ct_8 (a  0) (a  1) (a  2) (a  3) (a  4) (a  5) (a  6) (a  7)   (f  0) (f  1) (f  2) (f  3) (f  4) (f  5) (f  6) (f  7)
    `Seq` sub_bytes_ct_8 (a  8) (a  9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)   (f  8) (f  9) (f 10) (f 11) (f 12) (f 13) (f 14) (f 15)
  where a i = ArrayRead state (Val i)
        f i = AssArr state (Val i)

sub_bytes_4_ct :: SubBytes4
sub_bytes_4_ct v0 v1 v2 v3 =
  sub_bytes_ct_8 t0 t1 t2 t3 t0 t1 t2 t3
                 f0 f1 f2 f3 f0 f1 f2 f3
  where t0 = Var v0
        t1 = Var v1
        t2 = Var v2
        t3 = Var v3
        
        f0 = Ass v0
        f1 = Ass v1
        f2 = Ass v2
        f3 = Ass v3

type VarFunctionF = VarFunction -> For


{-
       /*
	 * This S-box implementation is a straightforward translation of
	 * the circuit described by Boyar and Peralta in "A new
	 * combinational logic minimization technique with applications
	 * to cryptology" (https://eprint.iacr.org/2009/191.pdf).
	 *
	 * Note that variables x* (input) and s* (output) are numbered
	 * in "reverse" order (x0 is the high bit, x7 is the low bit).
	 */
-}

sub_bytes_ct_8 ::
     VarFunction  -> VarFunction  -> VarFunction  -> VarFunction  -> VarFunction  -> VarFunction  -> VarFunction  -> VarFunction  
  -> VarFunctionF -> VarFunctionF -> VarFunctionF -> VarFunctionF -> VarFunctionF -> VarFunctionF -> VarFunctionF -> VarFunctionF
  -> For
sub_bytes_ct_8 a0 a1 a2 a3 a4 a5 a6 a7 
               f0 f1 f2 f3 f4 f5 f6 f7 = sub
  where [x0 , x1 , x2 , x3 , x4 , x5 , x6 , x7           ] = subBytesCtX
        [     y1 , y2 , y3 , y4 , y5 , y6 , y7 , y8 , y9 ,
         y10, y11, y12, y13, y14, y15, y16, y17, y18, y19,
         y20, y21                                        ] = subBytesCtY
        [ z0, z1 , z2 , z3 , z4 , z5 , z6 , z7 , z8 , z9 ,
         z10, z11, z12, z13, z14, z15, z16, z17          ] = subBytesCtZ
        [t0 , t1 , t2 , t3 , t4 , t5 , t6 , t7 , t8 , t9 ,
         t10, t11, t12, t13, t14, t15, t16, t17, t18, t19,
         t20, t21, t22, t23, t24, t25, t26, t27, t28, t29,
         t30, t31, t32, t33, t34, t35, t36, t37, t38, t39,
         t40, t41, t42, t43, t44, t45, t46, t47, t48, t49,
         t50, t51, t52, t53, t54, t55, t56, t57, t58, t59,
         t60, t61, t62, t63, t64, t65, t66, t67          ] = subBytesCtT
        [s0 , s1 , s2 , s3 , s4 , s5 , s6 , s7           ] = subBytesCtS

        sub =          Ass x0 (       (a0 `BAnd` (Val 128))
                                `Xor` (a1 `BAnd` (Val 128) `Shr` (Val 1))
                                `Xor` (a2 `BAnd` (Val 128) `Shr` (Val 2))
                                `Xor` (a3 `BAnd` (Val 128) `Shr` (Val 3))
                                `Xor` (a4 `BAnd` (Val 128) `Shr` (Val 4))
                                `Xor` (a5 `BAnd` (Val 128) `Shr` (Val 5))
                                `Xor` (a6 `BAnd` (Val 128) `Shr` (Val 6))
                                `Xor` (a7 `BAnd` (Val 128) `Shr` (Val 7))
                               )
                 `Seq` Ass x1 (       (a0 `BAnd` (Val  64) `Shl` (Val 1))
                                `Xor` (a1 `BAnd` (Val  64)              )
                                `Xor` (a2 `BAnd` (Val  64) `Shr` (Val 1))
                                `Xor` (a3 `BAnd` (Val  64) `Shr` (Val 2))
                                `Xor` (a4 `BAnd` (Val  64) `Shr` (Val 3))
                                `Xor` (a5 `BAnd` (Val  64) `Shr` (Val 4))
                                `Xor` (a6 `BAnd` (Val  64) `Shr` (Val 5))
                                `Xor` (a7 `BAnd` (Val  64) `Shr` (Val 6))
                               )
                 `Seq` Ass x2 (       (a0 `BAnd` (Val  32) `Shl` (Val 2))
                                `Xor` (a1 `BAnd` (Val  32) `Shl` (Val 1))
                                `Xor` (a2 `BAnd` (Val  32))
                                `Xor` (a3 `BAnd` (Val  32) `Shr` (Val 1))
                                `Xor` (a4 `BAnd` (Val  32) `Shr` (Val 2))
                                `Xor` (a5 `BAnd` (Val  32) `Shr` (Val 3))
                                `Xor` (a6 `BAnd` (Val  32) `Shr` (Val 4))
                                `Xor` (a7 `BAnd` (Val  32) `Shr` (Val 5))
                               )
                 `Seq` Ass x3 (       (a0 `BAnd` (Val  16) `Shl` (Val 3))
                                `Xor` (a1 `BAnd` (Val  16) `Shl` (Val 2))
                                `Xor` (a2 `BAnd` (Val  16) `Shl` (Val 1))
                                `Xor` (a3 `BAnd` (Val  16)              )
                                `Xor` (a4 `BAnd` (Val  16) `Shr` (Val 1))
                                `Xor` (a5 `BAnd` (Val  16) `Shr` (Val 2))
                                `Xor` (a6 `BAnd` (Val  16) `Shr` (Val 3))
                                `Xor` (a7 `BAnd` (Val  16) `Shr` (Val 4))
                               )
                 `Seq` Ass x4 (       (a0 `BAnd` (Val   8) `Shl` (Val 4))
                                `Xor` (a1 `BAnd` (Val   8) `Shl` (Val 3))
                                `Xor` (a2 `BAnd` (Val   8) `Shl` (Val 2))
                                `Xor` (a3 `BAnd` (Val   8) `Shl` (Val 1))
                                `Xor` (a4 `BAnd` (Val   8))
                                `Xor` (a5 `BAnd` (Val   8) `Shr` (Val 1))
                                `Xor` (a6 `BAnd` (Val   8) `Shr` (Val 2))
                                `Xor` (a7 `BAnd` (Val   8) `Shr` (Val 3))
                               )
                 `Seq` Ass x5 (       (a0 `BAnd` (Val   4) `Shl` (Val 5))
                                `Xor` (a1 `BAnd` (Val   4) `Shl` (Val 4))
                                `Xor` (a2 `BAnd` (Val   4) `Shl` (Val 3))
                                `Xor` (a3 `BAnd` (Val   4) `Shl` (Val 2))
                                `Xor` (a4 `BAnd` (Val   4) `Shl` (Val 1))
                                `Xor` (a5 `BAnd` (Val   4))
                                `Xor` (a6 `BAnd` (Val   4) `Shr` (Val 1))
                                `Xor` (a7 `BAnd` (Val   4) `Shr` (Val 2))
                               )
                 `Seq` Ass x6 (       (a0 `BAnd` (Val   2) `Shl` (Val 6))
                                `Xor` (a1 `BAnd` (Val   2) `Shl` (Val 5))
                                `Xor` (a2 `BAnd` (Val   2) `Shl` (Val 4))
                                `Xor` (a3 `BAnd` (Val   2) `Shl` (Val 3))
                                `Xor` (a4 `BAnd` (Val   2) `Shl` (Val 2))
                                `Xor` (a5 `BAnd` (Val   2) `Shl` (Val 1))
                                `Xor` (a6 `BAnd` (Val   2))
                                `Xor` (a7 `BAnd` (Val   2) `Shr` (Val 1))
                               )
                 `Seq` Ass x7 (       (a0 `BAnd` (Val   1) `Shl` (Val 7))
                                `Xor` (a1 `BAnd` (Val   1) `Shl` (Val 6))
                                `Xor` (a2 `BAnd` (Val   1) `Shl` (Val 5))
                                `Xor` (a3 `BAnd` (Val   1) `Shl` (Val 4))
                                `Xor` (a4 `BAnd` (Val   1) `Shl` (Val 3))
                                `Xor` (a5 `BAnd` (Val   1) `Shl` (Val 2))
                                `Xor` (a6 `BAnd` (Val   1) `Shl` (Val 1))
                                `Xor` (a7 `BAnd` (Val   1))
                               )
                 `Seq` Ass y14 (Var x3  `Xor` (Var x5))
                 `Seq` Ass y13 (Var x0  `Xor` (Var x6))
                 `Seq` Ass y9  (Var x0  `Xor` (Var x3))
                 `Seq` Ass y8  (Var x0  `Xor` (Var x5))
                 `Seq` Ass t0  (Var x1  `Xor` (Var x2))
                 `Seq` Ass y1  (Var t0  `Xor` (Var x7))
                 `Seq` Ass y4  (Var y1  `Xor` (Var x3))
                 `Seq` Ass y12 (Var y13 `Xor` (Var y14))
                 `Seq` Ass y2  (Var y1  `Xor` (Var x0))
                 `Seq` Ass y5  (Var y1  `Xor` (Var x6))
                 `Seq` Ass y3  (Var y5  `Xor` (Var y8))
                 `Seq` Ass t1  (Var x4  `Xor` (Var y12))
                 `Seq` Ass y15 (Var t1  `Xor` (Var x5))
                 `Seq` Ass y20 (Var t1  `Xor` (Var x1))
                 `Seq` Ass y6  (Var y15 `Xor` (Var x7))
                 `Seq` Ass y10 (Var y15 `Xor` (Var t0))
                 `Seq` Ass y11 (Var y20 `Xor` (Var y9))
                 `Seq` Ass y7  (Var x7  `Xor` (Var y11))
                 `Seq` Ass y17 (Var y10 `Xor` (Var y11))
                 `Seq` Ass y19 (Var y10 `Xor` (Var y8))
                 `Seq` Ass y16 (Var t0  `Xor` (Var y11))
                 `Seq` Ass y21 (Var y13 `Xor` (Var y16))
                 `Seq` Ass y18 (Var x0  `Xor` (Var y16))
                       
                 `Seq` Ass t2  (Var y12 `BAnd` (Var y15))
                 `Seq` Ass t3  (Var y3  `BAnd` (Var y6))
                 `Seq` Ass t4  (Var t3  `Xor`  (Var t2))
                 `Seq` Ass t5  (Var y4  `BAnd` (Var x7))
                 `Seq` Ass t6  (Var t5  `Xor`  (Var t2))
                 `Seq` Ass t7  (Var y13 `BAnd` (Var y16))
                 `Seq` Ass t8  (Var y5  `BAnd` (Var y1))
                 `Seq` Ass t9  (Var t8  `Xor`  (Var t7))
                 `Seq` Ass t10 (Var y2  `BAnd` (Var y7))
                 `Seq` Ass t11 (Var t10 `Xor`  (Var t7))
                 `Seq` Ass t12 (Var y9  `BAnd` (Var y11))
                 `Seq` Ass t13 (Var y14 `BAnd` (Var y17))
                 `Seq` Ass t14 (Var t13 `Xor`  (Var t12))
                 `Seq` Ass t15 (Var y8  `BAnd` (Var y10))
                 `Seq` Ass t16 (Var t15 `Xor`  (Var t12))
                 `Seq` Ass t17 (Var t4  `Xor`  (Var t14))
                 `Seq` Ass t18 (Var t6  `Xor`  (Var t16))
                 `Seq` Ass t19 (Var t9  `Xor`  (Var t14))
                 `Seq` Ass t20 (Var t11 `Xor`  (Var t16))
                 `Seq` Ass t21 (Var t17 `Xor`  (Var y20))
                 `Seq` Ass t22 (Var t18 `Xor`  (Var y19))
                 `Seq` Ass t23 (Var t19 `Xor`  (Var y21))
                 `Seq` Ass t24 (Var t20 `Xor`  (Var y18))

                 `Seq` Ass t25 (Var t21 `Xor`  (Var t22))
                 `Seq` Ass t26 (Var t21 `BAnd` (Var t23))
                 `Seq` Ass t27 (Var t24 `Xor`  (Var t26))
                 `Seq` Ass t28 (Var t25 `BAnd` (Var t27))
                 `Seq` Ass t29 (Var t28 `Xor`  (Var t22))
                 `Seq` Ass t30 (Var t23 `Xor`  (Var t24))
                 `Seq` Ass t31 (Var t22 `Xor`  (Var t26))
                 `Seq` Ass t32 (Var t31 `BAnd` (Var t30))
                 `Seq` Ass t33 (Var t32 `Xor`  (Var t24))
                 `Seq` Ass t34 (Var t23 `Xor`  (Var t33))
                 `Seq` Ass t35 (Var t27 `Xor`  (Var t33))
                 `Seq` Ass t36 (Var t24 `BAnd` (Var t35))
                 `Seq` Ass t37 (Var t36 `Xor`  (Var t34))
                 `Seq` Ass t38 (Var t27 `Xor`  (Var t36))
                 `Seq` Ass t39 (Var t29 `BAnd` (Var t38))
                 `Seq` Ass t40 (Var t25 `Xor`  (Var t39))

                 `Seq` Ass t41 (Var t40 `Xor`  (Var t37))
                 `Seq` Ass t42 (Var t29 `Xor`  (Var t33))
                 `Seq` Ass t43 (Var t29 `Xor`  (Var t40))
                 `Seq` Ass t44 (Var t33 `Xor`  (Var t37))
                 `Seq` Ass t45 (Var t42 `Xor`  (Var t41))
                 `Seq` Ass z0  (Var t44 `BAnd` (Var y15))
                 `Seq` Ass z1  (Var t37 `BAnd` (Var y6))
                 `Seq` Ass z2  (Var t33 `BAnd` (Var x7))
                 `Seq` Ass z3  (Var t43 `BAnd` (Var y16))
                 `Seq` Ass z4  (Var t40 `BAnd` (Var y1))
                 `Seq` Ass z5  (Var t29 `BAnd` (Var y7))
                 `Seq` Ass z6  (Var t42 `BAnd` (Var y11))
                 `Seq` Ass z7  (Var t45 `BAnd` (Var y17))
                 `Seq` Ass z8  (Var t41 `BAnd` (Var y10))
                 `Seq` Ass z9  (Var t44 `BAnd` (Var y12))
                 `Seq` Ass z10 (Var t37 `BAnd` (Var y3))
                 `Seq` Ass z11 (Var t33 `BAnd` (Var y4))
                 `Seq` Ass z12 (Var t43 `BAnd` (Var y13))
                 `Seq` Ass z13 (Var t40 `BAnd` (Var y5))
                 `Seq` Ass z14 (Var t29 `BAnd` (Var y2))
                 `Seq` Ass z15 (Var t42 `BAnd` (Var y9))
                 `Seq` Ass z16 (Var t45 `BAnd` (Var y14))
                 `Seq` Ass z17 (Var t41 `BAnd` (Var y8))

                 `Seq` Ass t46 (Var z15 `Xor` (Var z16))
                 `Seq` Ass t47 (Var z10 `Xor` (Var z11))
                 `Seq` Ass t48 (Var z5  `Xor` (Var z13))
                 `Seq` Ass t49 (Var z9  `Xor` (Var z10))
                 `Seq` Ass t50 (Var z2  `Xor` (Var z12))
                 `Seq` Ass t51 (Var z2  `Xor` (Var z5))
                 `Seq` Ass t52 (Var z7  `Xor` (Var z8))
                 `Seq` Ass t53 (Var z0  `Xor` (Var z3))
                 `Seq` Ass t54 (Var z6  `Xor` (Var z7))
                 `Seq` Ass t55 (Var z16 `Xor` (Var z17))
                 `Seq` Ass t56 (Var z12 `Xor` (Var t48))
                 `Seq` Ass t57 (Var t50 `Xor` (Var t53))
                 `Seq` Ass t58 (Var z4  `Xor` (Var t46))
                 `Seq` Ass t59 (Var z3  `Xor` (Var t54))
                 `Seq` Ass t60 (Var t46 `Xor` (Var t57))
                 `Seq` Ass t61 (Var z14 `Xor` (Var t57))
                 `Seq` Ass t62 (Var t52 `Xor` (Var t58))
                 `Seq` Ass t63 (Var t49 `Xor` (Var t58))
                 `Seq` Ass t64 (Var z4  `Xor` (Var t59))
                 `Seq` Ass t65 (Var t61 `Xor` (Var t62))
                 `Seq` Ass t66 (Var z1  `Xor` (Var t63))
                 `Seq` Ass s0  (Var t59 `Xor` (Var t63))
                 `Seq` Ass s6  (Var t56 `Xor` (BNot $ Var t62))
                 `Seq` Ass s7  (Var t48 `Xor` (BNot $ Var t60))
                 `Seq` Ass t67 (Var t64 `Xor` (Var t65))
                 `Seq` Ass s3 (Var t53 `Xor` (Var t66))
                 `Seq` Ass s4 (Var t51 `Xor` (Var t66))
                 `Seq` Ass s5 (Var t47 `Xor` (Var t65))
                 `Seq` Ass s1  (Var t64 `Xor` (BNot $ Var s3))
                 `Seq` Ass s2  (Var t55 `Xor` (BNot $ Var t67))


                 `Seq`                   f0  (       (Var s0 `BAnd` (Val 128)              )
                                               `Xor` (Var s1 `BAnd` (Val 128) `Shr` (Val 1))
                                               `Xor` (Var s2 `BAnd` (Val 128) `Shr` (Val 2))
                                               `Xor` (Var s3 `BAnd` (Val 128) `Shr` (Val 3))
                                               `Xor` (Var s4 `BAnd` (Val 128) `Shr` (Val 4))
                                               `Xor` (Var s5 `BAnd` (Val 128) `Shr` (Val 5))
                                               `Xor` (Var s6 `BAnd` (Val 128) `Shr` (Val 6))
                                               `Xor` (Var s7 `BAnd` (Val 128) `Shr` (Val 7))
                                             )
                 `Seq`                    f1 (       (Var s0 `BAnd` (Val  64) `Shl` (Val 1))
                                               `Xor` (Var s1 `BAnd` (Val  64)              )
                                               `Xor` (Var s2 `BAnd` (Val  64) `Shr` (Val 1))
                                               `Xor` (Var s3 `BAnd` (Val  64) `Shr` (Val 2))
                                               `Xor` (Var s4 `BAnd` (Val  64) `Shr` (Val 3))
                                               `Xor` (Var s5 `BAnd` (Val  64) `Shr` (Val 4))
                                               `Xor` (Var s6 `BAnd` (Val  64) `Shr` (Val 5))
                                               `Xor` (Var s7 `BAnd` (Val  64) `Shr` (Val 6))
                                             )
                 `Seq`                    f2 (       (Var s0 `BAnd` (Val  32) `Shl` (Val 2))
                                               `Xor` (Var s1 `BAnd` (Val  32) `Shl` (Val 1))
                                               `Xor` (Var s2 `BAnd` (Val  32))
                                               `Xor` (Var s3 `BAnd` (Val  32) `Shr` (Val 1))
                                               `Xor` (Var s4 `BAnd` (Val  32) `Shr` (Val 2))
                                               `Xor` (Var s5 `BAnd` (Val  32) `Shr` (Val 3))
                                               `Xor` (Var s6 `BAnd` (Val  32) `Shr` (Val 4))
                                               `Xor` (Var s7 `BAnd` (Val  32) `Shr` (Val 5))
                                             )
                 `Seq`                    f3 (       (Var s0 `BAnd` (Val  16) `Shl` (Val 3))
                                               `Xor` (Var s1 `BAnd` (Val  16) `Shl` (Val 2))
                                               `Xor` (Var s2 `BAnd` (Val  16) `Shl` (Val 1))
                                               `Xor` (Var s3 `BAnd` (Val  16))
                                               `Xor` (Var s4 `BAnd` (Val  16) `Shr` (Val 1))
                                               `Xor` (Var s5 `BAnd` (Val  16) `Shr` (Val 2))
                                               `Xor` (Var s6 `BAnd` (Val  16) `Shr` (Val 3))
                                               `Xor` (Var s7 `BAnd` (Val  16) `Shr` (Val 4))
                                             )
                 `Seq`                    f4 (       (Var s0 `BAnd` (Val   8) `Shl` (Val 4))
                                               `Xor` (Var s1 `BAnd` (Val   8) `Shl` (Val 3))
                                               `Xor` (Var s2 `BAnd` (Val   8) `Shl` (Val 2))
                                               `Xor` (Var s3 `BAnd` (Val   8) `Shl` (Val 1))
                                               `Xor` (Var s4 `BAnd` (Val   8))
                                               `Xor` (Var s5 `BAnd` (Val   8) `Shr` (Val 1))
                                               `Xor` (Var s6 `BAnd` (Val   8) `Shr` (Val 2))
                                               `Xor` (Var s7 `BAnd` (Val   8) `Shr` (Val 3))
                                             )
                 `Seq`                    f5 (       (Var s0 `BAnd` (Val   4) `Shl` (Val 5))
                                               `Xor` (Var s1 `BAnd` (Val   4) `Shl` (Val 4))
                                               `Xor` (Var s2 `BAnd` (Val   4) `Shl` (Val 3))
                                               `Xor` (Var s3 `BAnd` (Val   4) `Shl` (Val 2))
                                               `Xor` (Var s4 `BAnd` (Val   4) `Shl` (Val 1))
                                               `Xor` (Var s5 `BAnd` (Val   4))
                                               `Xor` (Var s6 `BAnd` (Val   4) `Shr` (Val 1))
                                               `Xor` (Var s7 `BAnd` (Val   4) `Shr` (Val 2))
                                             )
                 `Seq`                    f6 (       (Var s0 `BAnd` (Val   2) `Shl` (Val 6))
                                               `Xor` (Var s1 `BAnd` (Val   2) `Shl` (Val 5))
                                               `Xor` (Var s2 `BAnd` (Val   2) `Shl` (Val 4))
                                               `Xor` (Var s3 `BAnd` (Val   2) `Shl` (Val 3))
                                               `Xor` (Var s4 `BAnd` (Val   2) `Shl` (Val 2))
                                               `Xor` (Var s5 `BAnd` (Val   2) `Shl` (Val 1))
                                               `Xor` (Var s6 `BAnd` (Val   2))
                                               `Xor` (Var s7 `BAnd` (Val   2) `Shr` (Val 1))
                                             )
                 `Seq`                    f7 (       (Var s0 `BAnd` (Val   1) `Shl` (Val 7))
                                               `Xor` (Var s1 `BAnd` (Val   1) `Shl` (Val 6))
                                               `Xor` (Var s2 `BAnd` (Val   1) `Shl` (Val 5))
                                               `Xor` (Var s3 `BAnd` (Val   1) `Shl` (Val 4))
                                               `Xor` (Var s4 `BAnd` (Val   1) `Shl` (Val 3))
                                               `Xor` (Var s5 `BAnd` (Val   1) `Shl` (Val 2))
                                               `Xor` (Var s6 `BAnd` (Val   1) `Shl` (Val 1))
                                               `Xor` (Var s7 `BAnd` (Val   1))
                                             )

type ShiftRows = For
shift_rows :: ShiftRows
shift_rows =
                       Ass tmp (ArrayRead state (Val 1))
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




mixColumns :: For
mixColumns = 
                       for  0
                 `Seq` for  4
                 `Seq` for  8
                 `Seq` for 12
  where s0 = mixColumnsS !! 0
        s1 = mixColumnsS !! 1
        s2 = mixColumnsS !! 2
        s3 = mixColumnsS !! 3

        b0 = mixColumnsB !! 0
        b1 = mixColumnsB !! 1
        b2 = mixColumnsB !! 2
        b3 = mixColumnsB !! 3
        
        r0 = mixColumnsR !! 0
        r1 = mixColumnsR !! 1
        r2 = mixColumnsR !! 2
        r3 = mixColumnsR !! 3

        for i = 
                       Ass s0 (ArrayRead state (Val $ i + 0))
                 `Seq` Ass s1 (ArrayRead state (Val $ i + 1))
                 `Seq` Ass s2 (ArrayRead state (Val $ i + 2))
                 `Seq` Ass s3 (ArrayRead state (Val $ i + 3))

                 `Seq` Ass b0 ((Var s0 `Shl` (Val 1)) `Xor` (Val 0x1b `BAnd` ((Var s0 `Shr` (Val 7)) `Times` (Val 255))))
                 `Seq` Ass b1 ((Var s1 `Shl` (Val 1)) `Xor` (Val 0x1b `BAnd` ((Var s1 `Shr` (Val 7)) `Times` (Val 255))))
                 `Seq` Ass b2 ((Var s2 `Shl` (Val 1)) `Xor` (Val 0x1b `BAnd` ((Var s2 `Shr` (Val 7)) `Times` (Val 255))))
                 `Seq` Ass b3 ((Var s3 `Shl` (Val 1)) `Xor` (Val 0x1b `BAnd` ((Var s3 `Shr` (Val 7)) `Times` (Val 255))))

                 `Seq` Ass r0 ((Var b0) `Xor` (Var s1) `Xor` (Var b1) `Xor` (Var s2) `Xor` (Var s3))
                 `Seq` Ass r1 ((Var s0) `Xor` (Var b1) `Xor` (Var s2) `Xor` (Var b2) `Xor` (Var s3))
                 `Seq` Ass r2 ((Var s0) `Xor` (Var s1) `Xor` (Var b2) `Xor` (Var s3) `Xor` (Var b3))
                 `Seq` Ass r3 ((Var s0) `Xor` (Var b0) `Xor` (Var s1) `Xor` (Var s2) `Xor` (Var b3))
                 
                 `Seq` AssArr state (Val $ i + 0) (Var r0)
                 `Seq` AssArr state (Val $ i + 1) (Var r1)
                 `Seq` AssArr state (Val $ i + 2) (Var r2)
                 `Seq` AssArr state (Val $ i + 3) (Var r3)


scheduleSize256 :: Int
scheduleSize256 = 240

keySize :: Int
keySize = 256

num_rounds = 14
key_len = 32 -- 32 * 8 == 256

type ScheduleCore = Var -> Var -> Var -> Var -> Var -> For

scheduleCoreFor :: SubPrograms -> ScheduleCore
scheduleCoreFor (SubPrograms { sub_bytes_4 }) t0 t1 t2 t3 n =
                       rotate
                 `Seq` sub_bytes_4 t0 t1 t2 t3
                 `Seq` Ass t0 (Var t0 `Xor` (ArrayRead rcon (AssertRange 0 10 $ (Var n))))
  where rotate =
                       Ass tmp (Var t0)
                 `Seq` Ass t0  (Var t1)
                 `Seq` Ass t1  (Var t2)
                 `Seq` Ass t2  (Var t3)
                 `Seq` Ass t3  (Var tmp)
          where tmp = rotateTmp

expandKeyFor :: SubPrograms -> For
expandKeyFor subs@(SubPrograms { sub_bytes_4, precacheArray, precacheVar }) =
                       precacheArray wholeArray skey
                 `Seq` precacheArray wholeArray state
                 `Seq` precacheArray [0] rcon
                 `Seq` Ass n (Val 1)
                 `Seq` forFromToStepUsing 0 31 1 i (
                                 AssArr skey (AssertRange 0 31 $ Var i) (ArrayRead key (AssertRange 0 31 $ Var i))
                       )
                 `Seq` forFromToStepUsing (from $ keySize `div` 8) (from $ scheduleSize256 - 4) 4 size body
  where body =
                       precacheArray wholeArray skey
                 `Seq` Ass t0 (ArrayRead skey (Var size `Minus` (Val 4)))
                 `Seq` Ass t1 (ArrayRead skey (Var size `Minus` (Val 3)))
                 `Seq` Ass t2 (ArrayRead skey (Var size `Minus` (Val 2)))
                 `Seq` Ass t3 (ArrayRead skey (Var size `Minus` (Val 1)))

                 `Seq` (If ((Var size `Mod` (Val $ from $ keySize `div` 8)) `Eeq` (Val  0)) {- then -} (
                           scheduleCoreFor subs t0 t1 t2 t3 n
                     `Seq` precacheVar t1
                     `Seq` precacheVar t2
                     `Seq` precacheVar t3
                 `Seq`     Ass n (Var n `Plus` (Val 1))
                       ) {- else -} (
                           Skip
                       ))
                 `Seq` precacheArray wholeArray sbox
                 `Seq` (If ((Var size `Mod` (Val $ from $ keySize `div` 8)) `Eeq` (Val 16)) {- then -} (
                           sub_bytes_4 t0 t1 t2 t3
                       ) {- else -} (
                           precacheVar t0
                     `Seq` precacheVar t1
                     `Seq` precacheVar t2
                     `Seq` precacheVar t3
                       ))
                 `Seq` precacheArray wholeArray sbox
                 `Seq` precacheArray wholeArray skey
                 `Seq` AssArr skey (Var size `Plus` (Val 0)) (ArrayRead skey (Var size  `Minus` (Val $ from $ -0 + (keySize `div` 8))) `Xor` (Var t0))
                 `Seq` AssArr skey (Var size `Plus` (Val 1)) (ArrayRead skey (Var size  `Minus` (Val $ from $ -1 + (keySize `div` 8))) `Xor` (Var t1))
                 `Seq` AssArr skey (Var size `Plus` (Val 2)) (ArrayRead skey (Var size  `Minus` (Val $ from $ -2 + (keySize `div` 8))) `Xor` (Var t2))
                 `Seq` AssArr skey (Var size `Plus` (Val 3)) (ArrayRead skey (Var size  `Minus` (Val $ from $ -3 + (keySize `div` 8))) `Xor` (Var t3))

        i = expandKeyIndex 
        t0 = expandKeyT !! 0
        t1 = expandKeyT !! 1
        t2 = expandKeyT !! 2
        t3 = expandKeyT !! 3
        n = expandKeyN

        size = expandKeySize

        from :: Int -> Val
        from i = assert (min <= i  ∧  i <= max) $ fromIntegral i
          where min = fromIntegral (minBound :: Val)
                max = fromIntegral (maxBound :: Val)

br_aes_small_encryptFor subs@(SubPrograms { sub_bytes }) = 
                       addRoundFor subs (Val 0)
                 `Seq` forFromToStepUsing 1 (num_rounds - 1) 1 u (
                                 sub_bytes
                 `Seq`           shift_rows
                 `Seq`           mixColumns
                 `Seq`           addRoundFor subs (Var u `Shl` (Val 4))
                       )
                 `Seq` sub_bytes
                 `Seq` shift_rows
                 `Seq` addRoundFor subs (Val num_rounds `Shl` (Val 4))
  where u = encryptIndexU

data SubPrograms = SubPrograms {
    initConstants :: For,
    sub_bytes :: SubBytes,
    precacheArray :: PrecacheArray,
    precacheVar :: PrecacheVar,
    sub_bytes_4 :: SubBytes4
  }

subs_            = SubPrograms { initConstants = br_aes_S `Seq` simpleRcon, sub_bytes = sub_bytes_,            sub_bytes_4 = sub_bytes_4_,            precacheArray = const $ const Skip, precacheVar = const Skip }
subs_ct          = SubPrograms { initConstants =                simpleRcon, sub_bytes = sub_bytes_ct,          sub_bytes_4 = sub_bytes_4_ct,          precacheArray = const $ const Skip, precacheVar = const Skip}
subs_ct_precache = SubPrograms { initConstants = br_aes_S `Seq` simpleRcon, sub_bytes = sub_bytes_ct_precache, sub_bytes_4 = sub_bytes_4_ct_precache, precacheArray = precacheArray_ct_precache, precacheVar = pprecacheVar }

subs_procs = SubPrograms { initConstants = CallProcedure "initConstants", sub_bytes = CallProcedure "sub_bytes", sub_bytes_4 = const4 $ CallProcedure "sub_bytes_4", precacheArray = precacheArray, precacheVar = precacheVar }
  where const4 c _ _ _ _ = c
        precacheArray is a   = CallProcedure $ "precache " ++ (show is) ++ " in " ++ (simpleShow a)
        precacheVar x        = CallProcedure $ "precache "                        ++ (simpleShow x)


type Main = For -> For -> For
br_aes_small_cbcenc_mainFor :: SubPrograms -> Main
br_aes_small_cbcenc_mainFor subs@(SubPrograms { initConstants, precacheArray }) = \input output ->
                       Skip
                 `Seq` initConstants
                 `Seq` input
                 `Seq` expandKeyFor subs
                 `Seq` precacheArray wholeArray state
                 `Seq` br_aes_small_encryptFor subs
                 `Seq` output

br_aes_small_cbcenc_main    = br_aes_small_cbcenc_mainFor subs_
br_aes_small_cbcenc_main_ct = br_aes_small_cbcenc_mainFor subs_ct
br_aes_small_cbcenc_main_ct_precache =
                              br_aes_small_cbcenc_mainFor subs_ct_precache
br_aes_small_cbcenc_main_procs =
                              br_aes_small_cbcenc_mainFor subs_procs

type PrecacheArray = [Val] -> Array -> For

precacheArray_ct_precache :: PrecacheArray
precacheArray_ct_precache is skey = foldr Seq Skip [Ass tmp (ArrayRead skey (Val   i)) | i <- is]
  where tmp = orderSkeyCacheTmp

wholeArray :: [Val]
wholeArray = [0, 64, 128, 192]

type PrecacheVar = Var -> For

pprecacheVar :: PrecacheVar
pprecacheVar var = Ass tmp (Var var)
  where tmp = orderVarCacheTmp

ioInput :: For
ioInput =
          (foldr1 Seq [ ReadFromChannel tmp stdIn `Seq` AssArr state (Val i) (Var tmp) | i <- [0..15]])
    `Seq` (foldr1 Seq [ ReadFromChannel tmp stdIn `Seq` AssArr key   (Val i) (Var tmp) | i <- [0..(key_len - 1)]])
  where tmp = ioTmp

ioOutput = 
          (foldr1 Seq [ PrintToChannel  (ArrayRead state (Val i)) stdOut  | i <- [0..15]])

ioOutputSkey = 
          (foldr1 Seq [ PrintToChannel  (ArrayRead skey (Val i)) stdOut  | i <- [0..239]])

ioOutputKey = 
          (foldr1 Seq [ PrintToChannel  (ArrayRead key (Val i)) stdOut  | i <- [0..31]])

inputFor key state = Map.fromList [(stdIn, state ++ key)]

runAES256For :: Main -> [Word8] -> [Word8] -> [Word8]
runAES256For main = \key msg ->
  let program = for2Program $ main ioInput ioOutput :: Program Gr
      input = inputFor key msg
      traces = allFinishedExecutionTraces program input
      outputs =
          assert (length traces == 1)
        $ [ x | let [trace] = traces, (_,(_,PrintEvent x _,_),_) <- trace ]
  in outputs

runAES256 :: [Word8] -> [Word8] -> [Word8]
runAES256    = runAES256For br_aes_small_cbcenc_main

runAES256_ct :: [Word8] -> [Word8] -> [Word8]
runAES256_ct = runAES256For br_aes_small_cbcenc_main_ct

runAES256_ct_precache :: [Word8] -> [Word8] -> [Word8]
runAES256_ct_precache =
               runAES256For br_aes_small_cbcenc_main_ct_precache

cryptoTestSuit = [
                $(withName 'br_aes_small_cbcenc_main)
            ]
