{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheExecution where

import qualified Data.List as List

import Data.Bits (xor, (.&.), shiftL, shiftR, complement)

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Algebra.Lattice(JoinSemiLattice(..), BoundedJoinSemiLattice(..))

import Debug.Trace (traceShow)
import Control.Exception.Base (assert)


import Control.Monad.State
import Control.Monad.List


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic (grev)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.DFS (dfs, rdfs, topsort)
import Data.Graph.Inductive.Query.TransClos (trc)

import Unicode
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt, focus, removeFirstOrButLastMaxSize, removeFirstOrButLastAssocMaxSize)
import IRLSOD (CFGNode, CFGEdge(..), GlobalState(..), globalEmpty, ThreadLocalState, Var(..), isGlobal, Array(..), arrayIndex, isArrayIndex, arrayMaxIndex, arrayEmpty, ArrayVal, Val, BoolFunction(..), VarFunction(..), Name(..), useE, defE, useEFor, useBFor, useB, useV, use, def, SimpleShow (..), stepFor)
import qualified IRLSOD as IRLSOD (Input)

import Program (Program(..))
import Program.Generator (toCodeSimple)
import Program.For (compileAllToProgram, For(..), subCommands)

import Data.Graph.Inductive.Util (mergeTwoGraphs, isTransitive, fromSuccMap, delSuccessorEdges)
import Data.Graph.Inductive.Query.PostDominance (mdomOfLfp, sinkdomOfGfp, sinkdomsOf, isinkdomOfTwoFinger8)
import Data.Graph.Inductive.Query.PostDominance.Numbered (iPDomForSinks)
import Data.Graph.Inductive.Query.PostDominanceFrontiers (isinkDFTwoFinger)
import Data.Graph.Inductive.Query.Slices.PostDominance (wodTEILSliceViaISinkDom)

import           Data.Graph.Inductive.Query.InfiniteDelay (TraceWith (..), Trace)
import qualified Data.Graph.Inductive.Query.InfiniteDelay as InfiniteDelay (Input(..))

import MicroArchitecturalDependence (
    AbstractMicroArchitecturalGraphNode,
    ConcreteSemantic, AbstractSemantic,
    TimeState, NormalState,
    MergedMicroState(..),
    MicroArchitecturalAbstraction(..),
    stateGraphForSets, stateGraph, stateSets,
    muMergeDirectOf, muGraphFromMergeDirectFor
  )



cacheLineSize :: Int
cacheLineSize =
       assert ((max + 1) `mod` n == 0)
     $ assert ( n <= max + 1)
     $ n
  where max = fromIntegral arrayMaxIndex
        n = 64

cacheLineSizeVal = fromIntegral cacheLineSize

arrayMaxIndexInt :: Int
arrayMaxIndexInt = fromIntegral arrayMaxIndex

initialCacheLine   = [  0 | i <- [0 .. cacheLineSize - 1] ]
undefinedCacheLine = [0-1 | i <- [0 .. cacheLineSize - 1] ]

toAlignedIndex :: Val -> Val
toAlignedIndex i = require (isArrayIndex i) $ (i `div` cacheLineSizeVal) * cacheLineSizeVal


{- all possible cacheline aligned array indices -}
alignedIndices :: [Val]
alignedIndices = fmap fromIntegral [ cacheLineSize * (i-1) | i <- [1 ..  (arrayMaxIndexInt + 1) `div` cacheLineSize ]]
{- all possible cacheline aligned array indices relevant for an array acces at index x such that x is known to be: min <= x <= max -}
alignedIndicesFor min max = require (min <= max) $
    [ i | i <- alignedIndices, (i  < min  ∧  i + cacheLineSizeVal > min)  ∨  (min <= i ∧ i <= max) ]

nrOfDifferentCacheLinesPerArray = length $ alignedIndices



sliceFor :: Index -> ArrayVal -> ArrayVal
sliceFor ix array = between array left right
  where left  = toAlignedIndex ix
        right = left + cacheLineSizeVal - 1

        between :: Ord k => Map k v -> k -> k -> Map k v
        between map n m =
                  require (n < m) $
                  require (Map.member n map ∧ Map.member m map) $
                  let (  _, Just vn, right) = Map.splitLookup n map
                      (mid, Just vm,     _) = Map.splitLookup m right
                  in Map.insert n vn $ Map.insert m vm $ mid





type CacheSize = Int

type AccessTime = Integer

cacheMissTime :: AccessTime
cacheMissTime = 10

cacheHitTime  :: AccessTime
cacheHitTime  =  2

-- My cache model assumes a "asynchronous" write-throuh cache, i.e.: writes update the cache, and the main memory update executes "asynchronously" in the background, without stalling the cpu
cacheWriteTime :: AccessTime 
cacheWriteTime = 2

registerAccessTime :: AccessTime
registerAccessTime = 1

noOpTime  :: AccessTime
noOpTime = 1

guardTime :: AccessTime
guardTime = 1

initTime :: AccessTime
initTime = 1

removeFirstOrButLastAssoc = removeFirstOrButLastAssocMaxSize

type ArrayBound = Val

data CachedObject
    = CachedVar Var 
    | CachedArrayRange Array ArrayBound -- contents of Array from [ArrayBound ..to.. ArrayBound+cacheLineSize]
    | CachedUnknownRange Array          -- In an abstract cache [, .. CacheUnknownRange a  ..] represents a cacheline within array a with  unknown range
  deriving (Show, Eq, Ord)

data CacheValue = CachedVal Val | CachedArraySlice [Val] deriving (Show, Eq, Ord)

type          CacheState = [(CachedObject, CacheValue)]

type         CacheTimeState = (        CacheState, TimeState)
type FullState = (NormalState, CacheState, TimeState)

type Index = Val


instance SimpleShow CachedObject where
  simpleShow (CachedVar        var)  = simpleShow var
  simpleShow (CachedArrayRange (Array x) i) = x ++ "[" ++ (show i) ++ ".." ++ (show $ i + cacheLineSizeVal -1) ++ "]"
  simpleShow (CachedUnknownRange (Array x)) = x ++ "[ unknown .. unknown ]"

instance SimpleShow CacheValue where
  simpleShow (CachedVal        val ) = simpleShow val
  simpleShow (CachedArraySlice vals) = simpleShow vals


isCachable :: Name -> Bool
isCachable (VarName (Global _)) = True
isCachable (VarName (ThreadLocal _)) = False
isCachable (VarName (Register _)) = False
isCachable (ArrayName _) = True


twoAddressCode :: For -> For
twoAddressCode c = twoAddressCodeFrom r0 c
  where r0 = maximum ( 0 : [ r | c <- cs, r <- regsIn c ]) + 1000
        cs = subCommands c

        regsIn (If bf _ _)            =  [ r | VarName (Register r) <- Set.toList $ useB bf ]
        regsIn (ForC _ _)             =  []
        regsIn (ForV x _ )            =  [ r |         (Register r) <- [x] ]
        regsIn (Ass x vf)             =  [ r | VarName (Register r) <- Set.toList $ useV vf ]
                                      ++ [ r |         (Register r) <- [x] ]
        regsIn (AssArr a ix vf)       =  [ r | VarName (Register r) <- Set.toList $ useV ix ∪ useV vf ]
        regsIn (ReadFromChannel x _)  =  [ r |         (Register r) <- [x] ]
        regsIn (PrintToChannel  vf _) =  [ r | VarName (Register r) <- Set.toList $ useV vf ]
        regsIn (Skip)                 =  []
        regsIn (CallProcedure _)      =  []
        regsIn (SpawnThread _)        =  []
        regsIn (Seq _ _)              =  []


twoAddressCodeFrom :: Int -> For -> For
twoAddressCodeFrom r0 (If bf c1 c2) =
  let (loads, bf', _) = twoAddressCodeB r0 bf in case loads of
    Nothing ->          (If bf' (twoAddressCode c1) (twoAddressCode c2))
    Just ls -> ls `Seq` (If bf' (twoAddressCode c1) (twoAddressCode c2))
twoAddressCodeFrom r0  (Ass var vf)  =
  let (loads, vf', _) = twoAddressCodeV r0 vf in case loads of
    Nothing ->          (Ass var vf')
    Just ls -> ls `Seq` (Ass var vf')
twoAddressCodeFrom r0  (AssArr arr ix vf)  =
  let (loadsVf, vf', r) = twoAddressCodeV r0 vf
      (loadsIx, ix', _) = twoAddressCodeV r ix
      loads = loadsVf `sseq` loadsIx
  in case loads of
       Nothing ->          (AssArr arr ix' vf')
       Just ls -> ls `Seq` (AssArr arr ix' vf')
twoAddressCodeFrom r0  (ForC val c) = ForC val (twoAddressCodeFrom r0 c)
twoAddressCodeFrom r0  (ForV var c) = ForV var (twoAddressCodeFrom r0 c)
twoAddressCodeFrom r0  (Seq c1 c2 ) = Seq (twoAddressCodeFrom r0 c1) (twoAddressCodeFrom r0 c2)
twoAddressCodeFrom r0  c = c


twoAddressCodeB :: Int -> BoolFunction -> (Maybe For, BoolFunction, Int)
twoAddressCodeB r bf@CTrue =  (Nothing, bf, r)
twoAddressCodeB r bf@CFalse = (Nothing, bf, r)
twoAddressCodeB r bf@(Leq x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Leq x' y', r'')
twoAddressCodeB r bf@(Eeq x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Eeq x' y', r'')
twoAddressCodeB r bf@(And x y) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
        (loadsY, y', r'') = twoAddressCodeB r' y
    in (loadsX `sseq` loadsY, And x' y', r'')
twoAddressCodeB r bf@(Or x y) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
        (loadsY, y', r'') = twoAddressCodeB r' y
    in (loadsX `sseq` loadsY, And x' y', r'')
twoAddressCodeB r bf@(Not x) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
    in (loadsX, Not x', r')


sseq Nothing r = r
sseq l Nothing = l
sseq (Just l) (Just r) = Just (l `Seq` r)


twoAddressCodeV :: Int -> VarFunction -> (Maybe For, VarFunction, Int)
twoAddressCodeV r vf@(Val _) = (Nothing, vf, r)
twoAddressCodeV r vf@(Var (Register rr)) = assert (rr < r) $ (Nothing, vf, r)
twoAddressCodeV r (ArrayRead x ix) =
    let (loadsIx, ix', r' ) = twoAddressCodeV r ix
    in (loadsIx `sseq` (Just $ Ass (Register r') (ArrayRead x ix')), Var (Register r'), r' + 1)
twoAddressCodeV r vf@(Var x) = (Just $ Ass (Register r) vf, Var (Register r), r + 1)
twoAddressCodeV r vf@(Plus x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Plus x' y', r'')
twoAddressCodeV r vf@(Minus x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Minus x' y', r'')
twoAddressCodeV r vf@(Times x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Times x' y', r'')
twoAddressCodeV r vf@(Div x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Div x' y', r'')
twoAddressCodeV r vf@(Mod x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Mod x' y', r'')
twoAddressCodeV r vf@(Shl x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Shl x' y', r'')
twoAddressCodeV r vf@(Shr x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Shr x' y', r'')
twoAddressCodeV r vf@(Xor x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Xor x' y', r'')
twoAddressCodeV r vf@(BAnd x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, BAnd x' y', r'')
twoAddressCodeV r bf@(Neg x) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
    in (loadsX, Neg x', r')
twoAddressCodeV r bf@(BNot x) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
    in (loadsX, BNot x', r')
twoAddressCodeV r vf@(AssertRange min max x) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
    in (loadsX, (AssertRange min max x'), r')


consistent :: CacheSize -> FullState -> Bool
consistent cacheSize ((GlobalState { σv, σa }, tlσ, i), cache, _) = length cache <= cacheSize && (∀) (cache) cons
  where cons (CachedVar        var@(Global      x)      , CachedVal        val ) = val ==      σv ! var
        cons (CachedVar        var@(ThreadLocal x)      , CachedVal        val ) = val ==     tlσ ! var
        cons (CachedArrayRange arr@(Array       a) index, CachedArraySlice vals) = 
            (length vals == cacheLineSize) ∧ (index >= 0) ∧ (index `mod` cacheLineSizeVal == 0) ∧ (index <= arrayMaxIndex)
          ∧ (Map.size betw == cacheLineSize)
          ∧ (∀) (zipWith (==) vals (Map.elems betw)) id
          where betw :: ArrayVal
                betw = sliceFor index (σa ! arr)


cacheAwareReadLRU :: CacheSize -> Var -> FullState -> (Val, CacheState, AccessTime)
cacheAwareReadLRU cacheSize var σ@((GlobalState { σv }, tlσ, i), cache, _) = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ lookup     σv
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ (tlσ ! var, cache, registerAccessTime)
    Register    _ -> assert (not $ isCachable $ VarName var) $ (tlσ ! var, cache, registerAccessTime)
  where cvar = CachedVar var

        lookup :: Map Var Val -> (Val, CacheState, AccessTime )
        lookup someσ = 
          require (consistent cacheSize σ) $
          case removeFirstOrButLastAssoc cacheSize cvar cache of
            Right cache0 -> let { cval = CachedVal val ; val = someσ ! var } in
              (val, (cvar, cval) : cache0, cacheMissTime )
            Left (cval@(CachedVal val), cache0) ->
              (val, (cvar, cval) : cache0, cacheHitTime  )


cacheAwareArrayReadLRU :: CacheSize -> Array -> Index -> FullState -> (Val, CacheState, AccessTime)
cacheAwareArrayReadLRU cacheSize arr ix σ@((GlobalState { σa }, tlσ, _), cache, _) = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ lookup
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        lookup :: (Val, CacheState, AccessTime )
        lookup = 
          require (consistent cacheSize σ) $
          assert (alignedIx <= ix) $
          case removeFirstOrButLastAssoc cacheSize carr cache of
            Right                               cache0 -> let { cval = CachedArraySlice vals ; vals = Map.elems $ sliceFor alignedIx (σa ! arr) } in
              (vals !! (fromIntegral $ ix - alignedIx), (carr, cval) : cache0, cacheMissTime )
            Left (cval@(CachedArraySlice vals), cache0)->
              (vals !! (fromIntegral $ ix - alignedIx), (carr, cval) : cache0, cacheHitTime  )





cacheAwareReadLRUState :: Monad m => CacheSize -> Var -> StateT FullState m Val
cacheAwareReadLRUState cacheSize var = do
    σ@((globalσ,tlσ,i), cache, time) <- get
    let (val, cache', accessTime) = cacheAwareReadLRU cacheSize var σ
    put ((globalσ,tlσ,i), cache', time + accessTime)
    return val


cacheAwareArrayReadLRUState :: Monad m => CacheSize ->  Array -> Index -> StateT FullState m Val
cacheAwareArrayReadLRUState cacheSize arr ix = do
    σ@((globalσ,tlσ,i), cache, time) <- get
    let (val, cache', accessTime) = cacheAwareArrayReadLRU cacheSize arr ix σ
    put ((globalσ,tlσ,i), cache', time + accessTime)
    return val


cacheAwareWriteLRU :: CacheSize -> Var -> Val -> FullState -> FullState
cacheAwareWriteLRU cacheSize var val σ@((globalσ@(GlobalState { σv }), tlσ ,i), cache, time ) =  case var of
    Global      _ -> assert (      isCachable $ VarName var) $ let (     σv', cache', accessTime) = write      σv in ((globalσ{ σv = σv'}, tlσ , i), cache', time + accessTime)
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ let tlσ' = Map.insert var val tlσ in                  ((globalσ           , tlσ', i), cache , time + registerAccessTime )
    Register    _ -> assert (not $ isCachable $ VarName var) $ let tlσ' = Map.insert var val tlσ in                  ((globalσ           , tlσ', i), cache , time + registerAccessTime )
  where cvar = CachedVar var
        cval = CachedVal val
        write someσ = 
          require (consistent cacheSize σ) $
          case removeFirstOrButLastAssoc cacheSize cvar cache of
            Right cache0     -> (Map.insert var val someσ, (cvar, cval) : cache0, cacheWriteTime )
            Left (_, cache0) -> (Map.insert var val someσ, (cvar, cval) : cache0, cacheWriteTime )


cacheAwareWriteLRUState :: Monad m => CacheSize -> Var -> Val -> StateT FullState m ()
cacheAwareWriteLRUState cacheSize var val = do
    σ <- get
    put $ cacheAwareWriteLRU cacheSize var val σ
    return ()

cacheAwareArrayWriteLRU :: CacheSize -> Array -> Index -> Val -> FullState -> FullState
cacheAwareArrayWriteLRU cacheSize arr ix val σ@((globalσ@(GlobalState { σa }), tlσ ,i), cache, time ) = case arr of
    Array  _ -> assert (      isCachable $ ArrayName arr) $ let (     σa', cache', accessTime) = write      σa in ((globalσ{ σa = σa'}, tlσ , i), cache', time + accessTime)
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        cval = CachedArraySlice vals'
          where vals  = case Map.lookup arr σa of
                  Nothing -> initialCacheLine
                  Just av -> Map.elems $ sliceFor alignedIx av
                vals' = updateAt sliceIndex val vals
                 where sliceIndex = ix - alignedIx
        write :: Map Array ArrayVal -> (Map Array ArrayVal, CacheState, TimeState )
        write someσ = 
            require (consistent cacheSize σ) $
            case removeFirstOrButLastAssoc cacheSize carr cache of
              Right cache0     ->  (Map.alter update arr someσ, (carr, cval) : cache0, cacheWriteTime )
              Left (_, cache0) ->  (Map.alter update arr someσ, (carr, cval) : cache0, cacheWriteTime )
          where update (Nothing) = Just $ Map.insert ix val arrayEmpty
                update (Just av) = Just $ Map.insert ix val av 

cacheAwareArrayWriteLRUState :: Monad m => CacheSize -> Array -> Index -> Val -> StateT FullState m ()
cacheAwareArrayWriteLRUState cacheSize arr ix val = do
    σ <- get
    put $ cacheAwareArrayWriteLRU cacheSize arr ix val σ
    return ()


initialCacheState :: CacheState
initialCacheState = []

initialFullState :: FullState
initialFullState = ((globalEmpty, Map.empty, ()), initialCacheState, 0)

exampleSurvey1 :: FullState
exampleSurvey1 = ((GlobalState { σv = Map.fromList                $ [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4), (Global "x", 42)],
                                 σa = Map.empty },
                   Map.empty, ()),
                                   fmap wrapped                   $ [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4)],
                  0
                 )
  where wrapped (a,b) = (CachedVar a, CachedVal b)



cacheAwareLRUEvalB :: Monad m => CacheSize -> BoolFunction -> StateT FullState m Bool
cacheAwareLRUEvalB cacheSize CTrue     = return True
cacheAwareLRUEvalB cacheSize CFalse    = return False
cacheAwareLRUEvalB cacheSize (Leq x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal <= yVal
cacheAwareLRUEvalB cacheSize (Eeq x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal == yVal
cacheAwareLRUEvalB cacheSize (And b1 b2) = do
  b1Val <- cacheAwareLRUEvalB cacheSize b1
  b2Val <- cacheAwareLRUEvalB cacheSize b2
  return $ b1Val && b2Val
cacheAwareLRUEvalB cacheSize (Or b1 b2) = do
  b1Val <- cacheAwareLRUEvalB cacheSize b1
  b2Val <- cacheAwareLRUEvalB cacheSize b2
  return $ b1Val || b2Val
cacheAwareLRUEvalB cacheSize (Not b) = do
  bVal <- cacheAwareLRUEvalB cacheSize b
  return $ not bVal

cacheAwareLRUEvalV :: Monad m => CacheSize -> VarFunction -> StateT FullState m Val
cacheAwareLRUEvalV cacheSize (Val  x) = return x
cacheAwareLRUEvalV cacheSize (Var  x) = cacheAwareReadLRUState cacheSize x
cacheAwareLRUEvalV cacheSize (ArrayRead a ix) = do
  iVal <- cacheAwareLRUEvalV cacheSize ix
  cacheAwareArrayReadLRUState cacheSize a (arrayIndex iVal)
cacheAwareLRUEvalV cacheSize (Plus  x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal + yVal
cacheAwareLRUEvalV cacheSize (Minus x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal - yVal
cacheAwareLRUEvalV cacheSize (Times x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal * yVal
cacheAwareLRUEvalV cacheSize (Div x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal `div` yVal
cacheAwareLRUEvalV cacheSize (Mod x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal `mod` yVal
cacheAwareLRUEvalV cacheSize (Shl x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal `shiftL` (fromIntegral yVal)
cacheAwareLRUEvalV cacheSize (Shr x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal `shiftR` (fromIntegral yVal)
cacheAwareLRUEvalV cacheSize (Xor x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal `xor` yVal
cacheAwareLRUEvalV cacheSize (BAnd x y) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  yVal <- cacheAwareLRUEvalV cacheSize y
  return $ xVal .&. yVal
cacheAwareLRUEvalV cacheSize (Neg x) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  return $ - xVal
cacheAwareLRUEvalV cacheSize (BNot x) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  return $ complement $ xVal
cacheAwareLRUEvalV cacheSize (AssertRange min max x) = do
  xVal <- cacheAwareLRUEvalV cacheSize x
  return $   xVal

{-
instance MonadTrans (StateT s)
lift :: (Monad m, MonadTrans t) => m a -> t m a
lift (cacheAwareLRUevalB bf) :: StateT FullState (State FullState) Val
-}

cacheStepForState :: CacheSize -> CFGEdge -> StateT FullState [] (CFGEdge, FullState)
cacheStepForState cacheSize e@(Guard b bf) = do
        bVal <- cacheAwareLRUEvalB cacheSize bf
        σ@(normal, cache, time) <- get
        let σ' = (normal, cache, time + guardTime)
        if (b == bVal) then return (e,σ') else lift []
cacheStepForState cacheSize e@(Assign x vf) = do
        xVal <- cacheAwareLRUEvalV cacheSize vf
        cacheAwareWriteLRUState cacheSize x xVal
        σ' <- get
        return (e,σ')
cacheStepForState cacheSize e@(AssignArray a ix vf) = do
        vVal <- cacheAwareLRUEvalV cacheSize vf
        iVal <- cacheAwareLRUEvalV cacheSize ix
        cacheAwareArrayWriteLRUState cacheSize a (arrayIndex iVal) vVal
        σ' <- get
        return (e,σ')
cacheStepForState cacheSize e@(Init _ _) = do
        (normal@(σ, tlσ,()), cache, time) <- get
        let [(σ', tlσ', _)] = stepFor e (σ, tlσ, undefined)
        let normal' = (σ', tlσ', ())
        return (e, (normal', cache, time + initTime))
cacheStepForState cacheSize e@(InitArray _ _) = do
        (normal@(σ, tlσ,()), cache, time) <- get
        let [(σ', tlσ', _)] = stepFor e (σ, tlσ, undefined)
        let normal' = (σ', tlσ', ())
        return (e,(normal', cache, time + initTime))
cacheStepForState cacheSize e@NoOp = do
        σ@(normal,cache,time) <- get
        let σ' = (normal, cache, time + noOpTime)
        put σ'
        return (e,σ')
cacheStepForState cacheSize (Read  _ _) = undefined
cacheStepForState cacheSize (Print _ _) = undefined
cacheStepForState cacheSize (Spawn    ) = undefined
cacheStepForState cacheSize (Call     ) = undefined
cacheStepForState cacheSize (Return   ) = undefined

cacheStepFor ::  CacheSize -> AbstractSemantic FullState CFGEdge
cacheStepFor cacheSize e σ = evalStateT (cacheStepForState cacheSize e) σ


cacheExecutionGraph :: (Graph gr) => CacheSize -> gr CFGNode CFGEdge -> FullState -> Node -> gr (Node, FullState) CFGEdge
cacheExecutionGraph cacheSize = stateGraph (cacheStepFor cacheSize) Nothing


cacheExecution :: (Graph gr) => CacheSize -> gr CFGNode CFGEdge -> FullState -> Node -> [[(Node,TimeState)]]
cacheExecution cacheSize g σ0 n0 = run σ0 n0
  where run σ@(_,_,time) n = case try σ n of
                    [] -> [[(n, time)]]
                    ts -> ts
        try σ@(_,_,time) n = do
                    (n', e) <- lsuc g n
                    (_,σ') <- cacheStepFor cacheSize e σ
                    trace0 <- run σ' n'
                    return $ (n, time) : trace0


cacheExecutionLimit :: (Graph gr) => CacheSize -> Int -> gr CFGNode CFGEdge -> FullState -> Node -> [[(Node,TimeState)]]
cacheExecutionLimit cacheSize limit g σ0 n0 = run σ0 n0 0
  where run σ@(_,_,time) n i = if i >= limit then [] else case try σ n i of
                    [] -> [[(n, time)]]
                    ts -> ts
        try σ@(_,_,time) n i = do
                    (n', e) <- lsuc g n
                    (_,σ') <- cacheStepFor cacheSize e σ
                    trace0 <- run σ' n' (i+1)
                    return $ (n, time) : trace0


prependInitialization :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Node -> Map Name Node -> Map Var Val -> Map Array ArrayVal -> gr CFGNode CFGEdge
prependInitialization g0 n0 newN0 varToNode state stateA =
    g0 `mergeTwoGraphs` g1
  where g1 = mkGraph
               [(n,n) | n <- newN0 : Map.elems varToNode]
               (   [(newN0, if Map.null varToNode then n0 else snd $ head $ Map.assocs varToNode, NoOp)]
                ++ [ (n,n', Init      var (Just $ state  ! var)) | ((VarName   var,n),(_,n')) <- zip (Map.assocs varToNode) ((tail $ Map.assocs varToNode) ++ [(undefined,n0)]) ]
                ++ [ (n,n', InitArray arr (Just $ stateA ! arr)) | ((ArrayName arr,n),(_,n')) <- zip (Map.assocs varToNode) ((tail $ Map.assocs varToNode) ++ [(undefined,n0)]) ]
               )

prependFakeInitialization :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Node -> Map Name Node -> gr CFGNode CFGEdge
prependFakeInitialization g0 n0 newN0 varToNode =
    g0 `mergeTwoGraphs` g1
  where g1 = mkGraph
               [(n,n) | n <- newN0 : Map.elems varToNode]
               (   [(newN0, if Map.null varToNode then n0 else snd $ head $ Map.assocs varToNode, NoOp)]
                ++ [ (n,n', Init      var Nothing              ) | ((VarName   var,n),(_,n')) <- zip (Map.assocs varToNode) ((tail $ Map.assocs varToNode) ++ [(undefined,n0)]) ]
                ++ [ (n,n', InitArray arr Nothing              ) | ((ArrayName arr,n),(_,n')) <- zip (Map.assocs varToNode) ((tail $ Map.assocs varToNode) ++ [(undefined,n0)]) ]
               )

