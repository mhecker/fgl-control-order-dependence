{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
#define USE_PRECISE_ARRAY_CACHELINES
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
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt, focus, removeFirstOrButLastMaxSize)
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






-- max: 32, at cacheLineSize 128
-- max:  8, at cacheLineSize  64
cacheSize :: Int
cacheSize = 4

cacheSizeInBytes = cacheLineSize * cacheSize

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

removeFirstOrButLast = removeFirstOrButLastMaxSize cacheSize

undefinedCache = [ "_undef_" ++ (show i) | i <- [1..cacheSize]]
undefinedCacheValue = CachedVal (0-1)
undefinedCacheArrayValue = CachedArraySlice undefinedCacheLine


type ArrayBound = Val

data CachedObject
    = CachedVar Var 
    | CachedArrayRange Array ArrayBound -- contents of Array from [ArrayBound ..to.. ArrayBound+cacheLineSize]
    | CachedUnknownRange Array          -- In an abstract cache [, .. CacheUnknownRange a  ..] represents a cacheline within array a with  unknown range
  deriving (Show, Eq, Ord)

data CacheValue = CachedVal Val | CachedArraySlice [Val] deriving (Show, Eq, Ord)

cachedObjectsFor :: CFGEdge -> Set CachedObject
cachedObjectsFor = useE
  where 
    useE :: CFGEdge -> Set CachedObject
    useE = useEFor useV useB

    useB :: BoolFunction -> Set CachedObject
    useB = useBFor useV

    useV :: VarFunction -> Set CachedObject
    {- special case for constants -}
    useV (ArrayRead a ix@(Val i)) = Set.fromList [CachedArrayRange a (toAlignedIndex $ arrayIndex i) ]
    {- special case for assertions -}
    useV (ArrayRead a ix@(AssertRange min max i)) =
                                    Set.fromList [CachedArrayRange a           aligned | aligned <- alignedIndicesFor min max ]
    useV (ArrayRead a ix        ) = Set.fromList [CachedArrayRange a           aligned | aligned <- alignedIndices ]
                                  ∪ useV ix
    useV (Val  x)    = Set.empty
    useV (Var  x)    = Set.fromList [CachedVar x]
    useV (Plus  x y) = useV x ∪ useV y
    useV (Minus x y) = useV x ∪ useV y
    useV (Times x y) = useV x ∪ useV y
    useV (Div   x y) = useV x ∪ useV y
    useV (Mod   x y) = useV x ∪ useV y
    useV (BAnd  x y) = useV x ∪ useV y
    useV (Shl   x y) = useV x ∪ useV y
    useV (Shr   x y) = useV x ∪ useV y
    useV (Xor   x y) = useV x ∪ useV y
    useV (Neg x)     = useV x
    useV (BNot x)    = useV x
    useV (AssertRange _ _ x) = useV x

type CacheState = [(CachedObject, CacheValue)]

type CacheTimeState = (CacheState, TimeState)
type FullState = (NormalState, CacheState, TimeState)


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


consistent :: FullState -> Bool
consistent ((GlobalState { σv, σa }, tlσ, i), cache, _) = length cache <= cacheSize && (∀) (cache) cons
  where cons (CachedVar        var@(Global      x)      , CachedVal        val ) = val ==      σv ! var
        cons (CachedVar        var@(ThreadLocal x)      , CachedVal        val ) = val ==     tlσ ! var
        cons (CachedArrayRange arr@(Array       a) index, CachedArraySlice vals) = 
            (length vals == cacheLineSize) ∧ (index >= 0) ∧ (index `mod` cacheLineSizeVal == 0) ∧ (index <= arrayMaxIndex)
          ∧ (Map.size betw == cacheLineSize)
          ∧ (∀) (zipWith (==) vals (Map.elems betw)) id
          where betw :: ArrayVal
                betw = sliceFor index (σa ! arr)

sameArrayAs a (CachedArrayRange   a' _ ) = a' == a
sameArrayAs a (CachedUnknownRange a'   ) = a' == a
sameArrayAs _ _                          = False


cacheAwareReadLRU :: Var -> FullState -> (Val, CacheState, AccessTime)
cacheAwareReadLRU var σ@((GlobalState { σv }, tlσ, i), cache, _) = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ lookup     σv
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ (tlσ ! var, cache, registerAccessTime)
    Register    _ -> assert (not $ isCachable $ VarName var) $ (tlσ ! var, cache, registerAccessTime)
  where cvar = CachedVar var

        lookup :: Map Var Val -> (Val, CacheState, AccessTime )
        lookup someσ = 
          require (consistent σ) $
          case removeFirstOrButLast cvar cache of
            Right cache0 -> let { cval = CachedVal val ; val = someσ ! var } in
              (val, (cvar, cval) : cache0, cacheMissTime )
            Left (cval@(CachedVal val), cache0) ->
              (val, (cvar, cval) : cache0, cacheHitTime  )


cacheTimeReadLRU :: Var -> CacheState -> (CacheState, AccessTime)
cacheTimeReadLRU var cache = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ lookup
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime)
    Register    _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime)
  where cvar = CachedVar var
        lookup =
          case removeFirstOrButLast cvar cache of
            Right                       cache0  ->
              ( (cvar, undefinedCacheValue) : cache0, cacheMissTime)
            Left (cval@(CachedVal val), cache0) -> assert (cval == undefinedCacheValue) $
              ( (cvar, undefinedCacheValue) : cache0, cacheHitTime )


type Index = Val

cacheAwareArrayReadLRU :: Array -> Index -> FullState -> (Val, CacheState, AccessTime)
cacheAwareArrayReadLRU arr ix σ@((GlobalState { σa }, tlσ, _), cache, _) = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ lookup
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        lookup :: (Val, CacheState, AccessTime )
        lookup = 
          require (consistent σ) $
          assert (alignedIx <= ix) $
          case removeFirstOrButLast carr cache of
            Right                               cache0 -> let { cval = CachedArraySlice vals ; vals = Map.elems $ sliceFor alignedIx (σa ! arr) } in
              (vals !! (fromIntegral $ ix - alignedIx), (carr, cval) : cache0, cacheMissTime )
            Left (cval@(CachedArraySlice vals), cache0)->
              (vals !! (fromIntegral $ ix - alignedIx), (carr, cval) : cache0, cacheHitTime  )


unknownranges arr cache carr hitTime missTime =
    require (isArray carr) $ incache ++ notincache
  where isArray (CachedArrayRange _ _) = True
        isArray (CachedUnknownRange _) = True
        isArray _ = False
        
        incache = do
              (left, (carr', cval), right) <- focus (mayMatch carr . fst) cache
              return $ assert (cval == undefinedCacheArrayValue) $
                ( (carr', undefinedCacheArrayValue) : ( left ++ right            ), hitTime)
        notincache 
            | length carrs < nrOfDifferentCacheLinesPerArray =
               [( (carr , undefinedCacheArrayValue) : (take (cacheSize - 1) cache), missTime)]
            | otherwise = []
        carrs = [ carr' | (carr'                         , _) <- cache, sameArray carr']
        sameArray = sameArrayAs arr

        mayMatch _                      (CachedVar _) = False
        mayMatch x@(CachedVar _)          _             = error $ "called with carr == " ++ (show x)
        mayMatch (CachedArrayRange a i) (CachedArrayRange a' i') =
            require (toAlignedIndex i == i   ∧  toAlignedIndex i' == i')
          $ a == a' ∧ i == i'
        mayMatch (CachedArrayRange a _) (CachedUnknownRange a') =
            a == a'
        mayMatch (CachedUnknownRange a) (CachedArrayRange a' _) =
            a == a'
        mayMatch (CachedUnknownRange a) (CachedUnknownRange a') =
            a == a'

cacheTimeArrayReadLRU :: Array -> Index -> CacheState -> [(CacheState, AccessTime)]
cacheTimeArrayReadLRU arr ix cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ lookup
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        lookup = 
          case removeFirstOrButLast carr cache of
            Right _ ->
              unknownranges arr cache carr cacheHitTime cacheMissTime
            Left (cval, cache0) -> assert (cval == undefinedCacheArrayValue) $
              [( (carr, undefinedCacheArrayValue) : cache0, cacheHitTime)]

cacheTimeArrayReadUnknownIndexLRU :: Array -> CacheState -> [(CacheState, AccessTime)]
cacheTimeArrayReadUnknownIndexLRU arr cache = case arr of
    Array       a -> assert (      isCachable $ ArrayName arr) $ lookup
  where lookup = unknownranges arr cache carr cacheHitTime cacheMissTime
        carr  = CachedUnknownRange arr



cacheAwareReadLRUState :: Monad m => Var -> StateT FullState m Val
cacheAwareReadLRUState var = do
    σ@((globalσ,tlσ,i), cache, time) <- get
    let (val, cache', accessTime) = cacheAwareReadLRU var σ
    put ((globalσ,tlσ,i), cache', time + accessTime)
    return val

cacheTimeReadLRUState :: Monad m => Var -> StateT CacheTimeState m ()
cacheTimeReadLRUState var = do
    (cache, time) <- get
    let (cache', accessTime) = cacheTimeReadLRU var cache
    put (cache', time + accessTime)
    return ()


cacheTimeWriteLRU :: Var -> CacheState -> (CacheState, AccessTime)
cacheTimeWriteLRU var cache = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ write
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime )
    Register    _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime )
  where cvar = CachedVar var
        write = 
          case removeFirstOrButLast cvar cache of
            Right cache0      -> ( (cvar, undefinedCacheValue) : cache0, cacheWriteTime )
            Left  (_, cache0) -> ( (cvar, undefinedCacheValue) : cache0, cacheWriteTime )


cacheTimeWriteLRUState :: Monad m => Var -> StateT CacheTimeState m ()
cacheTimeWriteLRUState var = do
    (cache, time) <- get
    let (cache', accessTime) = cacheTimeWriteLRU var cache
    put (cache', time + accessTime)
    return ()


cacheAwareArrayReadLRUState :: Monad m => Array -> Index -> StateT FullState m Val
cacheAwareArrayReadLRUState arr ix = do
    σ@((globalσ,tlσ,i), cache, time) <- get
    let (val, cache', accessTime) = cacheAwareArrayReadLRU arr ix σ
    put ((globalσ,tlσ,i), cache', time + accessTime)
    return val

cacheTimeArrayReadLRUState :: Array -> Index -> StateT CacheTimeState [] ()
cacheTimeArrayReadLRUState arr ix = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayReadLRU arr ix cache
    put (cache', time + accessTime)
    return ()
    
cacheTimeArrayReadUnknownIndexLRUState :: Array -> StateT CacheTimeState [] ()
cacheTimeArrayReadUnknownIndexLRUState arr = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayReadUnknownIndexLRU arr cache
    put (cache', time + accessTime)
    return ()



cacheTimeArrayWriteLRU :: Array -> Index -> CacheState -> [(CacheState, AccessTime)]
cacheTimeArrayWriteLRU arr ix cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ write
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        write = 
          case removeFirstOrButLast carr cache of
            Right _ ->  unknownranges arr cache carr cacheWriteTime cacheWriteTime
            Left (_, cache0) ->  [( (carr, undefinedCacheArrayValue) : cache0, cacheWriteTime )]


cacheTimeArrayWriteUnknownIndexLRU :: Array -> CacheState -> [(CacheState, AccessTime)]
cacheTimeArrayWriteUnknownIndexLRU arr cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ write
  where write = unknownranges arr cache carr cacheWriteTime cacheWriteTime
        carr  = CachedUnknownRange arr



cacheTimeArrayWriteLRUState :: Array -> Index -> StateT CacheTimeState [] ()
cacheTimeArrayWriteLRUState arr ix = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayWriteLRU arr ix cache
    put (cache', time + accessTime)
    return ()

cacheTimeArrayWriteUnknownIndexLRUState :: Array -> StateT CacheTimeState [] ()
cacheTimeArrayWriteUnknownIndexLRUState arr = do
    (cache, time) <- get
    (cache', accessTime) <- lift $ cacheTimeArrayWriteUnknownIndexLRU arr cache
    put (cache', time + accessTime)
    return ()


cacheAwareWriteLRU :: Var -> Val -> FullState -> FullState
cacheAwareWriteLRU var val σ@((globalσ@(GlobalState { σv }), tlσ ,i), cache, time ) =  case var of
    Global      _ -> assert (      isCachable $ VarName var) $ let (     σv', cache', accessTime) = write      σv in ((globalσ{ σv = σv'}, tlσ , i), cache', time + accessTime)
    ThreadLocal _ -> assert (not $ isCachable $ VarName var) $ let tlσ' = Map.insert var val tlσ in                  ((globalσ           , tlσ', i), cache , time + registerAccessTime )
    Register    _ -> assert (not $ isCachable $ VarName var) $ let tlσ' = Map.insert var val tlσ in                  ((globalσ           , tlσ', i), cache , time + registerAccessTime )
  where cvar = CachedVar var
        cval = CachedVal val
        write someσ = 
          require (consistent σ) $
          case removeFirstOrButLast cvar cache of
            Right cache0     -> (Map.insert var val someσ, (cvar, cval) : cache0, cacheWriteTime )
            Left (_, cache0) -> (Map.insert var val someσ, (cvar, cval) : cache0, cacheWriteTime )


cacheAwareWriteLRUState :: Monad m => Var -> Val -> StateT FullState m ()
cacheAwareWriteLRUState var val = do
    σ <- get
    put $ cacheAwareWriteLRU var val σ
    return ()

cacheAwareArrayWriteLRU :: Array -> Index -> Val -> FullState -> FullState
cacheAwareArrayWriteLRU arr ix val σ@((globalσ@(GlobalState { σa }), tlσ ,i), cache, time ) = case arr of
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
            require (consistent σ) $
            case removeFirstOrButLast carr cache of
              Right cache0     ->  (Map.alter update arr someσ, (carr, cval) : cache0, cacheWriteTime )
              Left (_, cache0) ->  (Map.alter update arr someσ, (carr, cval) : cache0, cacheWriteTime )
          where update (Nothing) = Just $ Map.insert ix val arrayEmpty
                update (Just av) = Just $ Map.insert ix val av 
          
cacheAwareArrayWriteLRUState :: Monad m => Array -> Index -> Val -> StateT FullState m ()
cacheAwareArrayWriteLRUState arr ix val = do
    σ <- get
    put $ cacheAwareArrayWriteLRU arr ix val σ
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



cacheAwareLRUEvalB :: Monad m => BoolFunction -> StateT FullState m Bool
cacheAwareLRUEvalB CTrue     = return True
cacheAwareLRUEvalB CFalse    = return False
cacheAwareLRUEvalB (Leq x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal <= yVal
cacheAwareLRUEvalB (Eeq x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal == yVal
cacheAwareLRUEvalB (And b1 b2) = do
  b1Val <- cacheAwareLRUEvalB b1
  b2Val <- cacheAwareLRUEvalB b2
  return $ b1Val && b2Val
cacheAwareLRUEvalB (Or b1 b2) = do
  b1Val <- cacheAwareLRUEvalB b1
  b2Val <- cacheAwareLRUEvalB b2
  return $ b1Val || b2Val
cacheAwareLRUEvalB (Not b) = do
  bVal <- cacheAwareLRUEvalB b
  return $ not bVal

cacheAwareLRUEvalV :: Monad m => VarFunction -> StateT FullState m Val
cacheAwareLRUEvalV (Val  x) = return x
cacheAwareLRUEvalV (Var  x) = cacheAwareReadLRUState x
cacheAwareLRUEvalV (ArrayRead a ix) = do
  iVal <- cacheAwareLRUEvalV ix
  cacheAwareArrayReadLRUState a (arrayIndex iVal)
cacheAwareLRUEvalV (Plus  x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal + yVal
cacheAwareLRUEvalV (Minus x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal - yVal
cacheAwareLRUEvalV (Times x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal * yVal
cacheAwareLRUEvalV (Div x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal `div` yVal
cacheAwareLRUEvalV (Mod x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal `mod` yVal
cacheAwareLRUEvalV (Shl x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal `shiftL` (fromIntegral yVal)
cacheAwareLRUEvalV (Shr x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal `shiftR` (fromIntegral yVal)
cacheAwareLRUEvalV (Xor x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal `xor` yVal
cacheAwareLRUEvalV (BAnd x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal .&. yVal
cacheAwareLRUEvalV (Neg x) = do
  xVal <- cacheAwareLRUEvalV x
  return $ - xVal
cacheAwareLRUEvalV (BNot x) = do
  xVal <- cacheAwareLRUEvalV x
  return $ complement $ xVal
cacheAwareLRUEvalV (AssertRange min max x) = do
  xVal <- cacheAwareLRUEvalV x
  return $   xVal

{-
instance MonadTrans (StateT s)
lift :: (Monad m, MonadTrans t) => m a -> t m a
lift (cacheAwareLRUevalB bf) :: StateT FullState (State FullState) Val
-}

cacheStepForState :: CFGEdge -> StateT FullState [] FullState
cacheStepForState (Guard b bf) = do
        bVal <- cacheAwareLRUEvalB bf
        σ@(normal, cache, time) <- get
        let σ' = (normal, cache, time + guardTime)
        if (b == bVal) then return σ' else lift []
cacheStepForState (Assign x vf) = do
        xVal <- cacheAwareLRUEvalV vf
        cacheAwareWriteLRUState x xVal
        σ' <- get
        return σ'
cacheStepForState (AssignArray a ix vf) = do
        vVal <- cacheAwareLRUEvalV vf
        iVal <- cacheAwareLRUEvalV ix
        cacheAwareArrayWriteLRUState a (arrayIndex iVal) vVal
        σ' <- get
        return σ'
cacheStepForState e@(Init _ _) = do
        (normal@(σ, tlσ,()), cache, time) <- get
        let [(σ', tlσ', _)] = stepFor e (σ, tlσ, undefined)
        let normal' = (σ', tlσ', ())
        return (normal', cache, time + initTime)
cacheStepForState e@(InitArray _ _) = do
        (normal@(σ, tlσ,()), cache, time) <- get
        let [(σ', tlσ', _)] = stepFor e (σ, tlσ, undefined)
        let normal' = (σ', tlσ', ())
        return (normal', cache, time + initTime)
cacheStepForState NoOp = do
        σ@(normal,cache,time) <- get
        let σ' = (normal, cache, time + noOpTime)
        put σ'
        return σ'
cacheStepForState (Read  _ _) = undefined
cacheStepForState (Print _ _) = undefined
cacheStepForState (Spawn    ) = undefined
cacheStepForState (Call     ) = undefined
cacheStepForState (Return   ) = undefined

cacheStepFor ::  AbstractSemantic FullState
cacheStepFor e σ = evalStateT (cacheStepForState e) σ




cacheTimeLRUEvalB :: BoolFunction -> StateT CacheTimeState [] ()
cacheTimeLRUEvalB CTrue     = return ()
cacheTimeLRUEvalB CFalse    = return ()
cacheTimeLRUEvalB (Leq x y) = do
  xVal <- cacheTimeLRUEvalV x
  yVal <- cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalB (Eeq x y) = do
  xVal <- cacheTimeLRUEvalV x
  yVal <- cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalB (And b1 b2) = do
  b1Val <- cacheTimeLRUEvalB b1
  b2Val <- cacheTimeLRUEvalB b2
  return ()
cacheTimeLRUEvalB (Or b1 b2) = do
  b1Val <- cacheTimeLRUEvalB b1
  b2Val <- cacheTimeLRUEvalB b2
  return ()
cacheTimeLRUEvalB (Not b) = do
  bVal <- cacheTimeLRUEvalB b
  return ()

cacheTimeLRUEvalV :: VarFunction -> StateT CacheTimeState [] ()
cacheTimeLRUEvalV (Val  x) = return ()
cacheTimeLRUEvalV (Var  x) = cacheTimeReadLRUState x
{- special case for constants -}
cacheTimeLRUEvalV (ArrayRead a ix@(Val i)) = do
  cacheTimeLRUEvalV ix -- does nothing
  cacheTimeArrayReadLRUState a (arrayIndex i)
  return ()
{- special case for assertions -}
cacheTimeLRUEvalV (ArrayRead a ix@(AssertRange min max i)) = do
  cacheTimeLRUEvalV i
  i <- lift $ alignedIndicesFor min max
  cacheTimeArrayReadLRUState a (arrayIndex i)
  return ()
#ifdef USE_PRECISE_ARRAY_CACHELINES
cacheTimeLRUEvalV (ArrayRead a ix) = do
  cacheTimeLRUEvalV ix
  i <- lift alignedIndices
  cacheTimeArrayReadLRUState a i
  return ()
#else
cacheTimeLRUEvalV (ArrayRead a ix) = do
  cacheTimeLRUEvalV ix
  cacheTimeArrayReadUnknownIndexLRUState a
  return ()
#endif
cacheTimeLRUEvalV (Plus  x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Minus x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Times x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Div x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Mod x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Xor x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Shl   x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Shr   x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (BAnd  x y) = do
  cacheTimeLRUEvalV x
  cacheTimeLRUEvalV y
  return ()
cacheTimeLRUEvalV (Neg x) = do
  cacheTimeLRUEvalV x
  return ()
cacheTimeLRUEvalV (BNot x) = do
  cacheTimeLRUEvalV x
  return ()
cacheTimeLRUEvalV (AssertRange min max x) = do
  cacheTimeLRUEvalV x
  return ()







cacheTimeStepForState :: CFGEdge -> StateT CacheTimeState [] CacheTimeState
cacheTimeStepForState (Guard b bf) = do
        cacheTimeLRUEvalB bf
        (cache, time) <- get
        return (cache, time + guardTime)
cacheTimeStepForState (Assign x vf) = do
        cacheTimeLRUEvalV vf
        cacheTimeWriteLRUState x
        σ' <- get
        return σ'
{- special case for constants -}
cacheTimeStepForState (AssignArray a ix@(Val i) vf) = do
        cacheTimeLRUEvalV vf
        cacheTimeLRUEvalV ix -- does nothing
        cacheTimeArrayWriteLRUState a (arrayIndex i)
        σ' <- get
        return σ'
{- special case for assertions -}
cacheTimeStepForState (AssignArray a ix@((AssertRange min max i)) vf) = do
        cacheTimeLRUEvalV vf
        cacheTimeLRUEvalV i
        i <- lift $ alignedIndicesFor min max
        cacheTimeArrayWriteLRUState a (arrayIndex i)
        σ' <- get
        return σ'
#ifdef USE_PRECISE_ARRAY_CACHELINES
cacheTimeStepForState (AssignArray a ix vf) = do
        cacheTimeLRUEvalV vf
        cacheTimeLRUEvalV ix
        i <- lift alignedIndices
        cacheTimeArrayWriteLRUState a i
        σ' <- get
        return σ'
#else
cacheTimeStepForState (AssignArray a ix vf) = do
        cacheTimeLRUEvalV vf
        cacheTimeLRUEvalV ix
        cacheTimeArrayWriteUnknownIndexLRUState a
        σ' <- get
        return σ'
#endif
cacheTimeStepForState (Init _ _ ) = do
        (cache, time) <- get
        return (cache, time + initTime) 
cacheTimeStepForState (InitArray _ _ ) = do
        (cache, time) <- get
        return (cache, time + initTime) 
cacheTimeStepForState NoOp = do
        (cache, time) <- get
        return (cache, time + noOpTime) 
cacheTimeStepForState (Read  _ _) = undefined
cacheTimeStepForState (Print _ _) = undefined
cacheTimeStepForState (Spawn    ) = undefined
cacheTimeStepForState (Call     ) = undefined
cacheTimeStepForState (Return   ) = undefined

cacheTimeStepFor ::  AbstractSemantic CacheTimeState
cacheTimeStepFor e σ = evalStateT (cacheTimeStepForState e) σ

cacheOnlyStepFor ::  AbstractSemantic CacheState
cacheOnlyStepFor e σ = fmap fst $ evalStateT (cacheTimeStepForState e) (σ, 0)



cacheStateGraph'ForVarsAtMForGraph2 :: forall gr. (DynGraph gr) => Set CachedObject -> (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) ->  Node -> gr (Node, MergedCacheState) CFGEdge
cacheStateGraph'ForVarsAtMForGraph2 vars (css, es) mm = result
  where result = subgraph (rdfs [ m | (m, (m',_)) <- labNodes merged, m' == mm ] merged) merged

        merged :: gr (Node, MergedCacheState) CFGEdge
        merged = mkGraph nodes' edges'

        nodes' = zip [0..] [           α cs                      |  cs@(m,c)                  <- Set.toList css]
        edges' =           [(toNode' ! α cs, toNode' ! α cs', e) | (cs@(m,c), e, cs'@(m',c')) <- Set.toList es, m /= mm]
        toNode' = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes'

        α cs@(n, cache)
          | n == mm   = (mm, Merged $ Set.fromList [ v | (v,s) <- cache, v ∈ vars])
          | otherwise = (n,  Unmerged cache)






cacheExecutionGraph :: (Graph gr) => gr CFGNode CFGEdge -> FullState -> Node -> gr (Node, FullState) CFGEdge
cacheExecutionGraph = stateGraph cacheStepFor


cacheStateGraph :: (Graph gr) => gr CFGNode CFGEdge -> CacheState -> Node -> gr (Node, CacheState) CFGEdge
cacheStateGraph = stateGraph cacheOnlyStepFor


cacheExecution :: (Graph gr) => gr CFGNode CFGEdge -> FullState -> Node -> [[(Node,TimeState)]]
cacheExecution g σ0 n0 = run σ0 n0
  where run σ@(_,_,time) n = case try σ n of
                    [] -> [[(n, time)]]
                    ts -> ts
        try σ@(_,_,time) n = do
                    (n', e) <- lsuc g n
                    σ' <- cacheStepFor e σ
                    trace0 <- run σ' n'
                    return $ (n, time) : trace0


cacheExecutionLimit :: (Graph gr) => Int -> gr CFGNode CFGEdge -> FullState -> Node -> [[(Node,TimeState)]]
cacheExecutionLimit limit g σ0 n0 = run σ0 n0 0
  where run σ@(_,_,time) n i = if i >= limit then [] else case try σ n i of
                    [] -> [[(n, time)]]
                    ts -> ts
        try σ@(_,_,time) n i = do
                    (n', e) <- lsuc g n
                    σ' <- cacheStepFor e σ
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



costsFor :: DynGraph gr =>  gr (Node, CacheState) CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor csGraph  =  (∐) [ Map.fromList [ ((n0, m0, e), Set.fromList [time]) ]  |
                                                 (n, (n0,cs)) <- labNodes csGraph,
                                                 (m, e) <- lsuc csGraph n,
                                                 let Just (m0,_) = lab csGraph m,
                                                 fullState'@(_,time) <- cacheTimeStepFor e (cs, 0)
                      ]

costsFor2 :: (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor2 (css, es)  =  (∐) [ Map.fromList [ ((n, n', e), Set.fromList [time]) ]  |
                                                 ((n,cache), e, (n', cache')) <- Set.toList es,
                                                 fullState'@(_,time) <- cacheTimeStepFor e (cache, 0)
                      ]


cacheCostDecisionGraphFor :: DynGraph gr => gr CFGNode CFGEdge -> gr (Node, CacheState) CFGEdge -> (gr CFGNode CFGEdge, Map (Node, Node) Integer)
cacheCostDecisionGraphFor g csGraph = (
      mkGraph
        ((labNodes g) ++ [(nNew, n) | (nNew, n) <-  [ (m', n) | ((e@(n,_,_),_), m') <- Map.assocs nodesFor  ]
                                                 ++ [ (mj, n) | ( e@(n,_,_)   , mj) <- Map.assocs joinFor   ]
                                                 ++ [ (mj, n) | ( e@(n,_,_)   , mj) <- Map.assocs linJoinFor]
                         ])
        (irrelevant ++ [ (n , m', l'  ) | ((e@(n,_,l),_), m') <- Map.assocs nodesFor, let l' = Use $ isDataDependent l ]
                    ++ [ (m', mj, NoOp) | ((e@(_,_,l),_), m') <- Map.assocs nodesFor,                          let mj = joinFor ! e ]
                    ++ [ (mj,  m, l   ) |   e@(_,m,l)         <- relevant,                                     let mj = joinFor ! e ]
                    ++ [ (n , m', l'  ) | ((e@(n,_,l),_), m') <- Map.assocs linNodesFor, let l' = Use $ isDataDependent l ]
                    ++ [ (m', m , l   ) |   e@(_,m,l)         <- linRelevant,                                  let m' = linJoinFor ! e ]
        ),
                  Map.fromList [ ((n ,m ), cost    ) | e@(n,m,l) <- irrelevant, let [cost] = Set.toList $ costs ! e,           assert (cost > 0) True ]
      `Map.union` Map.fromList [ ((n ,m'), cost - 2) | ((e@(n,_,l),cost), m') <- Map.assocs nodesFor,                          assert (cost > 2) True ]
      `Map.union` Map.fromList [ ((m',mj),        1) | ((e@(_,_,l),   _), m') <- Map.assocs nodesFor,                          let mj = joinFor ! e ]
      `Map.union` Map.fromList [ ((mj,m ),        1) |   e@(_,m,l)            <- relevant,                                     let mj = joinFor ! e ]
      `Map.union` Map.fromList [ ((n ,m'), cost - 1) | ((e@(n,_,l),cost), m') <- Map.assocs linNodesFor,                       assert (cost > 1) True ]
      `Map.union` Map.fromList [ ((m',m ),        1) |   e@(_,m,l)            <- linRelevant,                                  let m' = linJoinFor ! e ]
    )
  where
        costs = costsFor csGraph

        isRelevant e = nrSuc e > 1
        nrSuc e = Set.size $ costs ! e

        isLinRelevant e@(n,m,l) =
            (nrSuc e == 1) ∧ (not $ List.null $ isDataDependent l) ∧ (length (suc g n) == 1 )

        isDataDependent = isDep
          where isDep l@(AssignArray a (Val _) vf ) = isDataDepV vf
                isDep l@(AssignArray a ix      vf ) = isDataDepV vf ++ [ name | name <- Set.toList $ useV ix ]
                isDep l                             = isDataDepE l

                arrayReadsV a@(ArrayRead _ _) = Set.singleton a
                arrayReadsV   (Val  x)    = Set.empty
                arrayReadsV   (Var  x)    = Set.empty
                arrayReadsV   (Plus  x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Minus x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Times x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Div   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Mod   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Shl   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Shr   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Xor   x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (BAnd  x y) = arrayReadsV x ∪ arrayReadsV y
                arrayReadsV   (Neg x)     = arrayReadsV x
                arrayReadsV   (BNot x)    = arrayReadsV x
                arrayReadsV   (AssertRange min max x) = arrayReadsV x

                arrayReadsB = useBFor arrayReadsV
                arrayReadsE = useEFor arrayReadsV arrayReadsB


                isDataDepV vf = [ name | r@(ArrayRead a ix) <- Set.toList $ arrayReadsV vf, case ix of { Val _ -> False ; _ -> True }, name <- Set.toList $ useV ix ]
{- unused
                isDataDepB bf = not $ List.null $ [ r | r@(ArrayRead a ix) <- Set.toList $ arrayReadsB bf, case ix of { Val _ -> False ; _ -> True } ]
-}
                isDataDepE l  = [ name | r@(ArrayRead a ix) <- Set.toList $ arrayReadsE  l, case ix of { Val _ -> False ; _ -> True }, name <- Set.toList $ useV ix ]

        nodesFor =               Map.fromList $ zip [ (e,time) | e <-   relevant, time <- Set.toList $ costs ! e ] nodesNew
        joinFor  =               Map.fromList $ zip                     relevant                                    joinNew

        linNodesFor =            Map.fromList $ zip [ (e,time) | e <-linRelevant, time <- Set.toList $ costs ! e ]  linNew
        linJoinFor  =            Map.fromList $ zip                  linRelevant                                    linNew

        relevant   = [ e | e <- labEdges g,       isRelevant e   , assert (not $ isLinRelevant e) True]
        linRelevant= [ e | e <- labEdges g,       isLinRelevant e, assert (not $ isRelevant    e) True]
        irrelevant = [ e | e <- labEdges g, not $ isRelevant e ∨ isLinRelevant e]
        totalnewSplit = sum $ fmap nrSuc relevant
        totalnewJoin  = length relevant
        totalnewLin   = length linRelevant
        (nodesNew, joinNew, linNew) = (left, mid, right)
          where all = newNodes (totalnewSplit + totalnewJoin + totalnewLin) g
                (tmp, right) = splitAt (totalnewSplit + totalnewJoin) all
                (left,  mid) = splitAt  totalnewSplit                 tmp

cacheCostDecisionGraph :: DynGraph gr => gr CFGNode CFGEdge -> Node -> (gr CFGNode CFGEdge, Map (Node, Node) Integer)
cacheCostDecisionGraph g n0 = cacheCostDecisionGraphFor g csGraph
  where csGraph = cacheStateGraph g initialCacheState n0
        


type AbstractCacheStateTimeEquiv = Set CachedObject
type MergedCacheState = MergedMicroState CacheState AbstractCacheStateTimeEquiv

cacheAbstraction :: MicroArchitecturalAbstraction CacheState AbstractCacheStateTimeEquiv 
cacheAbstraction = MicroArchitecturalAbstraction { 
      muGraph'For = muGraph'For,
      muInitialState = initialCacheState,
      muStepFor = cacheOnlyStepFor,
      muCostsFor = costsFor2
    }
  where muGraph'For graph csGraph m = [ cacheStateGraph'ForVarsAtMForGraph2 vars csGraph m |  vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars] ]

csdMergeDirectOf :: forall gr a a'. (DynGraph gr) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf = muMergeDirectOf cacheAbstraction

csdGraphFromMergeDirectFor :: forall gr a a'. (DynGraph gr) =>
  gr CFGNode CFGEdge ->
  Node ->
  Node ->
  gr (Node, Set AbstractMicroArchitecturalGraphNode) CFGEdge
csdGraphFromMergeDirectFor = muGraphFromMergeDirectFor cacheAbstraction




