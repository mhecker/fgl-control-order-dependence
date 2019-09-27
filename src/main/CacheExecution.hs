{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#define require assert
module CacheExecution where

import Data.Map.Ordered (OMap, (<|), (|<), (>|), (|>), (<>|), (|<>))
import qualified Data.Map.Ordered as OMap

import qualified Data.List as List

import Data.Bits (xor, (.&.), shiftL, shiftR)

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
import Util (moreSeeds, restrict, invert'', maxFromTreeM, fromSet, updateAt)
import           IRLSOD (CFGNode, CFGEdge(..), GlobalState(..), globalEmpty, ThreadLocalState, Var(..), isGlobal, Array(..), arrayIndex, isArrayIndex, arrayMaxIndex, arrayEmpty, ArrayVal, Val, BoolFunction(..), VarFunction(..), Name(..), useE, defE, useEFor, useBFor, useB, useV, use, def, SimpleShow (..))
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




cacheLineSize :: Int
cacheLineSize = assert ((arrayMaxIndex + 1) `mod` n == 0) n
  where n = 64

initialCacheLine   = [  0 | i <- [0 .. cacheLineSize - 1] ]
undefinedCacheLine = [ -1 | i <- [0 .. cacheLineSize - 1] ]

toAlignedIndex i = require (isArrayIndex i) $ (i `div` cacheLineSize) * cacheLineSize

alignedIndices = [ cacheLineSize * (i-1) | i <- [1 ..  (arrayMaxIndex + 1) `div` cacheLineSize ]]

between :: Ord k => Map k v -> k -> k -> Map k v
between map n m = require (n <= m) $ 
                  let (_, right) = Map.split n map
                      (mid, _)   = Map.split m right
                  in mid

sliceFor :: Index -> ArrayVal -> ArrayVal
sliceFor ix array = between array (left - 1) (right + 1)
  where left  = toAlignedIndex ix
        right = left + cacheLineSize - 1






cacheSize = 4

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


undefinedCache = [ "_undef_" ++ (show i) | i <- [1..cacheSize]]
undefinedCacheValue = CachedVal (-1)
undefinedCacheArrayValue = CachedArraySlice undefinedCacheLine

type ConcreteSemantic a = CFGEdge -> a -> Maybe a

type AbstractSemantic a = CFGEdge -> a -> [a]

type NormalState = (GlobalState,ThreadLocalState, ())


type ArrayBound = Int

data CachedObject
    = CachedVar Var 
    | CachedArrayRange Array ArrayBound -- contents of Array from [ArrayBound ..to.. ArrayBound+cacheLineSize]
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
    useV (ArrayRead a ix        ) = Set.fromList [CachedArrayRange a           aligned | aligned <- alignedIndices ]
                                  ∪ useV ix
    useV (Val  x)    = Set.empty
    useV (Var  x)    = Set.fromList [CachedVar x]
    useV (Plus  x y) = useV x ∪ useV y
    useV (Times x y) = useV x ∪ useV y
    useV (Div   x y) = useV x ∪ useV y
    useV (Mod   x y) = useV x ∪ useV y
    useV (BAnd  x y) = useV x ∪ useV y
    useV (Shl   x y) = useV x ∪ useV y
    useV (Shr   x y) = useV x ∪ useV y
    useV (Xor   x y) = useV x ∪ useV y
    useV (Neg x)     = useV x

type CacheState = OMap CachedObject CacheValue
type AbstractCacheState = ([(CachedObject, OMap.Index)], Set CachedObject)

type TimeState = Integer


type CacheTimeState = (CacheState, TimeState)
type FullState = (NormalState, CacheState, TimeState)


instance SimpleShow CachedObject where
  simpleShow (CachedVar        var)  = simpleShow var
  simpleShow (CachedArrayRange (Array x) i) = x ++ "[" ++ (show i) ++ ".." ++ (show $ i + cacheLineSize -1) ++ "]"

instance SimpleShow CacheValue where
  simpleShow (CachedVal        val ) = simpleShow val
  simpleShow (CachedArraySlice vals) = simpleShow vals


instance SimpleShow CacheState where
  simpleShow cs = simpleShow $ fmap fst $ OMap.assocs cs


isCachable :: Name -> Bool
isCachable (VarName (Global _)) = True
isCachable (VarName (ThreadLocal _)) = True -- maybe we dont want this?
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


consistent :: FullState -> Bool
consistent ((GlobalState { σv, σa }, tlσ, i), cache, _) = OMap.size cache <= cacheSize && (∀) (OMap.assocs cache) cons
  where cons (CachedVar        var@(Global      x)      , CachedVal        val ) = val ==      σv ! var
        cons (CachedVar        var@(ThreadLocal x)      , CachedVal        val ) = val ==     tlσ ! var
        cons (CachedArrayRange arr@(Array       a) index, CachedArraySlice vals) = 
            (length vals == cacheLineSize) ∧ (index >= 0) ∧ (index `mod` cacheLineSize == 0) ∧ (index <= arrayMaxIndex)
          ∧ (Map.size betw == cacheLineSize)
          ∧ (∀) (zipWith (==) vals (Map.elems betw)) id
          where betw :: ArrayVal
                betw = sliceFor index (σa ! arr)


cacheAwareReadLRU :: Var -> FullState -> (Val, CacheState, AccessTime)
cacheAwareReadLRU var σ@((GlobalState { σv }, tlσ, i), cache, _) = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ lookup     σv
    ThreadLocal _ -> assert (      isCachable $ VarName var) $ lookup     tlσ
    Register    _ -> assert (not $ isCachable $ VarName var) $ (tlσ ! var, cache, registerAccessTime)
  where cvar = CachedVar var

        lookup :: Map Var Val -> (Val, CacheState, AccessTime )
        lookup someσ = 
          require (consistent σ) $
          case OMap.lookup cvar cache of
            Nothing                   -> let { cval = CachedVal val ; val = someσ ! var } in
                                         (val, OMap.fromList $ (cvar, cval) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheMissTime )
            Just cval@(CachedVal val) -> (val, OMap.fromList $ (cvar, cval) : (                       OMap.assocs $ OMap.delete cvar cache), cacheHitTime  )


cacheTimeReadLRU :: Var -> CacheState -> (CacheState, AccessTime)
cacheTimeReadLRU var cache = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ lookup
    ThreadLocal _ -> assert (      isCachable $ VarName var) $ lookup
    Register    _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime)
  where cvar = CachedVar var
        lookup =
          case OMap.lookup cvar cache of
            Nothing  -> (OMap.fromList $ (cvar, undefinedCacheValue) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheMissTime)
            Just cval-> assert (cval == undefinedCacheValue) $
                        (OMap.fromList $ (cvar, undefinedCacheValue) : (                       OMap.assocs $ OMap.delete cvar cache), cacheHitTime)


type Index = Val

cacheAwareArrayReadLRU :: Array -> Index -> FullState -> (Val, CacheState, AccessTime)
cacheAwareArrayReadLRU arr ix σ@((GlobalState { σa }, tlσ, _), cache, _) = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ lookup
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        lookup :: (Val, CacheState, AccessTime )
        lookup = 
          require (consistent σ) $
          case OMap.lookup carr cache of
            Nothing ->                           let { cval = CachedArraySlice vals ; vals = Map.elems $ sliceFor alignedIx (σa ! arr) } in
                                                 (vals !! (ix - alignedIx), OMap.fromList $ (carr, cval) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheMissTime )
            Just cval@(CachedArraySlice vals) -> (vals !! (ix - alignedIx), OMap.fromList $ (carr, cval) : (                       OMap.assocs $ OMap.delete carr cache), cacheHitTime  )


cacheTimeArrayReadLRU :: Array -> Index -> CacheState -> (CacheState, AccessTime)
cacheTimeArrayReadLRU arr ix cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ lookup
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        lookup = 
          case OMap.lookup carr cache of
            Nothing   -> (OMap.fromList $ (carr, undefinedCacheArrayValue) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheMissTime)
            Just cval -> assert (cval == undefinedCacheArrayValue) $
                         (OMap.fromList $ (carr, undefinedCacheArrayValue) : (                       OMap.assocs $ OMap.delete carr cache), cacheHitTime)

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
    ThreadLocal _ -> assert (      isCachable $ VarName var) $ write
    Register    _ -> assert (not $ isCachable $ VarName var) $ (cache, registerAccessTime )
  where cvar = CachedVar var
        write = 
          case OMap.lookup cvar cache of
            Nothing  ->  (OMap.fromList $ (cvar, undefinedCacheValue) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheWriteTime )
            Just _   ->  (OMap.fromList $ (cvar, undefinedCacheValue) : (                       OMap.assocs $ OMap.delete cvar cache), cacheWriteTime )


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

cacheTimeArrayReadLRUState :: Monad m => Array -> Index -> StateT CacheTimeState m ()
cacheTimeArrayReadLRUState arr ix = do
    (cache, time) <- get
    let (cache', accessTime) = cacheTimeArrayReadLRU arr ix cache
    put (cache', time + accessTime)
    return ()



cacheTimeArrayWriteLRU :: Array -> Index -> CacheState -> (CacheState, AccessTime)
cacheTimeArrayWriteLRU arr ix cache = case arr of
    Array       _ -> assert (      isCachable $ ArrayName arr) $ write
  where alignedIx = toAlignedIndex ix
        carr = CachedArrayRange arr alignedIx
        write = 
          case OMap.lookup carr cache of
            Nothing  ->  (OMap.fromList $ (carr, undefinedCacheArrayValue) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheWriteTime )
            Just _   ->  (OMap.fromList $ (carr, undefinedCacheArrayValue) : (                       OMap.assocs $ OMap.delete carr cache), cacheWriteTime )


cacheTimeArrayWriteLRUState :: Monad m => Array -> Index -> StateT CacheTimeState m ()
cacheTimeArrayWriteLRUState arr ix = do
    (cache, time) <- get
    let (cache', accessTime) = cacheTimeArrayWriteLRU arr ix cache
    put (cache', time + accessTime)
    return ()

cacheAwareWriteLRU :: Var -> Val -> FullState -> FullState
cacheAwareWriteLRU var val σ@((globalσ@(GlobalState { σv }), tlσ ,i), cache, time ) = case var of
    Global      _ -> assert (      isCachable $ VarName var) $ let (     σv', cache', accessTime) = write      σv in ((globalσ{ σv = σv'}, tlσ , i), cache', time + accessTime)
    ThreadLocal _ -> assert (      isCachable $ VarName var) $ let (    tlσ', cache', accessTime) = write     tlσ in ((globalσ           , tlσ', i), cache', time + accessTime)
    Register    _ -> assert (not $ isCachable $ VarName var) $ let tlσ' = Map.insert var val tlσ in                  ((globalσ           , tlσ', i), cache , time + registerAccessTime )
  where cvar = CachedVar var
        cval = CachedVal val
        write someσ = 
          require (consistent σ) $
          case OMap.lookup cvar cache of
            Nothing  ->  (Map.insert var val someσ, OMap.fromList $ (cvar, cval) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheWriteTime )
            Just _   ->  (Map.insert var val someσ, OMap.fromList $ (cvar, cval) : (                       OMap.assocs $ OMap.delete cvar cache), cacheWriteTime )


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
            case OMap.lookup carr cache of
              Nothing  ->  (Map.alter update arr someσ, OMap.fromList $ (carr, cval) : (take (cacheSize - 1) $ OMap.assocs                    cache), cacheWriteTime )
              Just _   ->  (Map.alter update arr someσ, OMap.fromList $ (carr, cval) : (                       OMap.assocs $ OMap.delete carr cache), cacheWriteTime )
          where update (Nothing) = Just $ Map.insert ix val arrayEmpty
                update (Just av) = Just $ Map.insert ix val av 
          
cacheAwareArrayWriteLRUState :: Monad m => Array -> Index -> Val -> StateT FullState m ()
cacheAwareArrayWriteLRUState arr ix val = do
    σ <- get
    put $ cacheAwareArrayWriteLRU arr ix val σ
    return ()


initialCacheState :: CacheState
initialCacheState = OMap.empty

initialFullState :: FullState
initialFullState = ((globalEmpty, Map.empty, ()), initialCacheState, 0)

exampleSurvey1 :: FullState
exampleSurvey1 = ((GlobalState { σv = Map.fromList                $ [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4), (Global "x", 42)],
                                 σa = Map.empty },
                   Map.empty, ()),
                   OMap.fromList $ fmap wrapped                   $ [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4)],
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
  return $ xVal `shiftL` yVal
cacheAwareLRUEvalV (Shr x y) = do
  xVal <- cacheAwareLRUEvalV x
  yVal <- cacheAwareLRUEvalV y
  return $ xVal `shiftR` yVal
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
cacheTimeLRUEvalV (ArrayRead a ix) = do
  cacheTimeLRUEvalV ix
  i <- lift alignedIndices
  cacheTimeArrayReadLRUState a i
  return ()
cacheTimeLRUEvalV (Plus  x y) = do
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
cacheTimeStepForState (AssignArray a ix vf) = do
        cacheTimeLRUEvalV vf
        cacheTimeLRUEvalV ix
        i <- lift alignedIndices
        cacheTimeArrayWriteLRUState a i
        σ' <- get
        return σ'
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




stateSetsSlow :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> (Set (Node, s), Set ((Node, s), CFGEdge, (Node, s)))
stateSetsSlow step g  σ0 n0 = (㎲⊒) (Set.fromList [(n0,σ0)], Set.fromList []) f
  where f (cs, es) = (cs ∪ Set.fromList [  (n', σ') | (n, σ, e, n', σ') <- next ],
                      es ∪ Set.fromList [ ((n,  σ ), e, (n', σ')) | (n, σ, e, n', σ') <- next ]
                     )
          where next = [ (n, σ, e, n', σ')  | (n,σ) <- Set.toList cs, (n',e) <- lsuc g n, σ' <- step e σ]

stateSets :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> (Set (Node, s), Set ((Node, s), CFGEdge, (Node, s)))
stateSets step g σ0 n0 = {- assert (result == stateSetsSlow step g σ0 n0) $ -} result
  where result = go (Set.fromList [(n0,σ0)]) (Set.fromList [(n0,σ0)]) (Set.fromList [])
        go workset cs es
         | Set.null workset = (cs, es)
         | otherwise         = go (workset' ∪ csNew) (cs ∪ csNew) (es ∪ esNew)
             where ((n,σ), workset') = Set.deleteFindMin workset
                   next = [ (n, σ, e, n', σ')  | (n',e) <- lsuc g n, σ' <- step e σ]
                   
                   csNew = Set.fromList [ (n', σ') | (n, σ, e, n', σ') <- next, not $ (n', σ') ∈ cs ]
                   esNew = Set.fromList [ ((n,  σ ), e, (n', σ')) | (n, σ, e, n', σ') <- next ]


stateGraph :: (Graph gr, Ord s) => AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> gr (Node, s) CFGEdge
stateGraph step g σ0 n0 = mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es]
  where (cs, es) = stateSets step g σ0 n0
        nodes = zip [0..] (Set.toList cs)
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

stateGraphFor :: (Graph gr, Ord s, Ord s') => (s -> s') ->  AbstractSemantic s -> gr CFGNode CFGEdge -> s -> Node -> gr (Node, s') CFGEdge
stateGraphFor α step g σ0 n0 = mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where (cs, es) = stateSets step g σ0 n0
        cs' =  Set.map f cs
          where f (n, s) = (n, α s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α sn), e, (m, α sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

cacheStateGraphForVars :: (Graph gr) => Set CachedObject -> gr CFGNode CFGEdge -> CacheState -> Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVars vars = stateGraphFor α cacheOnlyStepFor
  where α = αFor vars

αFor vars cache = (
            [ (v,i) | (i,(v,s)) <- zip [0..] (OMap.assocs cache), v ∈ vars],
            Set.fromList [ v |  (v,s) <- List.dropWhileEnd (\(v,s) -> not $ v ∈ vars) (OMap.assocs cache), not $ v ∈ vars]
           )

αForReach :: Set CachedObject -> Set Name -> CacheState -> AbstractCacheState
αForReach vars reach cache = (
            [ (v,i) | (i,(v,s)) <- zip [0..] (OMap.assocs cache), v ∈ vars],
            Set.fromList [ v |  (v,s) <- List.dropWhileEnd (\(v,s) -> not $ v ∈ vars) (OMap.assocs cache), not $ v ∈ vars, isReachable v]
           )
  where isReachable (CachedVar v)          = VarName   v ∈ reach
        isReachable (CachedArrayRange a _) = ArrayName a ∈ reach

αForReach2 :: Set CachedObject -> Node -> Set Name -> Node -> CacheState -> AbstractCacheState
αForReach2 vars mm reach n cache
  | n == mm = (
            [ (v,0) | (v,s) <- OMap.assocs cache, v ∈ vars],
            Set.empty
           )
  | otherwise = αForReach vars reach cache




cacheStateGraphForVarsAndCacheStatesAndAccessReachable :: (Graph gr) => Set CachedObject -> (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) -> Map Node (Set Name) -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVarsAndCacheStatesAndAccessReachable vars (cs, es) reach =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α (reach !! n) s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α (reach !! n) sn), e, (m, α (reach !! m) sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α = αForReach vars
        
        (!!) m x = Map.findWithDefault Set.empty x m


cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 :: (Graph gr) => Set CachedObject -> (Set (Node, CacheState), Set ((Node, CacheState), CFGEdge, (Node, CacheState))) -> Map Node (Set Name) -> Node -> gr (Node, AbstractCacheState) CFGEdge
cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs, es) reach mm =  mkGraph nodes [(toNode ! c, toNode ! c', e) | (c,e,c') <- Set.toList es']
  where cs' =  Set.map f cs
          where f (n, s) = (n, α (reach !! n) n s)
        es' =  Set.map f es
          where f ((n, sn), e, (m,sm)) = ((n,α (reach !! n) n sn), e, (m, α (reach !! m) m sm))
        nodes = zip [0..] (Set.toList cs')
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        α = αForReach2 vars mm

        (!!) m x = Map.findWithDefault Set.empty x m


cacheStateGraph'ForVarsAtMForGraph :: forall gr. (DynGraph gr) => Set CachedObject ->  gr (Node, CacheState) CFGEdge  ->  Node -> gr (Node, CacheState) CFGEdge
cacheStateGraph'ForVarsAtMForGraph vars g0 mm = result
  where result = subgraph (rdfs (fmap fst $ withNewIds) merged) merged
        merged :: gr (Node, CacheState) CFGEdge
        merged = insEdges [ (id, oldMNodesToNew ! id', e) | edge@(id,id',e) <- mEdgesIncoming]
               $ insNodes withNewIds
               $ delNodes (fmap fst mNodes)
               $ g0
        mNodes = [ node | node@(id, (m, cache)) <- labNodes g0, m == mm ]
        mNodeS = Set.fromList $ fmap fst $ mNodes
        mEdgesIncoming = [ edge | edge@(id,id',e) <- labEdges g0, id' ∈ mNodeS, not $ id ∈ mNodeS ]

        oldMNodesToNew = Map.fromList $ [ (id, newId) | node@(id, (m, cache)) <- mNodes, let αcache = (m, α m cache), let Just (newId,_) = List.find (\(_,αcache') -> αcache == αcache') withNewIds ]
        new = newNodes (length abstract) g0
        abstract   = Set.toList $ Set.fromList [ (m, α m cache)  | node@(id, (m, cache)) <- mNodes ]
        withNewIds = zip new abstract


        α n cache
          | n == mm   = OMap.fromList [ (v,undefinedCacheValue) | (v,s) <- OMap.assocs cache, v ∈ vars]
          | otherwise = cache






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


prependInitialization :: DynGraph gr => gr CFGNode CFGEdge -> Node -> Node -> Map Name Node -> Map Name Val -> gr CFGNode CFGEdge
prependInitialization g0 n0 newN0 varToNode state =
    g0 `mergeTwoGraphs` g1
  where g1 = mkGraph
               [(n,n) | n <- newN0 : Map.elems varToNode]
               (   [(newN0, if Map.null varToNode then n0 else snd $ head $ Map.assocs varToNode, NoOp)]
                ++ [ (n,n', Assign      var          (Val $ state ! x))  | ((x@(VarName   var),n),(_,n')) <- zip (Map.assocs varToNode) ((tail $ Map.assocs varToNode) ++ [(undefined,n0)]) ]
                ++ [ (n,n', AssignArray arr  (Val 0) (Val $ state ! x))  | ((x@(ArrayName arr),n),(_,n')) <- zip (Map.assocs varToNode) ((tail $ Map.assocs varToNode) ++ [(undefined,n0)]) ]
               )


costsFor :: DynGraph gr =>  gr (Node, CacheState) CFGEdge -> Map (Node, Node, CFGEdge) (Set AccessTime)
costsFor csGraph  =  (∐) [ Map.fromList [ ((n0, m0, e), Set.fromList [time]) ]  |
                                                 (n, (n0,cs)) <- labNodes csGraph,
                                                 (m, e) <- lsuc csGraph n,
                                                 let Just (m0,_) = lab csGraph m,
                                                 fullState'@(_,time) <- cacheTimeStepFor e (cs, 0)
                      ]

cacheCostDecisionGraph :: DynGraph gr => gr CFGNode CFGEdge -> Node -> (gr CFGNode CFGEdge, Map (Node, Node) Integer)
cacheCostDecisionGraph g n0 = (
      mkGraph
        ((labNodes g) ++ ([(n,n) | n <- new]))
        (irrelevant ++ [ (n,m',l)    | ((e@(n,_,l),_), m') <- Map.assocs nodesFor ]
                    ++ [ (m',m,NoOp) | ((e@(_,m,_),_), m') <- Map.assocs nodesFor ]
        ),
                  Map.fromList [ ((n ,m),  cost    ) | e@(n,m,l) <- irrelevant, let [cost] = Set.toList $ costs ! e, assert (cost > 0) True]
      `Map.union` Map.fromList [ ((n ,m'), cost - 1) | ((e@(n,_,_),cost), m') <- Map.assocs nodesFor, assert (cost > 1) True   ]
      `Map.union` Map.fromList [ ((m',m ),        1) | ((e@(_,m,_),   _), m') <- Map.assocs nodesFor ]
    )
  where csGraph = cacheStateGraph g initialCacheState n0
        costs = costsFor csGraph

        isRelevant e = nrSuc e > 1
        nrSuc e = Set.size $ costs ! e
        
        nodesFor =               (Map.fromList $ zip [ (e,time) | e <-   relevant, time <- Set.toList $ costs ! e ] new)
                    -- `Map.union`  (Map.fromList       [ ((e,time), | e@(n,m,l) <- irrelevant, let time = 1 ])
        relevant   = [ e | e <- labEdges g,       isRelevant e]
        irrelevant = [ e | e <- labEdges g, not $ isRelevant e]
        totalnew = sum $ fmap nrSuc relevant
        new = newNodes totalnew g



type CacheGraphNode = Node


cacheStateFor graph csGraph n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e, isCachable var ]
           where cs = assert (n == n') $ cs'
                 Just (n', cs') = lab csGraph y'

cacheStateOnFor csGraph vars y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | var <- Set.toList $ vars ]
           where Just (_, cs) = lab csGraph y'



cacheStateUnsafeFor graph csGraph n y' = Map.fromList [(var, fmap (const ()) $ OMap.lookup var cs) | (_,e) <- lsuc graph n, var <- Set.toList $ useE e, isCachable var ]
           where cs = cs'
                 Just (_, cs') = lab csGraph y'


allCacheStateFor graph csGraph n y' = fmap (const ()) cs
           where cs = assert (n == n') $ cs'
                 Just (n', cs') = lab csGraph y'


nextReachable ::  Graph gr => gr (Node, s) CFGEdge  -> Map CacheGraphNode (Map Node (Set CacheGraphNode))
nextReachable csGraph = (㎲⊒) init f
  where f nextReach = Map.fromList [ (y, Map.fromList [ (n, Set.fromList [y]) ])                    | (y,(n,_)) <- labNodes csGraph ]
                    ⊔ Map.fromList [ (y, Map.delete n $ (∐) [ nextReach ! x | x <- suc csGraph y] ) | (y,(n,_)) <- labNodes csGraph ]
        init = Map.fromList [ (y, Map.empty) | y <- nodes csGraph ]



csd''''Of3 :: (DynGraph gr, Show (gr (Node, AbstractCacheState) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd''''Of3 graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph y,
                                        -- (if (n == 17 ∧ m == 21) then traceShow (vars,y,y's,  g'', "KKKKKK", csGraph) else id) True,
                                        let relevant  = Map.findWithDefault Set.empty m (nextReach ! y),
                                        -- (if (n == 23 ∧ m == 22) then traceShow (vars,y,y's,  relevant) else id) True,
                                        let canonical           = Set.findMin relevant,
                                        let canonicalCacheState = cacheState csGraph canonical,
                                        not $ (∀) relevant (\y' -> cacheState csGraph y' == canonicalCacheState)
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable vars (cs,es) reach :: Gr (Node, AbstractCacheState) CFGEdge,
      let nextReach = nextReachable csGraph,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph],
      let y's  = Set.fromList $ nodesToCsNodes ! m,
      let canonical = Set.findMin y's,
      let canonicalCacheState = cacheState csGraph canonical,
      not $ (∀) y's (\y' -> cacheState csGraph y' == canonicalCacheState),
      let ys = wodTEILSliceViaISinkDom csGraph y's
   ]
  where cacheState csGraph y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0

        


csd''''Of4 :: (DynGraph gr, Show (gr (Node, AbstractCacheState) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csd''''Of4 graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph y,
                                        n /= m,
                                        -- (if (n == 7 ∧ m == 17) then traceShow (vars,y,y's, "KKKKKK", csGraph, g'') else id) True,
                                        let relevant  = Map.findWithDefault Set.empty m (nextReach ! y),
                                        -- (if (n == 23 ∧ m == 22) then traceShow (vars,y,y's,  relevant) else id) True,
                                        let canonical           = Set.findMin relevant,
                                        let canonicalCacheState = cacheState csGraph canonical,
                                        if (∀) relevant (\y' -> cacheState csGraph y' == canonicalCacheState) then traceShow (n,m,y,vars,relevant) True else True,
                               assert  (not $ (∀) relevant (\y' -> cacheState csGraph y' == canonicalCacheState)) True
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: Gr (Node, AbstractCacheState) CFGEdge,
      let nextReach = nextReachable csGraph,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph],
      let y's  = Set.fromList $ nodesToCsNodes ! m,
      let canonical = Set.findMin y's,
      let canonicalCacheState = cacheState csGraph canonical,
      not $ (∀) y's (\y' -> cacheState csGraph y' == canonicalCacheState),
      let g'' = let { ms = Set.toList y's ;
            g = csGraph ;
            g''   = foldr (flip delSuccessorEdges) g' ms ;
            toMs   = rdfs ms g ;
            g' = subgraph toMs g } in g'',
      let ys = wodTEILSliceViaISinkDom csGraph y's
   ]
  where cacheState csGraph y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0


accessReachableFrom :: Graph gr => gr CFGNode CFGEdge -> Map Node (Set Name)
accessReachableFrom graph = (㎲⊒) init f
  where f reach = Map.fromList [ (n, (∐) [ Set.filter isCachable $ useE e ∪ defE e | (_,e) <- lsuc graph n ]) | n <- nodes graph ]
                ⊔ Map.fromList [ (n, (∐) [ reach ! x | x <- suc graph n] ) | n <- nodes graph ]
        init    = Map.fromList [ (n, Set.empty) | n <- nodes graph ]




merged :: (Graph gr) => gr (Node, s) CFGEdge ->  Map Node (Map CacheGraphNode (Set CacheGraphNode)) -> gr (Node, Set CacheGraphNode) CFGEdge
merged csGraph' equivs =  mkGraph nodes' edges
  where edges =  List.nub $ fmap f $ (labEdges csGraph')
          where f (y,y',e) = (toNode ! (n,equiv), toNode ! (n', equiv'), e)
                  where Just (n,_)  = lab csGraph' y
                        Just (n',_) = lab csGraph' y'
                        equiv  = representative $ equivs ! n  ! y
                        equiv' = representative $ equivs ! n' ! y'
        nodes = zip [0..] (Set.toList $ Set.fromList $ [ (n, representative equiv) | (n, equivN) <- Map.assocs equivs, equiv <- Map.elems equivN ])
        toNode = Map.fromList $ fmap (\(a,b) -> (b,a)) nodes

        representative = Set.findMin -- use the first node in a equivalence class as representative

        nodes' = fmap fromRep nodes
          where fromRep (i,(n,y)) = (i, (n, equivs ! n ! y))

csGraphFromMergeFor graph n0 m = merged csGraph' equivs
    where (equivs, csGraph') = mergeFromFor graph n0 m

mergeFromFor graph n0 m = (mergeFrom graph' csGraph' idom roots, csGraph')
    where (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0

          vars  = head $ List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars]
          graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m
          reach = accessReachableFrom graph'
          csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: Gr (Node, AbstractCacheState) CFGEdge
          nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph']
          y's  = nodesToCsNodes ! m
          
          csGraph' = let { toY's = subgraph (rdfs y's csGraph) csGraph } in foldr (flip delSuccessorEdges) toY's y's
          idom = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'
          roots = Set.fromList y's

csdMergeOf :: forall gr. (DynGraph gr, Show (gr (Node, AbstractCacheState) CFGEdge)) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeOf graph n0 =  invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph'' y,
                                        -- (if (n == 7 ∧ m == 17) then traceShow (vars,y,y's, "KKKKKK", csGraph, g'') else id) True,
                                        n /= m
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let reach = accessReachableFrom graph',
      let csGraph = cacheStateGraphForVarsAndCacheStatesAndAccessReachable2 vars (cs,es) reach m :: gr (Node, AbstractCacheState) CFGEdge,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph'],
      let y's  = nodesToCsNodes ! m,
      let csGraph' = let { toY's = subgraph (rdfs y's csGraph) csGraph } in foldr (flip delSuccessorEdges) toY's y's,
      let idom' = Map.fromList $ iPDomForSinks [[y'] | y' <- y's] csGraph',
      let roots' = Set.fromList y's,
      let equivs = mergeFrom graph' csGraph' idom' roots',
      let csGraph'' = merged csGraph' equivs,
      let idom'' = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'',
      let ys = Set.fromList [ y | y <- nodes csGraph'', idom'' ! y == Nothing]
   ]
  where cacheState csGraph y' = fmap fst $ fst $ cs
          where Just (_,cs) = lab csGraph y'
        (cs, es)  = stateSets cacheOnlyStepFor graph initialCacheState n0

csdMergeDirectOf :: forall gr. (DynGraph gr, Show (gr (Node, CacheState) CFGEdge),  Show (gr (Node, Set CacheGraphNode) CFGEdge )) => gr CFGNode CFGEdge -> Node -> Map Node (Set Node)
csdMergeDirectOf graph n0 = traceShow (List.length $ nodes $ csGraph) $ invert'' $
  Map.fromList [ (m, Set.fromList [ n | y <- Set.toList ys,
                                        let Just (n, _) = lab csGraph'' y,
                                        -- (if (n == 7 ∧ m == 17) then traceShow (vars,y,y's, "KKKKKK", csGraph, g'') else id) True,
                                        n /= m
                     ]
                 )
    | m <- nodes graph, vars <- List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars],
      let graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m,
      let csGraph' = cacheStateGraph'ForVarsAtMForGraph vars csGraph m :: gr (Node, CacheState) CFGEdge,
      let nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph', n == n' ] ) | n <- nodes graph'],
      let y's  = nodesToCsNodes ! m,
      let idom' = Map.fromList $ iPDomForSinks [[y'] | y' <- y's] csGraph',
      let roots' = Set.fromList y's,
      let equivs = mergeFromForEdgeToSuccessor edgeToSuccessors0 graph' csGraph'  idom' roots',
      let csGraph'' = merged csGraph' equivs,
      let idom'' = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'',
      let ys = Set.fromList [ y | y <- nodes csGraph'', idom'' ! y == Nothing]
   ]
  where csGraph = cacheStateGraph graph initialCacheState n0
        edgeToSuccessors0 = (∐) [ Map.fromList [ ((y,e), Set.fromList [(x,m)])] | (y,x,e) <- labEdges csGraph, let Just (m,_) = lab csGraph x]


csGraphFromMergeDirectFor graph n0 m = merged csGraph' equivs
    where (equivs, csGraph') = mergeDirectFromFor graph n0 m


mergeDirectFromFor graph n0 m = (mergeFromForEdgeToSuccessor edgeToSuccessors0 graph' csGraph'  idom roots, csGraph')
  where   csGraph = cacheStateGraph graph initialCacheState n0
          edgeToSuccessors0 = (∐) [ Map.fromList [ ((y,e), Set.fromList [(x,m)]) ] | (y,x,e) <- labEdges csGraph, let Just (m,_) = lab csGraph x]
          
          vars  = head $ List.nub [ vars | (_,e) <- lsuc graph m, let vars = cachedObjectsFor e, not $ Set.null vars]
          graph' = let { toM = subgraph (rdfs [m] graph) graph } in delSuccessorEdges toM m
          csGraph' = cacheStateGraph'ForVarsAtMForGraph vars csGraph m
          nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph', n == n' ] ) | n <- nodes graph']
          y's  = nodesToCsNodes ! m
          
          idom = fmap fromSet $ isinkdomOfTwoFinger8 csGraph'
          roots = Set.fromList y's


mergeFromSlow ::  (DynGraph gr, Show (gr (Node, s) CFGEdge))=> gr CFGNode CFGEdge -> gr (Node, s) CFGEdge -> Map CacheGraphNode (Maybe CacheGraphNode) -> Set CacheGraphNode -> Map Node (Map CacheGraphNode (Set CacheGraphNode))
mergeFromSlow graph csGraph idom roots  =  (𝝂) init f 
  where 
        nodesToCsNodes = Map.fromList [ (n, [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]
        f :: Map Node (Map CacheGraphNode (Set CacheGraphNode))
          -> Map Node (Map CacheGraphNode (Set CacheGraphNode))
        f equivs = -- traceShow (Map.filter (\equivs -> (∃) equivs (not . Set.null)) $ equivs, rootOf) $
          (
              Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y' | y' <- ys, Map.lookup y' rootOf == Just r ]) ] | y <- ys, Just r <- [Map.lookup y rootOf ]])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
            ⊔ Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y ] ) ] |  y <- ys])
                           | (n,ys) <- Map.assocs nodesToCsNodes
              ]
            ⊔ Map.fromList [ (n, (∐) [ Map.fromList [ (y, Set.fromList [ y' |
                                                                   y' <- ys,
                                                                   (∀) es (\(_,e) ->
                                                                     (∀) (lsuc csGraph y ) (\(x,  ey ) -> if ey  /= e then True else
                                                                     (∀) (lsuc csGraph y') (\(x', ey') -> if ey' /= e then True else
                                                                       let Just (m, _) = lab csGraph x
                                                                           Just (m',_) = lab csGraph x'
                                                                       in assert (m == m') $ 
                                                                       (∃) (equivs ! m) (\equiv -> x ∈ equiv ∧ x' ∈ equiv)
                                                                     ))
                                                                   )
                                                ]
                                  )] | y <- ys, not $ y ∈ roots, let es = lsuc csGraph y ])
                           | (n,ys) <- Map.assocs nodesToCsNodes,
                             assert ((∀) ys (\y -> (∀) ys (\y' -> (Set.fromList $ fmap snd $ lsuc csGraph y) == (Set.fromList $ fmap snd $ lsuc csGraph y')))) True
              ]
           )
        init = Map.fromList [ (n, Map.fromList [ (y, ysS) | y <- ys] ) | (n,ys) <- Map.assocs $ nodesToCsNodes, let ysS = Set.fromList ys]
        rootOf = Map.fromList [ (y, r) | y <- nodes csGraph, let r = maxFromTreeM idom y, r ∈ roots ]


mergeFrom ::  (DynGraph gr, Show (gr (Node, s) CFGEdge)) =>
  gr CFGNode CFGEdge ->
  gr (Node, s) CFGEdge ->
  Map CacheGraphNode (Maybe CacheGraphNode) ->
  Set CacheGraphNode ->
  Map Node (Map CacheGraphNode (Set CacheGraphNode))
mergeFrom graph csGraph idom roots = mergeFromForEdgeToSuccessor edgeToSuccessors graph csGraph  idom roots
  where edgeToSuccessors = (∐) [ Map.fromList [ ((y,e), Set.fromList [(x,m)]) ] | (y,x,e) <- labEdges csGraph, let Just (m,_) = lab csGraph x]



mergeFromForEdgeToSuccessor ::  (DynGraph gr, Show (gr (Node, s) CFGEdge)) =>
  Map (CacheGraphNode, CFGEdge) (Set (CacheGraphNode, Node)) ->
  gr CFGNode CFGEdge ->
  gr (Node, s) CFGEdge ->
  Map CacheGraphNode (Maybe CacheGraphNode) ->
  Set CacheGraphNode ->
  Map Node (Map CacheGraphNode (Set CacheGraphNode))
mergeFromForEdgeToSuccessor edgeToSuccessors0 graph csGraph idom roots = assert (result == mergeFromSlow graph csGraph idom roots) result
  where result = (go orderToNodes init) ⊔ equivsNBase
          where (⊔) :: Map Node (Map CacheGraphNode (Set CacheGraphNode)) -> Map Node (Map CacheGraphNode (Set CacheGraphNode)) -> Map Node (Map CacheGraphNode (Set CacheGraphNode))
                (⊔) left right =  Map.unionWithKey f left right
                f n fromSuccessorsN  fromBaseN = Map.unionWithKey g fromSuccessorsN fromBaseN
                g y fromSuccessorsYs fromBaseYs = {- assert (fromBaseYs ⊆ fromSuccessorsYs) $ -} fromSuccessorsYs
        go workset fromSuccessors
           | Map.null workset  = fromSuccessors
           | otherwise         =
               if changed then
                 go (workset' `Map.union` influenced) (Map.insert n (fromSuccessorsN' ⊔ fromRootsN) fromSuccessors)
               else
                 go  workset'                                                                       fromSuccessors
          where ((_,n), workset') = Map.deleteFindMin workset
                ys = nodesToCsNodes ! n
                fromRootsN = fromRoots ! n
                fromSuccessorsN' = goSuccessors (ys ∖ roots) Map.empty
                  where goSuccessors ysLeft fromsucc
                           | Set.null ysLeft = fromsucc
                           | otherwise = assert (y ∈ y's) goSuccessors ysLeft' ((Map.fromSet (const y's) y's) `Map.union` fromsucc)
                          where y = Set.findMin ysLeft
                                es = lsuc csGraph y
                                y's     = Set.insert y y's0
                                ysLeft' = Set.delete y ysLeft'0
                                (y's0, ysLeft'0) = Set.partition (\y' -> 
                                                                   (∀) es (\(_,e) ->
                                                                     (∀) (edgeToSuccessors ! (y , e)) (\(x , m ) ->
                                                                     (∀) (edgeToSuccessors ! (y', e)) (\(x', m') ->
                                                                          assert (m == m') $
                                                                          (x  ∈ Map.findWithDefault Set.empty x' (fromSuccessors ! m')  ∨  x ∈ equivsNBase ! m' ! x')
                                                                     ))
                                                                   )
                                                               )
                                                               ysLeft

                changed = assert (fromSuccessorsN ⊒ fromSuccessorsN') $
                          assert (diffSize == (fromSuccessorsN' /= fromSuccessorsN)) $ diffSize
                  where fromSuccessorsN = fromSuccessors ! n
                        diffSize = Map.size fromSuccessorsN /= Map.size fromSuccessorsN'
                                 ∨ (∃) (zip (Map.toAscList fromSuccessorsN) (Map.toAscList fromSuccessorsN')) (\((y,ys), (y', y's)) -> assert (y == y') $ Set.size ys /= Set.size y's)
                influenced = Map.fromList [ (nodesToOrder ! m, m) | m <- pre graph n]

        init = Map.mapWithKey (\n ys -> Map.fromSet (const ys) ys) nodesToCsNodes
        rootOf = Map.fromList [ (y, r) | y <- nodes csGraph, let r = maxFromTreeM idom y, r ∈ roots ]

        nodesToCsNodes = Map.fromList [ (n, Set.fromList [ y | (y, (n', csy)) <- labNodes csGraph, n == n' ] ) | n <- nodes graph]

        edgeToSuccessors = (∐) [ Map.fromList [ ((y,e), Set.fromList [ (x,m) ]) ] | x <- Set.toList $ roots, let Just (m,_) = lab csGraph x, (y,e) <- lpre csGraph x] `Map.union` edgeToSuccessors0

        fromRoots = Map.mapWithKey (\n ys -> go ys Map.empty) nodesToCsNodes
          where go ysLeft fromroots
                  | Set.null ysLeft = fromroots
                  | otherwise = let mr = Map.lookup y rootOf in case mr of
                        Nothing -> go ysLeft0                                          fromroots
                        Just r  -> let (y's, ysLeft') = Set.partition (\y' -> Map.lookup y' rootOf == mr) ysLeft in
                                   go ysLeft' (Map.fromSet (const y's) y's `Map.union` fromroots)
                      where (y, ysLeft0) = Set.deleteFindMin ysLeft

        equivsNBase = Map.mapWithKey (\n ys -> fromRoots ! n ⊔ (Map.fromSet Set.singleton $ ys ∖ roots)) nodesToCsNodes

        order = List.reverse $ topsort graph
        nodesToOrder = Map.fromList $ zip order [0..]
        orderToNodes = Map.fromList $ zip [0..] order

