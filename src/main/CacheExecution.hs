{-# LANGUAGE CPP #-}
#define require assert
module CacheExecutions where

import Data.Map.Ordered (OMap, (<|), (|<), (>|), (|>), (<>|), (|<>))
import qualified Data.Map.Ordered as OMap

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Control.Exception.Base (assert)
import Control.Monad.State


import Unicode
import IRLSOD


cacheSize = 4

type ConcreteSemantic a = CFGEdge -> a -> Maybe a

type AbstractSemantic a = CFGEdge -> a -> [a]

type NormalState = (GlobalState,ThreadLocalState,Input)
type CacheState = OMap Var Val
type FullState = (NormalState, CacheState)

consistent :: FullState -> Bool
consistent σ@((globalσ,tlσ,i), cache) = OMap.size cache == cacheSize && (∀) (OMap.assocs cache) cons
  where cons (var@(Global      x), val) =  val == globalσ ! var
        cons (var@(ThreadLocal x), val) =  val ==     tlσ ! var


cacheAwareReadLRU :: Var -> FullState -> (Val, CacheState)
cacheAwareReadLRU var σ@((globalσ,tlσ,i), cache) = case var of
    Global      _ -> lookup globalσ
    ThreadLocal _ -> lookup     tlσ
  where lookup someσ = 
          require (consistent σ) $
          case OMap.lookup var cache of
            Nothing  -> let val = someσ ! var in (val, OMap.fromList $ (var, val) : (take (cacheSize - 1) $ OMap.assocs                   cache) )
            Just val ->                          (val, OMap.fromList $ (var, val) : (                       OMap.assocs $ OMap.delete var cache) )

cacheAwareWriteLRU :: Var -> Val -> FullState -> FullState
cacheAwareWriteLRU var val σ@((globalσ,tlσ,i), cache) = case var of
    Global      _ -> let (globalσ', cache') = write globalσ in ((globalσ',tlσ ,i), cache')
    ThreadLocal _ -> let (    tlσ', cache') = write     tlσ in ((globalσ ,tlσ',i), cache')
  where write someσ = 
          require (consistent σ) $
          case OMap.lookup var cache of
            Nothing  ->  (Map.insert var val someσ, OMap.fromList $ (var, val) : (take (cacheSize - 1) $ OMap.assocs                   cache) )
            Just val ->  (Map.insert var val someσ, OMap.fromList $ (var, val) : (                       OMap.assocs $ OMap.delete var cache) )

initialCacheState = OMap.fromList [(Global ("___undefined___" ++ (show i)), undefined) | i <- [1..cacheSize]]

exampleSurvey1 :: FullState
exampleSurvey1 = ((  Map.fromList [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4), (Global "x", 42)], Map.empty, Map.empty),
                    OMap.fromList [(Global "a", 1), (Global "b", 2), (Global "c", 3), (Global "d", 4)]
                 )


{-
cacheAwareLRUEvalB :: CombinedState -> BoolFunction -> State CacheState Bool
cacheAwareLRUevalB _ CTrue     = return True
cacheAwareLRUevalB _ CFalse    = return False
cacheAwareLRUevalB σ (Leq x y) = do
  xVal <- 
  left <- cacheAwareLRUevalB σ evalV σ x <= evalV σ y
cacheAwareLRUevalB σ (And b1 b2) = evalB σ b1 && evalB σ b2
cacheAwareLRUevalB σ (Or  b1 b2) = evalB σ b1 || evalB σ b2
cacheAwareLRUevalB σ (Not b)     = not $ evalB σ b
-}


{-
cacheStepFor ::  AbstractSemantic FullState
cacheStepFor e c@((globalσ,tlσ,i), cache)  = step e where
      σ = globalσ `Map.union` tlσ
      step :: CFGEdge ->  [FullState]
      step (Guard b bf)
        | b == evalB σ bf                = [c]
        | otherwise                      = []
      step (Assign x@(Global _)      vf) = [(Map.insert x (evalV σ vf)    globalσ,                              tlσ,                    i)]
      step (Assign x@(ThreadLocal _) vf) = [(                             globalσ, Map.insert x (evalV σ vf)    tlσ,                    i)]
      step (Read   x@(Global _)      ch) = [(Map.insert x (head $ i ! ch) globalσ,                              tlσ, Map.adjust tail ch i)]
      step (Read   x@(ThreadLocal _) ch) = [(                             globalσ, Map.insert x (head $ i ! ch) tlσ, Map.adjust tail ch i)]
      step (Print  x ch)                 = [c]
      step (Spawn      )                 = undefined
      step (NoOp       )                 = [c]
      step (Call       )                 = [c]
      step (Return     )                 = [c]
-}
