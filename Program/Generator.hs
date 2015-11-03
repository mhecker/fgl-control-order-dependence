{-# LANGUAGE NamedFieldPuns #-}
module Program.Generator where

import IRLSOD
import Program (StaticThread)
import Program.For
import Unicode

import Test.QuickCheck

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.List ((\\))



data Generated = Generated For (Set Var) (Map StaticThread (Set Var)) deriving Show

instance Arbitrary Generated where
  arbitrary = sized $ forGenerator inChannels outChannels vars varsAvailable varsForbidden threadsAvailable
    where inChannels       = Set.fromList [stdIn]
          outChannels      = Set.fromList [stdOut]
          vars             = Set.fromList ["x", "y", "z", "a", "b", "c"]
          varsAvailable    = Set.fromList []
          varsForbidden    = Set.fromList []
          threadsAvailable = Set.fromList [1,2,3]

expGenerator :: Set Var -> Gen VarFunction
expGenerator varsAvailable
  | Set.null varsAvailable = elements $ fmap Val [-1,0,1,17,42]
  | otherwise              = frequency [
    (1, do x <- elements $ Set.toList varsAvailable
           y <- elements $ Set.toList varsAvailable
           return $ (Var x) `Plus` (Var y)
    )
  ]

bexpGenerator :: Set Var -> Gen BoolFunction
bexpGenerator varsAvailable
  | Set.null varsAvailable = elements $ [CTrue, CFalse]
  | otherwise              = frequency [
    (1, do x <- expGenerator varsAvailable
           return $ Leq (Val 0) x 
    )
  ]

forGenerator :: Set InputChannel -> Set OutputChannel -> Set Var -> Set Var -> Set Var -> Set StaticThread -> Int -> Gen Generated
forGenerator inChannels outChannels vars varsAvailable varsForbidden threadsAvailable n
 | n > maxSize = forGenerator inChannels outChannels vars varsAvailable varsForbidden threadsAvailable maxSize
 | n <= 1      = frequency [
   (1,    return $ Generated (Skip)
                             (varsAvailable)
                             (Map.empty)),
   (1, do var <- elements $ Set.toList (vars ∖ varsForbidden)
          exp <- expGenerator varsAvailable
          return $ Generated (Ass var exp)
                             (varsAvailable ∪ Set.fromList [var])
                             (Map.empty)),
   (1, do channel <- elements $ Set.toList inChannels
          var     <- elements $ Set.toList (vars ∖ varsForbidden)
          return $ Generated (ReadFromChannel var channel)
                             (varsAvailable ∪ Set.fromList [var])
                             (Map.empty)),
   (1, do channel <- elements $ Set.toList outChannels
          exp     <- expGenerator varsAvailable
          return $ Generated (PrintToChannel  exp channel)
                             (varsAvailable)
                             (Map.empty)),
    (if (Set.null (threadsAvailable)) then 0 else 1,
       do thread <- elements $ Set.toList threadsAvailable
          return $ Generated (SpawnThread thread)
                             (varsAvailable)
                             (Map.fromList [(thread, varsAvailable)]))
   ]
 | otherwise   = frequency [
   (2, do m <- elements $  [1..4]
          Generated p'  varsAvailable' spawned'  <- forGenerator inChannels outChannels vars varsAvailable varsForbidden                        threadsAvailable     (n-1)
          return $ Generated (ForC m p')
                             (varsAvailable')
                             (spawned')),
   (if (Set.null (varsAvailable ∖ varsForbidden)) then 0 else 2,
       do var <- elements $ Set.toList (varsAvailable ∖ varsForbidden)
          Generated p'  varsAvailable' spawned'  <- forGenerator inChannels outChannels vars varsAvailable (varsForbidden ∪ Set.fromList [var]) threadsAvailable     (n-1)
          return $ Generated (ForV var p')
                             (varsAvailable')
                             (spawned')),
   (2, do bexp <- bexpGenerator varsAvailable
          Generated p'  varsAvailable'  spawned'  <- forGenerator inChannels outChannels vars varsAvailable varsForbidden threadsAvailable                           (n-1)
          Generated p'' varsAvailable'' spawned'' <- forGenerator inChannels outChannels vars varsAvailable varsForbidden (threadsAvailable ∖ Map.keysSet spawned')  (n-1)
          return $ Generated (If bexp p' p'')
                             (varsAvailable' ∩ varsAvailable'')
                             (spawned' `Map.union` spawned'')
   ),
   (5, do Generated p'  varsAvailable'  spawned'  <- forGenerator inChannels outChannels vars varsAvailable  varsForbidden threadsAvailable                          (n-1)
          Generated p'' varsAvailable'' spawned'' <- forGenerator inChannels outChannels vars varsAvailable' varsForbidden (threadsAvailable ∖ Map.keysSet spawned') (n-1)
          return $ Generated (p' `Seq`p'')
                             (varsAvailable'')
                             (spawned''))
   ]
 where maxSize = 5

{- randomly pick n elements out of a given list, without repetition -}
pick :: Eq a => Int -> [a] -> Gen [a]
pick 0 list = return []
pick n list = do x <- elements list
                 picked <- pick (n-1) (list \\ [x])
                 return (x:picked)
