{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
module Program.Generator where

import IRLSOD
import Program (StaticThread, StaticProcedure, Program(..))
import Program.For
import Program.Defaults (defaultObservabilityMap)
import Unicode

import Test.QuickCheck
import Control.Monad(forM_)

import Data.Graph.Inductive.Graph

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.List ((\\))

import Debug.Trace


data Generated = Generated For (Set Var) (Map StaticThread (Set Var)) (Map StaticProcedure (Set Var))
instance Show Generated where
  show (Generated p vars spawned called)  = "Generated (" ++ (show p) ++ ") undefined undefined undefined"

data IntraGeneratedProgram = IntraGeneratedProgram (Map StaticThread StaticProcedure) (Map StaticProcedure Generated) deriving Show
data GeneratedProgram = GeneratedProgram (Map StaticThread StaticProcedure) (Map StaticProcedure Generated) deriving Show
data SimpleProgram    = SimpleProgram    (Map StaticThread StaticProcedure) (Map StaticProcedure Generated) deriving Show

data SimpleCFG gr = SimpleCFG (gr () ())

deriving instance (Show (gr () ())) => Show (SimpleCFG gr)


toCodeIntra :: IntraGeneratedProgram -> (Map StaticThread  StaticProcedure, Map StaticProcedure For)
toCodeIntra (IntraGeneratedProgram threadOf forProcedures) = (
  threadOf, 
  fmap (\(Generated for _ _ _) -> for) forProcedures
 )
  
toCodeSimple :: SimpleProgram -> (Map StaticThread  StaticProcedure, Map StaticProcedure For)
toCodeSimple (SimpleProgram threadOf forProcedures) = (
  threadOf, 
  fmap (\(Generated for _ _ _) -> for) forProcedures
 )

toCode :: GeneratedProgram -> (Map StaticThread StaticProcedure, Map StaticProcedure For)
toCode (GeneratedProgram threadOf forProcedures) = (
  threadOf, 
  fmap (\(Generated for _ _ _) -> for) forProcedures
 )

sampleCode = do
  generated <- sample' (arbitrary :: Gen GeneratedProgram)
  forM_ (fmap toCode generated) (\(threads, procedures) ->
    do putStrLn $ show $ procedures
   )

programGenerator :: Int -> (Set StaticThread) -> (Set StaticProcedure) -> (Map StaticThread StaticProcedure) -> (Map StaticProcedure Generated) -> Gen (Map StaticThread StaticProcedure, Map StaticProcedure Generated)
programGenerator n threadsAvailable proceduresAvailable generated generatedProcedures
  | not $ Set.null $ threadsAvailable ∩ threadsGenerated = error "invariance violated"
  | (Set.null $ toGenerate) && (Set.null $ toGenerateProcedures) = return (generated, generatedProcedures)
  -- TODO: is this bias toward threads harmful?
  | not $ Set.null $ toGenerate = do
      let thread = head $ Set.toList toGenerate
      let procedure = "thread" ++ show thread
      f@(Generated p' _ spawned' called') <- forGenerator inChannels
                                                          outChannels
                                                          vars
                                                          (varsAvailable ! thread)
                                                          varsForbidden
                                                          (threadsAvailable ∖ (Set.fromList [thread]))
                                                          proceduresAvailable
                                                          n
      programGenerator n
                       ((threadsAvailable ∖ (Map.keysSet spawned')) ∖ (Set.fromList [thread]) )
                       proceduresAvailable 
                       (Map.insert thread    procedure generated)
                       (Map.insert procedure f generatedProcedures)
  | not $ Set.null $ toGenerateProcedures = do
      let procedure = head $ Set.toList toGenerateProcedures
      f@(Generated p' _ spawned' called') <- forGenerator inChannels
                                                          outChannels
                                                          vars
                                                          (varsAvailableCalls ! procedure)
                                                          varsForbidden
                                                          threadsAvailable
                                                          (proceduresAvailable)
                                                          n
      programGenerator n
                       threadsAvailable 
                       ((proceduresAvailable ∖ Set.fromList [procedure]) )
                       generated
                       (Map.insert procedure f generatedProcedures)
  where spawned              = Map.keysSet $ Map.unions [ spawned | Generated _ _ spawned _      <- Map.elems generatedProcedures ]
        called               = Map.keysSet $ Map.unions [ called  | Generated _ _ _       called <- Map.elems generatedProcedures ]
        varsAvailable        = Map.unionsWith (∩)       [ spawned | Generated _ _ spawned _      <- Map.elems generatedProcedures ]
        varsAvailableCalls   = Map.unionsWith (∩)       [ called  | Generated _ _ _       called <- Map.elems generatedProcedures ]
        threadsGenerated     = Map.keysSet generated
        proceduresGenerated  = Map.keysSet generatedProcedures
        toGenerate           = spawned ∖ threadsGenerated
        toGenerateProcedures = called ∖ proceduresGenerated

        inChannels       = Set.fromList [stdIn,lowIn1]
        outChannels      = Set.fromList [stdOut]
        vars             = Set.map Global $
                           Set.fromList ["x", "y", "z", "a", "b", "c"]
        varsForbidden    = Set.fromList []


instance Arbitrary GeneratedProgram where
  arbitrary = sized $ \n -> do
      f@(Generated p _ spawned called) <- forGenerator inChannels
                                                       outChannels
                                                       vars
                                                       varsAvailable
                                                       varsForbidden
                                                       threadsAvailable
                                                       proceduresAvailable
                                                       n
      (generated, generatedProcedures) <- programGenerator n
                                    ((threadsAvailable ∖ (Map.keysSet spawned)) ∖ (Set.fromList [1]))
                                    proceduresAvailable
                                    (Map.fromList [(1, "main")])
                                    (Map.fromList [("main", f)])
      return $ GeneratedProgram generated generatedProcedures
    where
      threadsAvailable = Set.fromList [2,3]
      proceduresAvailable = Set.fromList ["foo", "bar", "baz", "procF", "procH", "procG"]
      inChannels       = Set.fromList [stdIn,lowIn1]
      outChannels      = Set.fromList [stdOut]
      vars             = Set.map Global $
                         Set.fromList ["x", "y", "z", "a", "b", "c"]
      varsForbidden    = Set.fromList []
      varsAvailable    = Set.fromList []



instance Arbitrary SimpleProgram where
  arbitrary = sized $ \n -> do
      f@(Generated p vars spawned called) <- forGenerator inChannels
                                                          outChannels
                                                          vars
                                                          varsAvailable
                                                          varsForbidden
                                                          threadsAvailable
                                                          proceduresAvailable
                                                          n
      return $ SimpleProgram (Map.fromList [(1,"main")]) (Map.fromList [("main", Generated (Skip `Seq` p) vars spawned called)])
    where
      threadsAvailable = Set.fromList []
      proceduresAvailable = Set.fromList []
      inChannels       = Set.fromList []
      outChannels      = Set.fromList []
      vars             = Set.map Global $
                         Set.fromList ["x", "y", "z", "h"]
      varsForbidden    = Set.fromList []
      varsAvailable    = vars

instance DynGraph gr => Arbitrary (SimpleCFG gr) where
  arbitrary = sized $ \n -> do
      simple  <- resize n arbitrary
      let p = toProgramSimple simple
      return $ SimpleCFG (nmap (const ()) $ emap (const ()) $ tcfg p)

instance Arbitrary IntraGeneratedProgram where
  arbitrary = sized $ \n -> do
      f@(Generated p _ spawned called) <- forGenerator inChannels
                                                       outChannels
                                                       vars
                                                       varsAvailable
                                                       varsForbidden
                                                       threadsAvailable
                                                       proceduresAvailable
                                                       n
      (generated, generatedProcedures) <- programGenerator n
                                    ((threadsAvailable ∖ (Map.keysSet spawned)) ∖ (Set.fromList [1]))
                                    proceduresAvailable
                                    (Map.fromList [(1, "main")])
                                    (Map.fromList [("main", f)])
      return $ IntraGeneratedProgram generated generatedProcedures
    where
      threadsAvailable = Set.fromList [2,3]
      proceduresAvailable = Set.fromList []
      inChannels       = Set.fromList [stdIn,lowIn1]
      outChannels      = Set.fromList [stdOut]
      vars             = Set.map Global $
                         Set.fromList ["x", "y", "z", "a", "b", "c"]
      varsForbidden    = Set.fromList []
      varsAvailable    = Set.fromList []






toProgramSimple :: DynGraph gr => SimpleProgram -> Program gr
toProgramSimple (SimpleProgram forThreads forProcedures) = toProgram (GeneratedProgram forThreads forProcedures)

toProgramIntra :: DynGraph gr => IntraGeneratedProgram -> Program gr
toProgramIntra (IntraGeneratedProgram forThreads forProcedures) = toProgram (GeneratedProgram forThreads forProcedures)

toProgram :: DynGraph gr => GeneratedProgram -> Program gr
toProgram generated = p { observability = defaultObservabilityMap (tcfg p) }
  where (codeThreads, codeProcedures) = toCode generated
        p    = compileAllToProgram codeThreads codeProcedures



instance DynGraph gr => Arbitrary (Program gr) where
  arbitrary = do
    generated <- arbitrary
    return $ toProgram generated


expGenerator :: Set Var -> Gen VarFunction
expGenerator varsAvailable
  | Set.null varsAvailable = elements $ fmap Val [-1,0,1,17,42]
  | otherwise              = frequency [
    (1, do x <- elements $ Set.toList varsAvailable
           y <- elements $ Set.toList varsAvailable
           return $ (Var x) `Times` (Var y)
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

forGenerator :: Set InputChannel -> Set OutputChannel -> Set Var -> Set Var -> Set Var -> Set StaticThread -> Set StaticProcedure -> Int -> Gen Generated
forGenerator inChannels outChannels vars varsAvailable varsForbidden threadsAvailable proceduresAvailable n
 | n > maxSize = forGenerator inChannels outChannels vars varsAvailable varsForbidden threadsAvailable proceduresAvailable maxSize
 | n <= 1      = frequency [
   (1,    return $ Generated (Skip)
                             (varsAvailable)
                             (Map.empty)
                             (Map.empty)
   ),
   (2, do var <- elements $ Set.toList (vars ∖ varsForbidden)
          exp <- expGenerator varsAvailable
          return $ Generated (Ass var exp)
                             (varsAvailable ∪ Set.fromList [var])
                             (Map.empty)
                             (Map.empty)
   ),
   (if (Set.null inChannels) then 0 else 2,
       do channel <- elements $ Set.toList inChannels
          var     <- elements $ Set.toList (vars ∖ varsForbidden)
          return $ Generated (ReadFromChannel var channel)
                             (varsAvailable ∪ Set.fromList [var])
                             (Map.empty)
                             (Map.empty)
   ),
   (if (Set.null outChannels) then 0 else 2,
       do channel <- elements $ Set.toList outChannels
          exp     <- expGenerator varsAvailable
          return $ Generated (PrintToChannel  exp channel)
                             (varsAvailable)
                             (Map.empty)
                             (Map.empty)
   ),
   (if (Set.null threadsAvailable) then 0 else 1,
       do thread <- elements $ Set.toList threadsAvailable
          return $ Generated (SpawnThread thread)
                             (varsAvailable)
                             (Map.fromList [(thread, varsAvailable)])
                             (Map.empty)
   ),
   (if (Set.null proceduresAvailable) then 0 else 2,
       do procedure <- elements $ Set.toList proceduresAvailable
          return $ Generated (CallProcedure procedure)
                             (varsAvailable)
                             (Map.empty)
                             (Map.fromList [(procedure, varsAvailable)])
   )
   ]
 | otherwise   = frequency [
   (1, do m <- elements $  [1..2]
          Generated p'  varsAvailable' spawned' called' <- forGenerator inChannels outChannels vars varsAvailable varsForbidden                        threadsAvailable     proceduresAvailable (n-1)
          return $ Generated (ForC m p')
                             (if (m>0) then varsAvailable' else varsAvailable)
                             (spawned')
                             (called')
   ),
   (if (Set.null (varsAvailable ∖ varsForbidden)) then 0 else 1,
       do var <- elements $ Set.toList (varsAvailable ∖ varsForbidden)
          Generated p'               _ spawned' called' <- forGenerator inChannels outChannels vars varsAvailable (varsForbidden ∪ Set.fromList [var]) threadsAvailable     proceduresAvailable (n-1)
          return $ Generated (ForV var p')
                             (varsAvailable)
                             (spawned')
                             (called')
   ),
   (1, do bexp <- bexpGenerator varsAvailable
          Generated p'  varsAvailable'  spawned'  called'  <- forGenerator inChannels outChannels vars varsAvailable varsForbidden threadsAvailable                           proceduresAvailable (n-1)
          Generated p'' varsAvailable'' spawned'' called'' <- forGenerator inChannels outChannels vars varsAvailable varsForbidden (threadsAvailable ∖ Map.keysSet spawned')  proceduresAvailable (n-1)
          return $ Generated (If bexp p' p'')
                             (varsAvailable' ∩ varsAvailable'')
                             (spawned' `Map.union` spawned'')
                             (Map.unionsWith (∩) [ called', called'' ])
   ),
   (3, do Generated p'  varsAvailable'  spawned'  called'  <- forGenerator inChannels outChannels vars varsAvailable  varsForbidden threadsAvailable                          proceduresAvailable (n-1)
          Generated p'' varsAvailable'' spawned'' called'' <- forGenerator inChannels outChannels vars varsAvailable' varsForbidden (threadsAvailable ∖ Map.keysSet spawned') proceduresAvailable (n-1)
          return $ Generated (p' `Seq`p'')
                             (varsAvailable'')
                             (spawned' `Map.union` spawned'')
                             (Map.unionsWith (∩) [ called', called'' ])
   )
   ]
 where maxSize = 5

{- randomly pick n elements out of a given list, without repetition -}
pick :: Eq a => Int -> [a] -> Gen [a]
pick 0 list = return []
pick n list = do x <- elements list
                 picked <- pick (n-1) (list \\ [x])
                 return (x:picked)

