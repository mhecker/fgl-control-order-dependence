{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Program.DynamicAnalysis where



import System.IO.Unsafe (unsafePerformIO)
import Control.DeepSeq (deepseq)
import Control.Exception.Base (assert)
import Control.Monad.Random (evalRandIO, MonadRandom(..))
import Debug.Trace (traceShow)

import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set


import qualified Data.List as List


import Data.Vector (Vector)
import qualified Data.Vector as Vector

import Statistics.Test.Types (TestResult(..))

import Data.Graph.Inductive.Graph

import Statistics (wellektest, plunketttest)

import Unicode
import IRLSOD(Trace, ExecutionTrace, Input, eventStep, eventStepAt, toTrace, SecurityLattice (..), observable, Input)
import Execution (someFinishedReversedAnnotatedExecutionTraces, sample, initialConfiguration, someFinishedReversedObservations)
import PNI (counterExamplesWithRegardToEquivAnnotatedIf)

import Program.Defaults
import Program


isSecureEmpiricallyMyOwnSuckyOldTest program@(Program { tcfg, observability }) input input' = unsafePerformIO $ do
  θ  <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program input
  θ' <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program input'
  let counterExamples =  fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotatedIf areDifferent tcfg observability θ θ'
  return $ length counterExamples == 0
 where areDifferent p p' =   abs(p-p') > 2/100
       n = 7500

isLSODEmpirically program@(Program { tcfg, observability }) = unsafePerformIO $ do
  θobs  <- evalRandIO $ someFinishedReversedObservations n program defaultInput
  θ'obs <- evalRandIO $ someFinishedReversedObservations n program defaultInput'
  return $
       (Set.size θobs ) == 1
     ∧ (Set.size θ'obs) == 1
     ∧ θobs == θ'obs
 where n = 2048


type ID = Int
type Count = Integer

isSecureEmpiricallyCombinedTest :: Graph gr => Program gr -> Input -> Input -> Bool
isSecureEmpiricallyCombinedTest program@(Program { tcfg, observability }) input input' = unsafePerformIO $ evalRandIO $ test (0, 0, Map.empty, Map.empty, Map.empty)
  where α = 0.0000001
        ε = 0.009
        nMin = 4096
        
        newExecutionTrace :: MonadRandom m => Input -> m ExecutionTrace
        newExecutionTrace input = do
            e0 <- sample initialTraces
            sampleTrace e0
          where initialTraces  =  [ [(initialConfiguration program input, e, c')] | (e,c') <- initialSteps ]
                initialSteps   = eventStep tcfg $ initialConfiguration program input

                sampleTrace :: MonadRandom m => ExecutionTrace -> m ExecutionTrace
                sampleTrace e0@((c,e,c'):cs)
                  | finished  = return e0
                  | otherwise = do
                      index0 <- getRandomR (1, length ns)
                      let (event,c'') = eventStepAt (index0 - 1) tcfg c'
                      sampleTrace ((c',event,c''):e0)
                  where finished = List.null ns
                        (ns,_,_,_) = c'


        newSamplePairs :: MonadRandom m => Integer -> (Integer, ID, Map Trace ID, Map ID Count , Map ID Count) -> m (Integer, ID, Map Trace ID, Map ID Count , Map ID Count)
        newSamplePairs 0 state = return state
        newSamplePairs k (n, nextId, toId, θs, θ's) = do
            e  <- newExecutionTrace input
            e' <- newExecutionTrace input'
            let t  = observable tcfg observability Low $ toTrace e
            let t' = observable tcfg observability Low $ toTrace e'
          
            let (knownId,  toId' ) = Map.insertLookupWithKey useKnown t  nextId   toId
            let (id, nextId'  ) = case knownId  of { Nothing -> (nextId , nextId  + 1) ; Just id -> (id, nextId ) }

            let (knownId', toId'') = Map.insertLookupWithKey useKnown t' nextId'  toId'
            let (id', nextId'') = case knownId' of { Nothing -> (nextId', nextId' + 1) ; Just id -> (id, nextId') }
            let state' = (n+1, nextId'', toId'', Map.insertWith (+) id 1 θs, Map.insertWith (+) id' 1 θ's)

            if (k `mod` 1024 == 0) then
               state' `deepseq` newSamplePairs (k-1) state'
            else
                                newSamplePairs (k-1) state'

        useKnown  _ _ known = known

        gen ::  Map ID Count -> Map ID Count -> ID -> (Int, Double)
        gen θs θ's id = (
            fromInteger  $ Map.findWithDefault 0 id θs,
            fromIntegral $ Map.findWithDefault 0 id θ's
          )

        test :: MonadRandom m => (Integer, ID, Map Trace ID, Map ID Count , Map ID Count) -> m Bool
        test state@(n, nextId, toId, θs, θ's) = do

          let vLeft  = assert (nextId == Map.size toId) $ Vector.generate (Map.size toId) $ gen θs  θ's
          let vRight = assert (nextId == Map.size toId) $ Vector.generate (Map.size toId) $ gen θ's θs 
          let evidenceThatObservationsAreDifferent = assert (left == right) $ left
                where left  = plunketttest α vLeft
                      right = plunketttest α vRight
          let evidenceThatObservationsAreWithinEpsilonDistance = if left == right then left else NotSignificant
                where left  = wellektest ε α vLeft
                      right = wellektest ε α vRight

          let ts b = traceShow ("Finished:  ", n, b, take 8 $ Map.assocs $ θs, take 8 $ Map.assocs $ θ's) b

          if (n < nMin) ∨ (evidenceThatObservationsAreDifferent == NotSignificant  ∧   evidenceThatObservationsAreWithinEpsilonDistance == NotSignificant) then do
            state' <- newSamplePairs (max nMin n) state
            test state'
          else if (evidenceThatObservationsAreDifferent ==    Significant  ∧  evidenceThatObservationsAreWithinEpsilonDistance == NotSignificant) then
            return $ False
          else if (evidenceThatObservationsAreDifferent == NotSignificant  ∧  evidenceThatObservationsAreWithinEpsilonDistance ==    Significant) then
            return $ True
          else 
            return
              $ assert ( evidenceThatObservationsAreDifferent == Significant  ∧  evidenceThatObservationsAreWithinEpsilonDistance == Significant)
              $ error ("Tests are contradictory, wtf:" ++ show (n, θs, θ's))

isSecureEmpirically :: Graph gr => Program gr -> Bool
isSecureEmpirically p = isSecureEmpiricallyCombinedTest p defaultInput defaultInput'

isSecureEmpiricallyFor  :: Graph gr => Program gr -> Input -> Input -> Bool
isSecureEmpiricallyFor = isSecureEmpiricallyCombinedTest

