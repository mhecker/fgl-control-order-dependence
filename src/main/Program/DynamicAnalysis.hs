{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Program.DynamicAnalysis where


import System.IO.Unsafe (unsafePerformIO)
import Control.Exception.Base (assert)
import Control.Monad.Random (evalRandIO, MonadRandom(..))
import Debug.Trace (traceShow)

import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.List as List


-- import Data.Vector.Generic
import Data.Vector (Vector)
import qualified Data.Vector as Vector



-- import Statistics.Distribution
-- import Statistics.Distribution.ChiSquared
-- import Statistics.Test.ChiSquared

import Statistics.Test.Types (TestResult(..))

import Data.Graph.Inductive.Graph

import Statistics (gtest, gtestViaChi2, wellektest, wellektestSignificantDifference, mytestSignificantDifference, plunketttest)
import Statistics.Test.ChiSquared (chi2test)

import Unicode
import IRLSOD(Trace, ExecutionTrace, Input, eventStep, eventStepAt, toTrace, SecurityLattice (..), observable)
import Execution (someFinishedReversedAnnotatedExecutionTraces, sample, initialConfiguration)
import PNI (counterExamplesWithRegardToEquivAnnotatedIf)

import Program.Defaults
import Program


isSecureEmpiricallyMyOwnSuckyOldTest program@(Program { tcfg, observability }) = unsafePerformIO $ do
  θ  <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program defaultInput
  θ' <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program defaultInput'
  let counterExamples =  fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotatedIf areDifferent tcfg observability θ θ'
  return $ length counterExamples == 0
 where areDifferent p p' =   abs(p-p') > 2/100
       n = 7500


type ID = Int
type Count = Integer

isSecureEmpiricallyCombinedTest :: Graph gr => Program gr -> Bool
isSecureEmpiricallyCombinedTest program@(Program { tcfg, observability }) = unsafePerformIO $ evalRandIO $ test (0, 0, Map.empty, Map.empty, Map.empty)
  where α = 0.0000001
        ε = 0.01
        nMin = 1000
        nDelta = 1000
        
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
            e  <- newExecutionTrace defaultInput
            e' <- newExecutionTrace defaultInput'
            let t  = observable tcfg observability Low $ toTrace e
            let t' = observable tcfg observability Low $ toTrace e'
          
            let (knownId,  toId' ) = Map.insertLookupWithKey useKnown t  nextId   toId
            let (id, nextId'  ) = case knownId  of { Nothing -> (nextId , nextId  + 1) ; Just id -> (id, nextId ) }

            let (knownId', toId'') = Map.insertLookupWithKey useKnown t' nextId'  toId'
            let (id', nextId'') = case knownId' of { Nothing -> (nextId', nextId' + 1) ; Just id -> (id, nextId') }

            newSamplePairs (k-1) (n+1, nextId'', toId'', Map.insertWith (+) id 1 θs, Map.insertWith (+) id' 1 θ's)

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
          let ok (x,y0) = let y = round y0 in  (x >= 3 ∨ y >= 3 ∨ x == y)
          let allGt5 = (∀) vLeft ok
          let gt5CounterExamples = List.sortBy (comparing (\(x,y) -> max (fromIntegral x) y)) $ Vector.toList $ Vector.filter (not . ok) vLeft
          let tsCounterExamples = if n < nMin then id else let { l1 = length gt5CounterExamples ; l2 =  Vector.length vLeft } in traceShow (l1, l2, fromIntegral l1 / fromIntegral l2 :: Double, take 10 gt5CounterExamples)
          let evidenceThatObservationsAreDifferent = assert (left == right) $ left
                where left  = plunketttest α vLeft
                      right = plunketttest α vRight
          let evidenceThatObservationsAreWithinEpsilonDistance = if left == right then left else NotSignificant
                where left  = wellektest ε α vLeft
                      right = wellektest ε α vRight

          let ts b = traceShow ("Finished:  ", n, b, θs, θ's) b

          if (n < nMin) ∨ (evidenceThatObservationsAreDifferent == NotSignificant  ∧   evidenceThatObservationsAreWithinEpsilonDistance == NotSignificant) then do
            state' <- newSamplePairs nDelta state
            test state'
          else if (evidenceThatObservationsAreDifferent ==    Significant  ∧  evidenceThatObservationsAreWithinEpsilonDistance == NotSignificant) then
            return $ ts $ False
          else if (evidenceThatObservationsAreDifferent == NotSignificant  ∧  evidenceThatObservationsAreWithinEpsilonDistance ==    Significant) then
            return $ ts $ True
          else 
            return
              $ assert ( evidenceThatObservationsAreDifferent == Significant  ∧  evidenceThatObservationsAreWithinEpsilonDistance == Significant)
              $ error "Tests are contradictory, wtf."

isSecureEmpirically :: Graph gr => Program gr -> Bool
isSecureEmpirically = isSecureEmpiricallyCombinedTest

