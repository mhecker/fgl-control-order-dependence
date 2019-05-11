{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Program.DynamicAnalysis where


import System.IO.Unsafe (unsafePerformIO)
import Control.Exception.Base (assert)
import Control.Monad.Random (evalRandIO, MonadRandom(..))
import Debug.Trace (traceShow)


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

import Statistics (gtest, gtestViaChi2, wellektest)

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
isSecureEmpiricallyCombinedTest program@(Program { tcfg, observability }) = unsafePerformIO $ evalRandIO $ test 0 0 Map.empty Map.empty Map.empty
  where α = 0.000000001
        ε = 0.01
        
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

        useKnown  _ _ known = known

        gen ::  Map ID Count -> Map ID Count -> ID -> (Int, Double)
        gen θs θ's id = (
            fromInteger  $ Map.findWithDefault 0 id θs,
            fromIntegral $ Map.findWithDefault 0 id θ's
          )

        test :: MonadRandom m => Integer -> ID -> Map Trace ID -> Map ID Count -> Map ID Count -> m Bool
        test n nextId toId θs θ's = do

          let vLeft  = assert (nextId == Map.size toId) $ Vector.generate (Map.size toId) $ gen θs  θ's
          let vRight = assert (nextId == Map.size toId) $ Vector.generate (Map.size toId) $ gen θ's θs 
          let evidenceThatObservationsAreDifferent = assert (left == right) $ left
                -- where left  = chi2test α 0 vLeft
                --       right = chi2test α 0 vRight
                -- where left  = gtest vLeft
                --       right = gtest vRight
                where left  = gtestViaChi2 α 0 vLeft
                      right = gtestViaChi2 α 0 vRight
            
          let evidenceThatObservationsAreWithinEpsilonDistance = assert (left == right) $ left
                -- where left  = chi2test α 0 vLeft
                --       right = chi2test α 0 vRight
                -- where left  = gtest vLeft
                --       right = gtest vRight
                where left  = wellektest ε α vLeft
                      right = wellektest ε α vRight
          let ts = traceShow (θs, θ's)
          let ts = traceShow (toId, θs, θ's)
          let ts b = traceShow ("Finished:  ", n, b, θs, θ's) b
          let tsSome = if (n < 5) ∨ (n `mod` 100 == 0) then traceShow ("Sample: ", n) else id

          if (n < 20000) ∨ (evidenceThatObservationsAreDifferent == NotSignificant  ∧   evidenceThatObservationsAreWithinEpsilonDistance == NotSignificant) then do
            e  <- newExecutionTrace defaultInput
            e' <- newExecutionTrace defaultInput'
            let t  = observable tcfg observability Low $ toTrace e
            let t' = observable tcfg observability Low $ toTrace e'
          
            let (knownId,  toId' ) = Map.insertLookupWithKey useKnown t  nextId   toId
            let (id, nextId'  ) = case knownId  of { Nothing -> (nextId , nextId  + 1) ; Just id -> (id, nextId ) }

            let (knownId', toId'') = Map.insertLookupWithKey useKnown t' nextId'  toId'
            let (id', nextId'') = case knownId' of { Nothing -> (nextId', nextId' + 1) ; Just id -> (id, nextId') }
            let ts = traceShow (t, t')

            test (n+1) nextId'' toId'' (Map.insertWith (+) id 1 θs) (Map.insertWith (+) id' 1 θ's)
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

