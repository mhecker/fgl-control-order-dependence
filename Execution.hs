{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Execution where


import IRLSOD
import Program

import System.Random
import Control.Monad.Random

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad(forM_)

import Data.Graph.Inductive.Graph

initialConfiguration :: Graph gr => Program gr -> Input -> Configuration
initialConfiguration (Program { mainThread, entryOf }) input = ([entryOf mainThread], Map.empty, input)


showAllFinalStates program input = do
  forM_ (allFinalStates program input) (\(ns,sigma) -> do
     putStrLn "-----------------"
     putStrLn $ show $ ns
     putStrLn $ show $ sigma
     putStrLn "-----------------"
   )

allFinalStates :: Graph gr => Program gr -> Input -> [(ControlState,GlobalState)]
allFinalStates program@(Program { tcfg }) input = iter [] [initialConfiguration program input]
  where iter finals []    = fmap hide finals
        iter finals confs = iter (newfinals++finals) $ concat $ fmap (step tcfg) confs
          where newfinals = [conf | conf <- confs, step tcfg conf == []]


showAllFinishedTraces program input = do
  forM_ (allFinishedTraces program input) (\trace -> do
     putStrLn "-----------------"
     forM_ trace (\(ns,σ) -> do
        putStrLn $ show ns
        putStrLn $ show σ
        putStrLn $ ""
       )
    )


showAllFinishedExecutionTraces program input = do
  forM_ (allFinishedExecutionTraces program input) (\trace -> do
     putStrLn "-----------------"
     forM_ trace (\((ns,σ,i),(n,e),(ns',σ',i')) -> do
        putStrLn $ show ns
        putStrLn $ show σ
        putStr   $ "---"
        putStr   $ show (n,e)
        putStrLn $ "-->"
        putStrLn $ ""
       )
    )

allFinishedExecutionTraces :: Graph gr => Program gr -> Input -> [ExecutionTrace]
allFinishedExecutionTraces program@(Program { tcfg }) input = fmap reverse $ iter [] [[(initialConfiguration program input, e, c')] | (e,c') <- eventStep tcfg $ initialConfiguration program input]
  where iter :: [ExecutionTrace] -> [ExecutionTrace] -> [ExecutionTrace]
        iter finished []     = finished
        iter finished traces = iter (newfinished++finished) $ concat $ fmap (\((c,e,c'):cs) -> fmap (appendStep (c,e,c') cs) (eventStep tcfg c') ) traces
          where newfinished = [ trace | trace@((c,e,c'):cs) <- traces, eventStep tcfg c' == []]
                appendStep (c,e,c') cs ((n,e'),c'')  = (c',(n,e'),c''):(c,e,c'):cs


allFinishedTraces :: Graph gr => Program gr -> Input -> [[(ControlState,GlobalState)]]
allFinishedTraces program@(Program { tcfg }) input = fmap reverse $ iter [] [[initialConfiguration program input]]
  where iter finished []     = fmap (fmap hide) finished
        iter finished traces = iter (newfinished++finished) $ concat $ fmap (\(c:cs) -> fmap (:(c:cs)) (step tcfg c)) traces
          where newfinished = [ trace | trace@(c:cs) <- traces, step tcfg c == []]



type AnnotatedExecutionTrace = (ExecutionTrace, Rational)

allFinishedAnnotatedExecutionTraces :: Graph gr => Program gr -> Input -> [AnnotatedExecutionTrace]
allFinishedAnnotatedExecutionTraces program@(Program { tcfg }) input = iter [] [ ([(initialConfiguration program input, e, c')],p) | (e,c') <- initialSteps ]
  where initialSteps = eventStep tcfg $ initialConfiguration program input
        p :: Rational
        p = 1 / (toRational $ length initialSteps)

        iter :: [AnnotatedExecutionTrace] -> [AnnotatedExecutionTrace] -> [AnnotatedExecutionTrace]
        iter finished []     = finished
        iter finished traces = iter (newfinished++finished) $ concat $ fmap appendAll traces
          where appendAll :: AnnotatedExecutionTrace -> [AnnotatedExecutionTrace]
                appendAll (t0@((c,e,c'):cs), p0) = fmap (\s -> (appendStep s, p0 * p)) successors
                   where p          = 1 / (toRational $ length successors)
                         successors = eventStep tcfg c'
                         appendStep ((n,e'),c'')  = (c',(n,e'),c''):t0
                newfinished = [ annTrace | annTrace@((c,e,c'):cs,p) <- traces, eventStep tcfg c' == []]

-- TODO: this is somewhat "left-biased", fix this
sampleFinishedAnnotatedExecutionTraces :: MonadRandom m => Rational -> [AnnotatedExecutionTrace] -> m [AnnotatedExecutionTrace]
sampleFinishedAnnotatedExecutionTraces pLimit traces = takeSome [] 0 traces
  where takeSome :: MonadRandom m =>  [AnnotatedExecutionTrace] -> Rational -> [AnnotatedExecutionTrace] -> m [AnnotatedExecutionTrace]
        takeSome sampled pSampled []
          | pSampled > pLimit = return sampled
          | otherwise         = takeSome sampled pSampled traces
        takeSome sampled pSampled ((aTrace@(t,pTrace)):traces)
          | pSampled > pLimit = return sampled
          | otherwise         = do
              q :: Double <- getRandomR (0,1)
              if q < 0.2 then takeSome (aTrace:sampled) (pSampled + pTrace) traces
                         else takeSome         sampled  (pSampled         ) traces

