{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Execution where

import IRLSOD
import Program

import System.Random
import Control.Monad.Random

import Control.Monad (liftM)

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad(forM_)

import Data.Graph.Inductive.Graph

initialConfiguration :: Graph gr => Program gr -> Input -> Configuration
initialConfiguration (Program { mainThread, entryOf, procedureOf }) input = ([(entryOf (procedureOf mainThread), [])], Map.empty, [Map.empty], input)


showAllFinalStates program input = do
  forM_ (allFinalStates program input) (\(ns,sigma,tlsigma) -> do
     putStrLn "-----------------"
     putStrLn $ show $ ns
     putStrLn $ show $ tlsigma
     putStrLn "-----------------"
   )

allFinalStates :: Graph gr => Program gr -> Input -> [(ControlState,GlobalState,ThreadLocalStates)]
allFinalStates program@(Program { tcfg }) input = iter [] [initialConfiguration program input]
  where iter finals []    = fmap hide finals
        iter finals confs = iter (newfinals++finals) $ concat $ fmap (step tcfg) confs
          where newfinals = [conf | conf <- confs, step tcfg conf == []]


showAllFinishedTraces program input = do
  forM_ (allFinishedTraces program input) (\trace -> do
     putStrLn "-----------------"
     forM_ trace (\(ns,globalσ,tlσ) -> do
        putStrLn $ show ns
        putStrLn $ show globalσ
        putStrLn $ show tlσ
        putStrLn $ ""
       )
    )


showAllFinishedExecutionTraces program input = do
  forM_ (allFinishedExecutionTraces program input) (\trace -> do
     putStrLn "-----------------"
     forM_ trace (\((ns,globalσ,tlσ,i),(n,e,index),(ns',globalσ',tlσ',i')) -> do
        putStrLn $ show ns
        putStrLn $ show globalσ
        putStrLn $ show tlσ
        putStr   $ "---"
        putStr   $ show (n,e,index)
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
                appendStep (c,e,c') cs ((n,e',index),c'')  = (c',(n,e',index),c''):(c,e,c'):cs


allFinishedTraces :: Graph gr => Program gr -> Input -> [[(ControlState,GlobalState, ThreadLocalStates)]]
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
                         appendStep ((n,e',index),c'')  = (c',(n,e',index),c''):t0
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



sample :: MonadRandom m => [t] -> m t
sample xs = do
  i <- getRandomR (1, length xs)
  return $ xs !! (i-1)

-- Although we return AnnotatedExecutionTraces just as in allFinishedAnnotatedExecutionTraces,
-- the meainig of the probability annotation is different: here, if a given execution is more likely than others,
-- it will also be sampled more often, and hence appear multiple times in the result, say: k times
-- The empirical probability such a trace is then k/n, and hence we annotate each occurence with p = 1/n,
-- which is more appropriate for functions like counterExamplesWithRegardToEquivAnnotated
someFinishedReversedAnnotatedExecutionTraces :: (MonadRandom m, Graph gr) => Integer -> Program gr -> Input -> m [AnnotatedExecutionTrace]
someFinishedReversedAnnotatedExecutionTraces n program@(Program { tcfg }) input = sampleSome [] 0
  where initialTraces  =  [ [(initialConfiguration program input, e, c')] | (e,c') <- initialSteps ]
        initialSteps   = eventStep tcfg $ initialConfiguration program input
        p              = 1 / (toRational n)
        sampleSome sampled i
          | i >= n            = return $ fmap (,p) sampled
          | otherwise         = do
              t0 <- sample initialTraces
              newTrace <- sampleTrace t0
              sampleSome (newTrace:sampled) (i+1)
        sampleTrace t0@((c,e,c'):cs)
          | finished  = return t0
          | otherwise = do
               ((n,e',index),c'') <- sample successors
               sampleTrace ((c',(n,e',index),c''):t0)
         where finished   = successors == []
               successors = eventStep tcfg c'

someFinishedAnnotatedExecutionTraces :: (MonadRandom m, Graph gr) => Integer -> Program gr -> Input -> m [AnnotatedExecutionTrace]
someFinishedAnnotatedExecutionTraces n p i = liftM (fmap (\(t,p) -> (reverse t,p))) $  someFinishedReversedAnnotatedExecutionTraces n p i

showSomeFinishedExecutionTraces program input n = do
  traces <- evalRandIO $ someFinishedAnnotatedExecutionTraces n program input
  forM_ traces (\(trace,q) -> do
     putStrLn "-----------------"
     forM_ trace (\((ns,globalσ,tlσ,i),(n,e,index),(ns',globalσ',tlσ',i')) -> do
        putStrLn $ show ns
        putStrLn $ show globalσ
        putStrLn $ show tlσ
        putStr   $ "---"
        putStr   $ show (n,e,index)
        putStrLn $ "-->"
        putStrLn $ ""
       )
    )
