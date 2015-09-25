{-# LANGUAGE NamedFieldPuns #-}
module PNI where


import IRLSOD
import ListUnicode

import Program
import Execution

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph

import Control.Monad(forM_)


-- import Data.Map ( Map, (!) )
-- import qualified Data.Map as Map
import Data.List (groupBy,sortBy,nub)
import Data.Ord (comparing)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode

import Text.Printf (printf)


-- [(Configuration, (Node,Event), Configuration)]
prob :: Graph gr => gr CFGNode CFGEdge -> ExecutionTrace -> Rational
prob gr [] = 1
prob gr (((control,σ,i), o, (control',σ',i')) : trace)
    | length successors /= length control = error "nicht genau ein nachfolgezustand pro thread" -- TODO: genauer reingucken, obs wirklich für jeden Thread genau einen gibt
    | otherwise                           = ( (if ((o,(control',σ')) `elem` successors) then 1 else 0) /
                                              toRational (length successors) )
                                            * prob gr trace
  where successors = [(o,(control,σ)) | (o,(control,σ,i)) <- eventStep gr (control,σ,i)]


probability :: Graph gr => gr CFGNode CFGEdge -> ProgramClassification -> [ExecutionTrace] -> ExecutionTrace -> Rational
probability graph cl executions e = sum $ [ prob graph e' | e' <- executions, let (t,t') = (toTrace e, toTrace e'),
                                                            t ∼ t' ]
  where (∼) = (≈) graph cl Low

secureWithRegardTo :: Graph gr => gr CFGNode CFGEdge -> ProgramClassification -> [ExecutionTrace] -> [ExecutionTrace] -> Bool
secureWithRegardTo graph cl θ θ' =
      (∀) (θ ++ θ') (\e -> p e == p' e)
  where p  = probability graph cl θ
        p' = probability graph cl θ'


pniFor :: Graph gr => Program gr -> Input -> Input -> Bool
pniFor program@(Program { tcfg, clInit }) i i' = secureWithRegardTo tcfg clInit θ θ'
  where θ  = allFinishedExecutionTraces program i
        θ' = allFinishedExecutionTraces program i'



showCounterExamplesPniFor program i i' = do
  putStrLn $ "i  = " ++ (show $ fmap (take 5) i ) ++ " ...     "  ++
             "i' = " ++ (show $ fmap (take 5) i') ++ " ... "
  forM_ (counterExamplesPniFor program i i') (\(p,p',trace) -> do
     putStrLn "-----------------"
     putStrLn $ "p  = " ++ (show p ) ++ " ≃ " ++ (printf "%.5f" $ (fromRational p  :: Double)) ++ "                                  "  ++
                "p' = " ++ (show p') ++ " ≃ " ++ (printf "%.5f" $ (fromRational p' :: Double))
--     forM_ execution (\((σ,i),(n,e),(ns',σ',i')) -> do
     forM_ trace (\(σ, o, σ') -> do
        putStrLn $ show σ
        putStr   $ "---"
        putStr   $ show o
        putStrLn $ "-->"
        putStrLn $ show σ'
      )
    )

counterExamplesWithRegardTo :: Graph gr => gr CFGNode CFGEdge -> ProgramClassification -> [ExecutionTrace] -> [ExecutionTrace] -> [(Rational,Rational,Trace)]
counterExamplesWithRegardTo graph cl θ θ' =
      nub $ [ (p e,p' e, observable graph cl Low (toTrace e)) | e <- (θ ++ θ'), p e /= p' e]
  where p  = probability graph cl θ
        p' = probability graph cl θ'


counterExamplesPniFor :: Graph gr => Program gr -> Input -> Input -> [(Rational,Rational,Trace)]
counterExamplesPniFor program@(Program { tcfg, clInit }) i i' = counterExamplesWithRegardTo tcfg clInit θ θ'
  where θ  = allFinishedExecutionTraces program i
        θ' = allFinishedExecutionTraces program i'



allOutcomes :: Graph gr => Program gr -> Input -> [(Rational,GlobalState)]
allOutcomes program@(Program { tcfg }) input = [ (prob tcfg trace, σ trace) | trace <- allFinishedExecutionTraces program input ]
   where σ trace = last $ [ σ | (_,_,(_,σ,_)) <- trace]


allOutcomesGrouped :: Graph gr => Program gr -> Input -> [(Rational,GlobalState)]
allOutcomesGrouped program input =
    [ (sum $ fmap fst outcome,
       snd $ head $ outcome)
    | outcome <- groupBy (\(p,σ) (p',σ') -> σ == σ') $ sortBy (comparing snd) outcomes
    ]
 where outcomes = allOutcomes program input



showAllOutcomes program input = do
  forM_ (allOutcomes program input) (\(p, σ) -> do
      putStrLn $ show p
      putStrLn $ show σ
      putStrLn $ ""
   )

showAllOutcomesGrouped program input = do
  forM_ (allOutcomesGrouped program input) (\(p, σ) -> do
      putStrLn $ show p
      putStrLn $ show σ
      putStrLn $ ""
   )
