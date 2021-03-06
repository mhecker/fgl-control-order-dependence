{-# LANGUAGE NamedFieldPuns #-}
module PNI where


import IRLSOD

import Program
import Execution

import Unicode

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph

import Control.Monad(forM_)
import Control.Monad.Random

import Debug.Trace

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.List (groupBy,sortBy,nub)
import Data.Ord (comparing)

import Data.Set (Set)
import qualified Data.Set as Set

import Text.Printf (printf)


-- Probability of an execution under the uniform scheduler.
-- > 0 only for finished executions.
prob :: Graph gr => gr CFGNode CFGEdge -> ExecutionTrace -> Rational
prob gr [] = 1
prob gr (((control,globalσ,tlσs,i), o, (control',globalσ',tlσs',i')) : trace)
    | length successors /= length control   = error "nicht genau ein nachfolgezustand pro thread" -- TODO: genauer reingucken, obs wirklich für jeden Thread genau einen gibt
    | ((o,(control',globalσ',tlσs')) ∊ successors) = (1 / toRational (length successors) ) * prob gr trace
    | otherwise                             = 0
  where successors = [(o,(control,globalσ,tlσs)) | (o,(control,globalσ,tlσs,i)) <- eventStep gr (control,globalσ,tlσs,i)]


{- Probabilistich Noninteference -}
probability :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> [(Rational,ExecutionTrace)] -> ExecutionTrace -> Rational
probability graph obs executions e = sum $ [ p' | (p',e') <- executions, let (t,t') = (toTrace e, toTrace e'),
                                                  t ∼ t' ]
  where (∼) = (≈) graph obs Low

secureWithRegardTo :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> [ExecutionTrace] -> [ExecutionTrace] -> Bool
secureWithRegardTo graph obs θ θ' =
      (∀) (θ ++ θ') (\e -> p e == p' e)
  where p  = probability graph obs [(prob graph e,e) | e <- θ ]
        p' = probability graph obs [(prob graph e,e) | e <- θ']


pniFor :: Graph gr => Program gr -> Input -> Input -> Bool
pniFor program@(Program { tcfg, observability }) i i' = secureWithRegardTo tcfg observability θ θ'
  where θ  = allFinishedExecutionTraces program i
        θ' = allFinishedExecutionTraces program i'



{- Probabilistic noninteference, somewhat more efficient implementation that precomputes probabilities for all occuring equivalence classes -}
pniForEquiv :: Graph gr => Program gr -> Input -> Input -> Bool
pniForEquiv program@(Program { tcfg, observability }) i i' = secureWithRegardToEquiv tcfg observability θ θ'
  where θ  = allFinishedExecutionTraces program i
        θ' = allFinishedExecutionTraces program i'


secureWithRegardToEquiv :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> [ExecutionTrace] -> [ExecutionTrace] -> Bool
secureWithRegardToEquiv graph obs θ θ' =
      (∀) (θ ++ θ') (\e -> p e == p' e)
  where tLow e = observable graph obs Low (toTrace e)
        p  e = Map.findWithDefault 0 (tLow e) equiv
        p' e = Map.findWithDefault 0 (tLow e) equiv'

        equiv  = equivClasses graph obs θ
        equiv' = equivClasses graph obs θ'


equivClasses :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification ->  [ExecutionTrace] -> Map Trace Rational
equivClasses graph obs θ = foldr newEquivClassMember Map.empty θ
  where newEquivClassMember e classes = Map.insertWith (+) t p classes
           where p = prob graph e
                 t = observable graph obs Low (toTrace e)



{- Probabilistic noninteference, somewhat more efficient implementation that precomputes probabilities for all occuring equivalence classes,
   and shared probability computation -}
pniForEquivAnnotated :: Graph gr => Program gr -> Input -> Input -> Bool
pniForEquivAnnotated program@(Program { tcfg, observability }) i i' = secureWithRegardToEquivAnnotated tcfg observability θ θ'
  where θ  = allFinishedAnnotatedExecutionTraces program i
        θ' = allFinishedAnnotatedExecutionTraces program i'


secureWithRegardToEquivAnnotated :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> [AnnotatedExecutionTrace] -> [AnnotatedExecutionTrace] -> Bool
secureWithRegardToEquivAnnotated graph obs θ θ' =
      (∀) (θ ++ θ') (\(e,_) -> p e == p' e)
  where tLow e = observable graph obs Low (toTrace e)
        p  e = Map.findWithDefault 0 (tLow e) equiv
        p' e = Map.findWithDefault 0 (tLow e) equiv'

        equiv  = equivClassesAnnotated graph obs θ
        equiv' = equivClassesAnnotated graph obs θ'


equivClassesAnnotated :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification ->  [AnnotatedExecutionTrace] -> Map Trace Rational
equivClassesAnnotated graph obs θ = foldr newEquivClassMember Map.empty θ
  where newEquivClassMember (e,p) classes = Map.insertWith (+) t p classes
           where t = observable graph obs Low (toTrace e)




{- Counterexamples to PNI -}
showCounterExamplesPniFor program i i' = do
  showInputs i i'
  showCounterExamples $ counterExamplesPniFor program i i'

counterExamplesWithRegardTo :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> [ExecutionTrace] -> [ExecutionTrace] -> [(Rational,Rational,Trace)]
counterExamplesWithRegardTo graph obs θ θ' =
      nub $ [ (p e,p' e, observable graph obs Low (toTrace e)) | e <- (θ ++ θ'), p e /= p' e]
  where p  = probability graph obs [(prob graph e,e) | e <- θ ]
        p' = probability graph obs [(prob graph e,e) | e <- θ']


counterExamplesPniFor :: Graph gr => Program gr -> Input -> Input -> [(Rational,Rational,Trace)]
counterExamplesPniFor program@(Program { tcfg, observability }) i i' = counterExamplesWithRegardTo tcfg observability θ θ'
  where θ  = allFinishedExecutionTraces program i
        θ' = allFinishedExecutionTraces program i'


{- Counterexamples to PNI, using pre-computed probabilities for occuring equivalence classes -}
counterExamplesWithRegardToEquiv :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> [ExecutionTrace] -> [ExecutionTrace] -> [(Rational,Rational,Trace)]
counterExamplesWithRegardToEquiv graph obs θ θ' =
      nub $ [ (p e,p' e, tLow e) | e <- (θ ++ θ'), p e /= p' e]
  where tLow e  = observable graph obs Low (toTrace e)
        p  e = Map.findWithDefault 0 (tLow e) equiv
        p' e = Map.findWithDefault 0 (tLow e) equiv'
        equiv  = equivClasses graph obs θ
        equiv' = equivClasses graph obs θ'


counterExamplesPniForEquiv :: Graph gr => Program gr -> Input -> Input -> [(Rational,Rational,Trace)]
counterExamplesPniForEquiv program@(Program { tcfg, observability }) i i' = counterExamplesWithRegardToEquiv tcfg observability θ θ'
  where θ  = allFinishedExecutionTraces program i
        θ' = allFinishedExecutionTraces program i'



{- Counterexamples to PNI, using pre-computed probabilities for occuring equivalence classes, and shared probability computation -}
counterExamplesWithRegardToEquivAnnotatedIf :: Graph gr => (Rational -> Rational -> Bool) -> gr CFGNode CFGEdge -> ObservationalSpecification -> [AnnotatedExecutionTrace] -> [AnnotatedExecutionTrace] -> [(Rational,Rational,Trace)]
counterExamplesWithRegardToEquivAnnotatedIf pred graph obs θ θ' =
      nub $ [ (pe, p'e, tLow e) | (e,_) <- (θ ++ θ'), let pe = p e, let p'e = p' e, pred pe p'e]
  where tLow e  = observable graph obs Low (toTrace e)
        p  e = Map.findWithDefault 0 (tLow e) equiv
        p' e = Map.findWithDefault 0 (tLow e) equiv'
        equiv  = equivClassesAnnotated graph obs θ
        equiv' = equivClassesAnnotated graph obs θ'


counterExamplesWithRegardToEquivAnnotated :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> [AnnotatedExecutionTrace] -> [AnnotatedExecutionTrace] -> [(Rational,Rational,Trace)]
counterExamplesWithRegardToEquivAnnotated = counterExamplesWithRegardToEquivAnnotatedIf (/=)


counterExamplesPniForEquivAnnotated :: Graph gr => Program gr -> Input -> Input -> [(Rational,Rational,Trace)]
counterExamplesPniForEquivAnnotated program@(Program { tcfg, observability }) i i' =
        fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotated tcfg observability θ θ'
  where θ  = allFinishedAnnotatedExecutionTraces program i
        θ' = allFinishedAnnotatedExecutionTraces program i'

counterExamplesPniForEquivAnnotatedSampled :: Graph gr => Program gr -> Input -> Input -> [(Rational,Rational,Trace)]
counterExamplesPniForEquivAnnotatedSampled program@(Program { tcfg, observability }) i i' =
        fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotated tcfg observability θ θ'
  where θ  = allFinishedAnnotatedExecutionTraces program i
        θ' = allFinishedAnnotatedExecutionTraces program i'


showInputs i i' = do
  putStrLn $ "i  = " ++ (show $ fmap (take 5) i ) ++ " ...     "  ++
             "i' = " ++ (show $ fmap (take 5) i') ++ " ... "

showCounterExamples :: [(Rational,Rational,Trace)] -> IO ()
showCounterExamples counterExamples  =
  forM_ counterExamples (\(p,p',trace) -> do
     putStrLn "-----------------"
     putStrLn $ "p  = " ++ (show p ) ++ " ≃ " ++ (printf "%.5f" $ (fromRational p  :: Double)) ++ "                                  "  ++
                "p' = " ++ (show p') ++ " ≃ " ++ (printf "%.5f" $ (fromRational p' :: Double))
     forM_ trace (\(σ, o, σ') -> do
        putStrLn $ show σ
        putStr   $ "---"
        putStr   $ show o
        putStrLn $ "-->"
        putStrLn $ show σ'
      )
    )


showCounterExamplesPniForEquiv program i i' = do
  showInputs i i'
  showCounterExamples $ counterExamplesPniForEquiv program i i'


showCounterExamplesPniForEquivAnnotated program i i' = do
  showInputs i i'
  showCounterExamples $ counterExamplesPniForEquivAnnotated program i i'

showCounterExamplesPniForEquivAnnotatedSampled program@(Program { tcfg, observability }) i i' = do
  showInputs i i'
  θ  <- evalRandIO $ sampleFinishedAnnotatedExecutionTraces 0.1 $ allFinishedAnnotatedExecutionTraces program i
  θ' <- evalRandIO $ sampleFinishedAnnotatedExecutionTraces 0.1 $ allFinishedAnnotatedExecutionTraces program i'
  let counterExamples =  fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotated tcfg observability θ θ'
  showCounterExamples counterExamples

showCounterExamplesPniForEquivAnnotatedSome n program@(Program { tcfg, observability }) i i' = do
  showInputs i i'
  θ  <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program i
  θ' <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces n program i'
  let counterExamples =  fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotatedIf areDifferent tcfg observability θ θ'
  showCounterExamples counterExamples
 where n' = fromInteger n
       areDifferent p p' =   abs(p-p') > 2/100


showCounterExamplesPniForEquivAnnotatedSomeWithConfidence nI program@(Program { tcfg, observability }) i i' = do
  showInputs i i'
  θ  <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces nI program i
  θ' <- evalRandIO $ someFinishedReversedAnnotatedExecutionTraces nI program i'
  let counterExamples =  fmap (\(p,p',trace) -> (p,p',reverse trace)) $ counterExamplesWithRegardToEquivAnnotatedIf areDifferent tcfg observability θ θ'
  showCounterExamples counterExamples
 where toString :: Rational -> String
       toString p = (printf "%.5f" $ (fromRational p  :: Double))
       -- True iff with (1-alpha) confidence, the observed trace has different probbability compaing input i with i'.
       areDifferent :: Rational -> Rational -> Bool
       areDifferent p p' = result --if result then traceShow ((n,toString p, toString p'), "   ", (printf "%.5f" c1 :: String, printf "%.5f" c2 :: String)) $ result else result
         where result = not $ c1 <= 0 && 0 <= c2
               n1 = n*p
               n0 = n - n1
               n1' = n * p'
               n0' = n - n1'
               s :: Double
               s  = sqrt $ fromRational $ (n1  * (1 - p ) * (1 - p )  +  n0  * p  * p ) / (n - 1)
               s' = sqrt $ fromRational $ (n1' * (1 - p') * (1 - p')  +  n0' * p' * p') / (n - 1)
               sx = sqrt $ ( (s * s / nD) + (s' * s' / nD))
               (c1,c2) = ( x - z*sx, x + z*sx)
                 where x = fromRational $ p - p' 
                       -- z = 0.43 -- alpha/2 = 0.33 ,   (1-alpha) = 0.33
                       -- z = 1.29 -- alpha/2 = 0.1  ,   (1-alpha) = 0.8
                       z    = 1.65 -- alpha/2 = 0.05,    (1-alpha) = 0.9
                       -- z = 1.96 -- alpha/2 = 0.025,   (1-alpha) = 0.95
                       -- z = 2.33 -- alpha/2 = 0.01 ,   (1-alpha) = 0.99
       n  = fromInteger nI
       nD = fromInteger nI



allOutcomes :: Graph gr => Program gr -> Input -> [(Rational,GlobalState)]
allOutcomes program@(Program { tcfg }) input = [ (prob tcfg trace, σ trace) | trace <- allFinishedExecutionTraces program input ]
   where σ    trace = last $ [ σ    | (_,_,(_,σ,_   ,_)) <- trace]


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
