module Statistics where

import Control.Exception.Base (assert)
import Debug.Trace (traceShow)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map


import Statistics.Distribution
import Statistics.Distribution.ChiSquared
import Statistics.Distribution.Normal (standard)
import Statistics.Test.ChiSquared

import Statistics.Function (square)
import Statistics.Test.Types (significant)

import Data.Vector (Vector, generate)
import qualified Data.Vector as Vector

wikipediaExample :: Vector (Int, Double)
wikipediaExample = generate 6 f
  where f 0 = ( 5, 10)
        f 1 = ( 8, 10)
        f 2 = ( 9, 10)
        f 3 = ( 8, 10)
        f 4 = (10, 10)
        f 5 = (20, 10)

wikipediaExample' :: Vector (Int, Double)
wikipediaExample' = generate 6 f
  where f 0 = ( 4, 10)
        f 1 = ( 7, 10)
        f 2 = ( 8, 10)
        f 3 = ( 7, 10)
        f 4 = ( 9, 10)
        f 5 = (25, 10)


wellekExample91 :: Vector (Int, Double)
wellekExample91 = generate 6 f
  where e = 100.0/6.0
        f 0 = (17, e)
        f 1 = (16, e)
        f 2 = (25, e)
        f 3 = ( 9, e)
        f 4 = (16, e)
        f 5 = (17, e)


fair :: Vector (Int, Double)
fair = generate 6 f
  where f 0 = (10, 10)
        f 1 = (10, 10)
        f 2 = (10, 10)
        f 3 = (10, 10)
        f 4 = (10, 10)
        f 5 = (10, 10)


fromListPair :: (Map Int Int, Map Int Int) -> Vector (Int, Double)
fromListPair (m1,m2) = assert (Map.size m1 == Map.size m2) $ generate (Map.size m1) f
  where f id = (m1 ! id, fromIntegral $ m2 ! id)


deterministic :: Int -> Vector (Int, Double)
deterministic n = generate 1 f
  where nn = fromIntegral n
        f 0 = (n, nn)



rofl :: Int -> Int -> Vector (Int, Double)
rofl k x = generate 2 f
  where f 0 = (x, fromIntegral $ x + k)
        f 1 = (k,0)




lol :: Vector (Int, Double)
lol = generate 2 f
  where f 0 = (35, 36)
        f 1 = (1,0)


lol' :: Vector (Int, Double)
lol' = generate 2 f
  where f 0 = (35, 37)
        f 1 = (2,0)

test = chi2test 0.05 0 wikipediaExample


infixl 7 *.
(*.) x y = if x == 0 then 0 else x * y


likelihood :: Vector (Int, Double) -> Double
likelihood rss = Vector.sum $ fmap f rs
  where rs = fmap (\(x,y) -> (fromIntegral x, y)) rss
        r = Vector.sum $ fmap fst $ rs
        s = Vector.sum $ fmap snd $ rs
        f (ri,si)  =  (  ri *. log ((ri / r) / ((ri+si)/(r+s)))  )
                   +  (  si *. log ((si / s) / ((ri+si)/(r+s)))  )

gtest :: Vector (Int, Double) -> TestResult
gtest rss
    | g > 2 * (fromIntegral dof) = Significant
    | otherwise                  = NotSignificant
  where dof = Vector.length rss - 1
        g = 2 * (likelihood rss)
        

-- | Generic form of G-Test for binned data. Data
--   sample is supplied in form of tuples (observed quantity,
--   expected number of events). Both must be positive.
gtestViaChi2 :: 
            Double              -- ^ p-value
         -> Int                 -- ^ Number of additional degrees of
                                --   freedom. One degree of freedom
                                --   is due to the fact that the are
                                --   N observation in total and
                                --   accounted for automatically.
         -> Vector (Int,Double) -- ^ Observation and expectation.
         -> TestResult
gtestViaChi2 p ndf vec
  | ndf < 0        = error $ "Statistics.Test.ChiSquare.gtestViaChi2: negative NDF " ++ show ndf
  | n   < 0        = error $ "Statistics.Test.ChiSquare.gtestViaChi2: too short data sample"
  | p > 0 && p < 1 = significant $ complCumulative d g < p
  | otherwise      = error $ "Statistics.Test.ChiSquare.chi2test: bad p-value: " ++ show p
  where
    n     = Vector.length vec - ndf - 1
    g     = gg
      where gg = 2 * (likelihood  vec)
            chi2  = sum $ fmap (\(o,e) -> square (fromIntegral o - e) / e) vec
    d     = chiSquared n

chi2 vec = sum $ fmap (\(o,e) -> square (fromIntegral o - e) / e) vec


wellektest :: Double -> Double -> Vector (Int, Double) -> TestResult
wellektest ε α rss =
      id
    -- $ traceShow (sqrt euclid2, ε, uα, v / (sqrt n))
    $ significant
    $ euclid2 < (ε^2 - (uα * v / (sqrt n)))
   where n   = assert (nLeft == nRight) $ fromIntegral nLeft
           where nLeft  =         Vector.sum $ fmap fst $ rss
                 nRight = round $ Vector.sum $ fmap snd $ rss
         rs' = fmap (\(x,y) -> (x / n, y / n)) rs
          where rs  = fmap (\(x,y) -> (fromIntegral x,       y)) rss
         euclid2 =         Vector.sum $ fmap (\(x,y) ->  (x - y) ^ 2)      $ rs'
         v2 = 4 * (sum1 - sum2)
           where sum1    = Vector.sum $ fmap (\(x,y) -> ((x - y) ^ 2) * x) $ rs'
                 sum2    =        sum [ (x1 - y1) * (x2 - y2) * x1 * x2 | (x1, y1) <- Vector.toList rs', (x2,y2) <- Vector.toList rs' ]

         v = sqrt v2

         uα = quantile standard (1 - α)



wellektestSignificantDifference :: Double -> Double -> Vector (Int, Double) -> TestResult
wellektestSignificantDifference ε α rss =
      id
    $ traceShow ("Wellek", sqrt euclid2, ε, uα', v / (sqrt n), "....", euclid2, " >= ", (ε^2 - (uα' * v / (sqrt n))))
    $ significant
    $ assert (limit >= 0)
    $ euclid2 >= limit 
   where limit = ((ε^2 - (uα' * v / (sqrt n))))
         n   = assert (nLeft == nRight) $ fromIntegral nLeft
           where nLeft  =         Vector.sum $ fmap fst $ rss
                 nRight = round $ Vector.sum $ fmap snd $ rss
         rs' = fmap (\(x,y) -> (x / n, y / n)) rs
          where rs  = fmap (\(x,y) -> (fromIntegral x,       y)) rss
         α' = 1 - α
         euclid2 =         Vector.sum $ fmap (\(x,y) ->  (x - y) ^ 2)      $ rs'
         v2 = 4 * (sum1 - sum2)
           where sum1    = Vector.sum $ fmap (\(x,y) -> ((x - y) ^ 2) * x) $ rs'
                 sum2    =        sum [ (x1 - y1) * (x2 - y2) * x1 * x2 | (x1, y1) <- Vector.toList rs', (x2,y2) <- Vector.toList rs' ]

         v = sqrt v2

         uα' = quantile standard (1 - α')


mytestSignificantDifference :: Double -> Double -> Vector (Int, Double) -> TestResult
mytestSignificantDifference ε α rss =
      id
    $ traceShow (wellektestSignificantDifference ε α rss)
    $ traceShow ("My    ", sqrt euclid2, ε, uα', v / (sqrt n), "....", euclid2, " >= ", (ε^2 - (uα' * v / (sqrt n))))
    $ significant
    $ euclid2 >= limit 
   where limit = ((ε^2 - (uα' * v / (sqrt n))))
         n   = assert (nLeft == nRight) $ fromIntegral nLeft
           where nLeft  =         Vector.sum $ fmap fst $ rss
                 nRight = round $ Vector.sum $ fmap snd $ rss
         rs' = fmap (\(x,y) -> (x / n, y / n)) rs
          where rs  = fmap (\(x,y) -> (fromIntegral x,       y)) rss
         α' = 1 - α
         euclid2 =         Vector.sum $ fmap (\(x,y) ->  (x - y) ^ 2)      $ rs'
         v2 = 4 * (sum1 - sum2)
           where sum1    = Vector.sum $ fmap (\(x,y) -> ((x - y - 0) ^ 2) * (x - y)) $ rs'
                 sum2    =        sum [ (x1 - y1) * (x2 - y2) * (x1 - y1) * (x2 - y2) | (x1, y1) <- Vector.toList rs', (x2,y2) <- Vector.toList rs' ]

         v = sqrt v2

         uα' = quantile standard (1 - α')




{- https://doi.org/10.1007/s11749-018-0600-8 -}
{- Two-sample test for sparse high-dimensional multinomialdistributions -}
{- Amanda Plunkett·Junyong Park -}
plunketttest :: Double -> Vector (Int, Double) -> TestResult
plunketttest α rss =
      id
    -- $ traceShow ("plunkett", sigma2estimate, "....", t, " > ", zα)
    $ significant
    $ t > zα
   where n   = assert (nLeft == nRight) $ fromIntegral nLeft
           where nLeft  =         Vector.sum $ fmap fst $ rss
                 nRight = round $ Vector.sum $ fmap snd $ rss
         bigNs = fmap (\(n1,n2) -> (fromIntegral n1, n2)) rss
         ps = fmap (\(x,y) -> (x / n, y / n)) bigNs

         sigma2estimate = sum1 + sum2
           where sum1 =                Vector.sum $ fmap (\(p1, p2) -> innersum p1 + innersum p2) ps
                 sum2 = (4.0 / n^2) * (Vector.sum $ fmap (\(p1, p2) -> p1 * p2) ps)
                 
                 innersum p = (2.0 / n^2) * (p^2 - (p / n))
                 
         fStar (x1, x2) = ((x1 / n) - (x2 / n))^2 - (x1 / n^2) - (x2 / n^2)

         t = (Vector.sum $ fmap fStar bigNs) / (sqrt sigma2estimate)

         zα = quantile standard (1 - α)

