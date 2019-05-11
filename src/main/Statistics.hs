module Statistics where

import Control.Exception.Base (assert)
import Debug.Trace (traceShow)

import Statistics.Distribution
import Statistics.Distribution.ChiSquared
import Statistics.Distribution.Normal (standard)
import Statistics.Test.ChiSquared

import Statistics.Function (square)
import Statistics.Test.Types (significant)

-- import Data.Vector.Generic
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
{-# SPECIALIZE
    chi2test :: Double -> Int -> Vector (Int,Double) -> TestResult #-}


chi2 vec = sum $ fmap (\(o,e) -> square (fromIntegral o - e) / e) vec



-- euclid2 :: Vector (Int, Double) -> Double
-- euclid2 v = Vector.sum $ fmap (\(x,y) -> (fromIntegral x - y) ^ 2) $ v

wellektest :: Double -> Double -> Vector (Int, Double) -> TestResult
wellektest ε α rss =
      -- traceShow (euclid2, ε, uα, v / (sqrt n)) $
      significant
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
-- likelihood' :: Vector (Int, Double) -> Double
-- likelihood' rss = Vector.sum $ fmap f rs
--   where rs = fmap (\(x,y) -> (fromIntegral x, y)) rss
--         r = Vector.sum $ fmap fst $ rs
--         s = Vector.sum $ fmap snd $ rs
--         f (ri,si)  =  (  ri *. log ((ri * (r+s)) / (r * (ri + si)))  )
--                    +  (  si *. log ((si * (r+s)) / (s * (ri + si)))  )

-- g :: Vector (Int, Double) -> (Double, Double, 
-- g rss = Vector.sum $ fmap f rs
--   where rs = fmap (\(x,y) -> (fromIntegral x, y)) rss
--         r = Vector.sum $ fmap fst $ rs
--         s = Vector.sum $ fmap snd $ rs
--         f (ri,si)  =  (  ri *. log ((ri / r) / ((ri+si)/(r+s)))  )
--                    +  (  si *. log ((si / s) / ((ri+si)/(r+s)))  )
        
