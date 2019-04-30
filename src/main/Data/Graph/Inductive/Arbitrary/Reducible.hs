module Data.Graph.Inductive.Arbitrary.Reducible where

import Test.QuickCheck (Arbitrary (..), Gen, elements, frequency, sized)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree (Gr)
import Unicode

import Data.Set (Set)
import qualified Data.Set as Set



data Reducible ag a b = RedG { redArbGraph :: ag a b }
                        deriving (Eq, Show, Read)


t1 :: (Eq b, DynGraph gr) => gr a b ->  [gr a b]
t1 g = do
    (n,b) <- [ (n,b) | n <- nodes g, b <- [ b | (n', b) <- lsuc g n, n == n' ]]
    return $ delLEdge (n,n,b) g

t2 ::  DynGraph gr => gr a b ->  [gr a b]
t2 g = do
    (n1,n2) <- [ (n1,n2) | n2 <- nodes g,
                           let preds = pre g n2,
                           (Set.size $ Set.fromList $ preds) == 1,
                           let (n1:_) = preds,
                           n1 /= n2
         ]
    return $ delNode n2
           $ insEdges [(n1,m,b) | (m,b) <- lsuc g n2]
           $ g



isReducible :: (Eq b, DynGraph gr) => gr a b -> Bool
isReducible g = (length $ nodes (reduct g)) <= 1


reduct :: (Eq b, DynGraph gr) => gr a b -> gr a b
reduct g 
    | null $ reducts = g
    | otherwise      = reduct $ head reducts
  where reducts =  (t1 g) ++ (t2 g)

t1Reverse :: DynGraph gr => gr a b -> b ->  [gr a b]
t1Reverse g b = do
    n <- [ n | n <- nodes g]
    return $ insEdge (n, n, b) g

t2Reverse :: (Eq b, DynGraph gr) => gr a b -> a -> b ->  [gr a b]
t2Reverse g a b = do
    n1 <- nodes g
    let [n2] = newNodes 1 g
    let sucs = lsuc g n1
    (suc1, suc2) <- [ (suc1, suc2) | (suc1, suc2) <- twoDistributions $ sucs]
    return $ insEdge    (n1, n2, b)
           $ insEdges  [(n2, m, l) | (m,l) <- suc2]
           $ insNode    (n2, a)
           $ insEdges  [(n1, m, l) | (m,l) <- suc1]
           $ delLEdges [(n1, m, l) | (m,l) <- sucs]
           $ g

delLEdges edges g = foldr delLEdge g edges


twoDistributions :: [a] -> [([a], [a])]
twoDistributions [] = [([],[])]
twoDistributions (a:as) = do
          (left, right) <- twoDistributions as
          result <- [(a:left, right), (left, a:right), (a:left, a:right)]
          return result


{- A Generator for reducible Graphs. It is not very fast. Recommended Sizes: 0 <= n <= 200. -}
reducibleGenerator ::  (Eq b, DynGraph gr, Arbitrary a, Arbitrary b) => Int -> Gen (Reducible gr a b)
reducibleGenerator 0 = do
    a <- arbitrary
    return $ (RedG $ mkGraph [(1,a)] [])
reducibleGenerator n = do
     (RedG g)  <- reducibleGenerator (n-1)
     (RedG g') <- frequency [ (1, genT1 g),
                              (4, genT2 g)
           ]
     return $ RedG g'
  where genT1 g = do
          b  <- arbitrary
          g' <- elements $ t1Reverse g b
          return $ RedG g'
        genT2 g = do
          a  <- arbitrary
          b  <- arbitrary
          g' <- elements $ t2Reverse g a b
          return $ RedG g'

instance (DynGraph ag, Arbitrary a, Arbitrary b, Eq b) => Arbitrary (Reducible ag a b) where
  arbitrary = sized reducibleGenerator
  shrink (RedG g) = fmap RedG $ (t1 g) ++ (t2 g)


-- Some tests
t1t2t2 = do
  let initial = mkGraph [(1,())] [] :: Gr () ()
  g1 <- t1Reverse initial ()
  g2 <- t2Reverse g1 () ()
  g3 <- t2Reverse g2 () ()
  return g3

t2t2t2t2 = do
  let initial = mkGraph [(1,())] [] :: Gr () ()
  g1 <- t2Reverse initial () ()
  g2 <- t2Reverse g1 () ()
  g3 <- t2Reverse g2 () ()
  g4 <- t2Reverse g3 () ()
  return g4
