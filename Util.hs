module Util where


import Data.List (find, nub, nubBy)
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Foldable as Foldable
import Unicode
import Algebra.Lattice

import Control.Exception.Base (assert)
import Control.Monad (foldM)
import Control.Monad.Random hiding (join)
the p = fromJust . find p 



chooseOneEach :: [(a,[b])] -> [[(a,b)]]
chooseOneEach choices = fmap (zip as) $ sequence bss
  where as  = fmap fst choices
        bss = fmap snd choices

restrict σ vars = Map.filterWithKey (\var _ -> var ∈ vars) σ


invert :: (Ord k, Ord v) => Map k v -> Map v (Set k)
invert m = Map.fromListWith (∪) pairs
    where pairs = [(v, Set.singleton k) | (k, v) <- Map.toList m]




treeDfs :: (Ord k) => Map k [k] -> [k] -> [k]
treeDfs m roots = dfs roots
  where m' = invert' m `Map.union` (Map.fromList [(n, []) | n <- Map.keys m])
        dfs [] = []
        dfs (n:ns) = n : (dfs ( m' ! n ++ ns ))

invert' :: (Ord k, Ord v) => Map k [v] -> Map v [k]
invert' m = Map.fromListWith (++) pairs
    where pairs = [(v, [k]) | (k, vs) <- Map.toList m, v <- vs]


invert'' :: (Ord k, Ord v) => Map k (Set v) -> Map v (Set k)
invert'' m = fmap Set.fromList $ invert' $ fmap Set.toList m


reallyInvert m = fmap (base ∖) m
  where base =      (Map.keysSet m)
             ∪ (∐) (Map.elems   m)

meetFrom :: (Foldable.Foldable f,  MeetSemiLattice a) => a -> f a -> a
meetFrom x l = Foldable.foldr (⊓) x l
                               
foldM1 :: (Monad m) => (a -> a -> m a) -> [a] -> m a
foldM1 _ [] = error "foldM1" "empty list"
foldM1 f (x:xs) = foldM f x xs


instance JoinSemiLattice a => JoinSemiLattice (Maybe a) where
  join Nothing Nothing   = Nothing
  join Nothing jx        = jx
  join jx      Nothing   = jx
  join (Just x) (Just y) = Just $ join x y


leastElements as            = nub      $ [ a | a <- as, (∀) as (\a' -> a ⊑ a') ]
leastElementsFor (⊑) eq  as = nubBy eq $ [ a | a <- as, (∀) as (\a' -> a ⊑ a') ]

minimalElements as            = nub      $ [ a | a <- as, (∀) as (\a' -> a ==   a'   ∨  (not $ a' ⊑ a)) ]
minimalElementsFor (⊑) eq  as = nubBy eq $ [ a | a <- as, (∀) as (\a' -> a `eq` a'   ∨  (not $ a' ⊑ a)) ]


deleteAt n [] = error "cannot delete from empty list"
deleteAt 0 (x:xs) = xs
deleteAt n (x:xs)
   | n < 0     = error "invalid index: delete"
   | otherwise = x:(deleteAt (n-1) xs)


updateAt n y [] = error "cannot update in empty list"
updateAt 0 y (x:xs) = y:xs
updateAt n y (x:xs)
   | n < 0     = error "invalid index: update"
   | otherwise = x:(updateAt (n-1) y xs)


reachableFrom :: Ord α => Map α (Set α) -> Set α -> Set α -> Set α
reachableFrom m xs seen
    | Set.null xs = seen
    | otherwise = xs ∪ reachableFrom m new (seen ∪ xs)
  where new = Set.fromList [ x' | x <- Set.toList xs, Just x's <- [ Map.lookup x m ], x' <- Set.toList $ m ! x, not $ x ∈ seen]

reachableFromIn :: Ord a => Map a (Set (a, (Integer, Set a))) -> a -> a -> Set Integer
reachableFromIn succs x y
    | x == y    = Set.fromList [0]
    | otherwise = reachableVisited (Set.fromList [(x,0)]) (Set.fromList [x]) Set.empty
  where reachableVisited xs visited found
          | null new = found
          | otherwise = reachableVisited (Set.fromList new) visited' (found ∪ (Set.map (fst.snd) $ Set.filter (\(y', _) -> y' == y)  nextxs))
          where 
                nextxs =  (∐) [ Set.map (\(x', (sx', pis)) -> (x', (sx+sx', pis))) $ succs ! x | (x,sx) <- Set.toList xs ]
                new = [ (x', sx') | (x', (sx', pis)) <- Set.toList nextxs, not $ x' ∈ visited]
                visited' = visited ∪ (Set.map fst nextxs) ∪ (∐) [ pis | pis <- Set.toList $ Set.map (snd . snd) nextxs]


rotations :: [a] -> [[a]]
rotations xs = rots l double
  where rots 0 ds     = []
        rots 1 ds     = [take l ds]
        rots n (d:ds) = (take l (d:ds)):(rots (n-1) ds)
        double = take (2*l) $ cycle xs
        l = length xs



sampleFrom :: Int -> Integer -> [a] -> [a]
sampleFrom seed n xs = evalRand (s n) (mkStdGen seed)
  where s 0 = return $ []
        s n = do
          y <- ss xs
          ys <- s (n-1)
          return (y:ys)
        ss :: MonadRandom m => [t] -> m t
        ss xs = do
          i <- getRandomR (1, length xs)
          return $ xs !! (i-1)


roots idom
  | Set.null ns0 = []
  | otherwise    = rootsFrom x [x] unchecked
  where ns0 = Map.keysSet idom
        (x, unchecked) = Set.deleteFindMin ns0
        rootsFrom n seen unchecked
            | Set.null $ idom ! n = [n] : rest
            | n' ∈ unchecked      = rootsFrom n' (n':seen) (Set.delete n' unchecked)
            | otherwise           = if (afterN' /= []) then (n':beforeN') : rest else rest
          where (beforeN',afterN') = span (/= n') seen
                rest
                   | Set.null unchecked = []
                   | otherwise          = rootsFrom x' [x'] unchecked'
                  where (x', unchecked') = Set.deleteFindMin unchecked
                [n'] = Set.toList $ idom ! n


require = assert
