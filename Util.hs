module Util where

import Data.List (find, nub, nubBy)
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Foldable as Foldable
import Unicode
import Algebra.Lattice

import Control.Monad (foldM)
the p = fromJust . find p 



chooseOneEach :: [(a,[b])] -> [[(a,b)]]
chooseOneEach choices = fmap (zip as) $ sequence bss
  where as  = fmap fst choices
        bss = fmap snd choices

restrict σ vars = Map.filterWithKey (\var _ -> var ∈ vars) σ


invert :: (Ord k, Ord v) => Map k v -> Map v (Set k)
invert m = Map.fromListWith (∪) pairs
    where pairs = [(v, Set.singleton k) | (k, v) <- Map.toList m]




invert' :: (Ord k, Ord v) => Map k [v] -> Map v [k]
invert' m = Map.fromListWith (++) pairs
    where pairs = [(v, [k]) | (k, vs) <- Map.toList m, v <- vs]


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

