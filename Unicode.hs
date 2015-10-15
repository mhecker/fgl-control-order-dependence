module Unicode where

import Algebra.Lattice
import Data.Foldable
import Data.List (filter)

infixl 6 ⊔
(⊔) :: (JoinSemiLattice a) => a -> a -> a
(⊔) = join

infixl 7 ⊓
(⊓) :: (MeetSemiLattice a) => a -> a -> a
(⊓) = meet

(⊥) :: (BoundedJoinSemiLattice a) => a
(⊥) = bottom

(⊤) :: (BoundedMeetSemiLattice a) => a
(⊤) = top


(∐) :: (BoundedJoinSemiLattice a) => [a] -> a
(∐) = joins

(∏) :: (BoundedMeetSemiLattice a) => [a] -> a
(∏) = meets


𝝁 :: (Eq a, BoundedJoinSemiLattice a) => (a -> a) -> a
𝝁 = lfp

𝝂 :: (Eq a, BoundedMeetSemiLattice a) => (a -> a) -> a
𝝂 = gfp

(㎲⊒) :: (Eq a, BoundedJoinSemiLattice a) => a -> (a -> a) -> a
(㎲⊒) = lfpFrom

(∀) :: (Eq a, Foldable t) => t a -> (a -> Bool) -> Bool
(∀) a pred = null $ filter (not.pred) $ toList a

(∃) :: (Eq a, Foldable t) => t a -> (a -> Bool) -> Bool
(∃) a pred = (not.null) $ filter pred $ toList a


(→) :: Bool -> Bool -> Bool
(→) = implies
  where implies a b = (not a) || b

(⊑) :: (Eq a, JoinSemiLattice a) => a -> a -> Bool
(⊑) = joinLeq
