module Unicode (
  module Set,
  module Bool,
  module Unicode
) where

import Prelude hiding (elem)
import Algebra.Lattice
import Data.Foldable
import Data.List (filter)
import Data.Set.Unicode as Set
import Data.Bool.Unicode as Bool




import qualified Algebra.PartialOrd as PO

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
(∐) l = joins l

(∏) :: (MeetSemiLattice a) => [a] -> a
(∏) [] = error "empty meet"
(∏) (x:xs) = foldr (/\) x xs


𝝁 :: (Eq a, BoundedJoinSemiLattice a) => (a -> a) -> a
𝝁 = lfp

𝝂 :: (Eq a, PO.PartialOrd a) => a -> (a -> a) -> a
𝝂 = PO.unsafeGfpFrom

(㎲⊒) :: (Eq a, BoundedJoinSemiLattice a) => a -> (a -> a) -> a
(㎲⊒) = lfpFrom

(∀) :: (Foldable t) => t a -> (a -> Bool) -> Bool
(∀) a pred = null $ filter (not.pred) $ toList a

(∫) :: (Eq a, Foldable t) => t a -> (a -> Bool) -> [a]
(∫) a pred = filter (not.pred) $ toList a

(∃) :: (Foldable t) => t a -> (a -> Bool) -> Bool
(∃) a pred = (not.null) $ filter pred $ toList a

-- We used to do this:
--  infix 4 ∈
--  (∈) :: (Eq a, Foldable t) => a -> t a -> Bool
--  (∈) = elem
--, but the ∊ instantion for Set does not (cannot?) use the Ord constraint, and hence makes a linaer (!) search!


infix 4 ∊
(∊) :: (Eq a) => a -> [a] -> Bool
(∊) = elem
 
infix 4 ↔
(↔) :: Bool -> Bool -> Bool
(↔) = (==)

(→) :: Bool -> Bool -> Bool
(→) = implies
  where implies a b = (not a) || b

(←) :: Bool -> Bool -> Bool
(←) = implies
  where implies a b = (not b) || a

(⊑) :: (Eq a, JoinSemiLattice a) => a -> a -> Bool
(⊑) = joinLeq

(⊏) :: (Eq a, JoinSemiLattice a) => a -> a -> Bool
a ⊏ b = a /= b  ∧  a ⊑ b

 
(⊒) :: (Eq a, JoinSemiLattice a) => a -> a -> Bool
(⊒) = flip (⊑)

(⊐) :: (Eq a, JoinSemiLattice a) => a -> a -> Bool
(⊐) = flip (⊏)
