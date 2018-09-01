{-# LANGUAGE CPP #-}
{- |
Module      :  Data.Dequeue.SimpleDequeue
Description :  A simple implementation for double-ended queues.
Copyright   :  (c) Henry Bucklow 2009-2010
               (c) Martin Hecker 2018
License     :  BSD3

An implementation of naive Dequeues, based on Data.Dequeue.BankersDequeue
-}
module Data.Dequeue.SimpleDequeue (
    SimpleDequeue,
    -- * QuickCheck properties for 'SimpleDequeue'
    prop_pushpop_front_sq,
    prop_pushpop_back_sq,
    prop_push_front_sq,
    prop_push_back_sq,
    prop_takeFront_sq,
    prop_takeBack_sq,
    prop_length_toList_sq,
    prop_fromList_toList_sq,
    prop_read_show_sq
) where

import Prelude hiding (foldl, foldr, foldl1, foldr1, length, last)

import Control.Monad
import Data.Foldable
import qualified Data.List as List

import Test.QuickCheck
#if MIN_VERSION_QuickCheck(2,0,0)
#else
   hiding (check)
#endif

import Safe

import qualified Data.Dequeue.Show
import Data.Dequeue

-- | An implementation of a naive dequeue.
--   The functions for the 'Dequeue' instance will have horrible performance in any but the following access patterns:
--
--    * (popFront* pushBack )*
--    * (popBack*  pushFront)*

data SimpleDequeue a = SimpleDequeue Int [a] Int [a]

instance Functor SimpleDequeue where
    fmap f (SimpleDequeue sizeF front sizeR rear) =
        SimpleDequeue sizeF (fmap f front) sizeR (fmap f rear)

instance Foldable SimpleDequeue where
    fold (SimpleDequeue _ front _ rear) = fold (front ++ reverse rear)
    foldMap f (SimpleDequeue _ front _ rear) = foldMap f (front ++ reverse rear)
    foldr f a (SimpleDequeue _ front _ rear) = foldr f a (front ++ reverse rear)
    foldl f a (SimpleDequeue _ front _ rear) = foldl f a (front ++ reverse rear)
    foldr1 f (SimpleDequeue _ front _ rear) = foldr1 f (front ++ reverse rear)
    foldl1 f (SimpleDequeue _ front _ rear) = foldl1 f (front ++ reverse rear)
#if MIN_VERSION_base(4,8,0)
    length (SimpleDequeue sizeF _ sizeR _) = sizeF + sizeR
#endif

instance Dequeue SimpleDequeue where
    empty = SimpleDequeue 0 [] 0 []
    null (SimpleDequeue 0 [] 0 []) = True
    null _ = False
#if !MIN_VERSION_base(4,8,0)
    length (SimpleDequeue sizeF _ sizeR _) = sizeF + sizeR
#endif
    first (SimpleDequeue _ [] _ [x]) = Just x
    first (SimpleDequeue _ front _ _) =  headMay front
    last (SimpleDequeue _ [x] _ []) = Just x
    last (SimpleDequeue _ _ _ rear) = headMay rear
    takeFront i (SimpleDequeue sizeF front _ rear) =
        take i front ++ take (i - sizeF) (reverse rear)
    takeBack i (SimpleDequeue _ front sizeR rear) =
        take i rear ++ take (i - sizeR) (reverse front)
    pushFront (SimpleDequeue sizeF front sizeR rear) x =
        SimpleDequeue (sizeF + 1) (x : front) sizeR rear
    popFront (SimpleDequeue _ [] _     [] ) = Nothing
    popFront (SimpleDequeue _ [] _     [x]) = Just (x, empty)
    popFront (SimpleDequeue _ [] sizeR xs ) = Just (x, SimpleDequeue (sizeR - 1) xs' 0 [])
      where (x:xs') = reverse xs
    popFront (SimpleDequeue sizeF (f : fs) sizeR rear) =
        Just (f, SimpleDequeue (sizeF - 1) fs sizeR rear)
    pushBack (SimpleDequeue sizeF front sizeR rear) x =
        SimpleDequeue sizeF front (sizeR + 1) (x : rear)
    popBack  (SimpleDequeue _     []  _ []) = Nothing
    popBack  (SimpleDequeue _     [x] _ []) = Just (x, empty)
    popBack  (SimpleDequeue sizeL xs  _ []) = Just (x, SimpleDequeue 0 [] (sizeL - 1) xs')
      where (x:xs') = reverse xs
    popBack  (SimpleDequeue sizeF front sizeR (r : rs)) =
        Just (r, SimpleDequeue sizeF front (sizeR - 1) rs)
    fromList list = SimpleDequeue (List.length list) list 0 []

instance (Arbitrary a) => Arbitrary (SimpleDequeue a) where
    arbitrary = (liftM fromList) arbitrary

#if MIN_VERSION_QuickCheck(2,0,0)
#else
    coarbitrary (SimpleDequeue _ front _ rear) =
        variant 0 . coarbitrary front . coarbitrary rear
#endif

instance Eq a => Eq (SimpleDequeue a) where
    queue1 == queue2 = toList queue1 == toList queue2

instance Show a => Show (SimpleDequeue a) where
    show q = showDequeue q

instance Read a => Read (SimpleDequeue a) where
    readsPrec i = readDequeue $ readsPrec i

-- QuickCheck properties for SimpleDequeue.

-- | Validates that if you push, then pop, the front of a 'SimpleQueue',
--   you get the same queue.
prop_pushpop_front_sq :: SimpleDequeue Int -> Int -> Bool
prop_pushpop_front_sq = prop_pushpop_front

-- | Validates that if you push, then pop, the back of a 'SimpleDequeue',
--   you get the same queue.
prop_pushpop_back_sq :: SimpleDequeue Int -> Int -> Bool
prop_pushpop_back_sq = prop_pushpop_back

-- | Validates that 'first' returns the last 'pushFront''d element.
prop_push_front_sq :: SimpleDequeue Int -> Int -> Bool
prop_push_front_sq = prop_push_front

-- | Validates that 'last' returns the last 'pushBack''d element.
prop_push_back_sq :: SimpleDequeue Int -> Int -> Bool
prop_push_back_sq = prop_push_back

-- | Validates that the last 'n' pushed elements are returned by takeFront.
prop_takeFront_sq :: SimpleDequeue Int -> [Int] -> Bool
prop_takeFront_sq = prop_takeFront

-- | Validates that the last 'n' pushed elements are returned by takeBack.
prop_takeBack_sq :: SimpleDequeue Int -> [Int] -> Bool
prop_takeBack_sq = prop_takeBack

-- | Validates that the length of a 'SimpleDequeue' is the same as the length
--   of the list generated from the queue.
prop_length_toList_sq :: SimpleDequeue Int -> Bool
prop_length_toList_sq = prop_length_toList

-- | Validates that fromList . toList is the identity for a 'SimpleDequeue'.
prop_fromList_toList_sq :: SimpleDequeue Int -> Bool
prop_fromList_toList_sq = prop_fromList_toList


-- | Validates that a 'SimpleDequeue' has read and show instances that are
--   the inverse of each other.
prop_read_show_sq :: SimpleDequeue Int -> Bool
prop_read_show_sq q = (read . show) q == q

