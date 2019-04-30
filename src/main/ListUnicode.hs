module ListUnicode where

import Data.List (all)

(∀) :: (Eq a) => [a] -> (a -> Bool) -> Bool
(∀) = flip all
