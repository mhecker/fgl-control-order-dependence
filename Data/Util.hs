module Data.Util where


import Data.Tree (Tree(..))
import qualified Data.Tree as Tree

import Control.Monad.State
import Control.Monad(forM)

paths :: Tree a -> [[a]]
paths (Node a []) = [[a]]
paths (Node a as) = map (a:) $ concatMap paths as



withId :: Tree a -> Tree (Integer, a)
withId tree = evalState (withIds tree) 0
  where withIds (Node x trees) =
          do n <- get
             put (n+1)
             trees' <- forM trees withIds
             return $ Node (n,x) trees'
