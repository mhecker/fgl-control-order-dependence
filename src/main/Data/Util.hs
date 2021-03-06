{-# LANGUAGE TemplateHaskell #-}
module Data.Util where


import Data.Tree (Tree(..))
import qualified Data.Tree as Tree

import Control.Monad.State(evalState, get, put)
import Control.Monad(forM)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax


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

consecutive :: [a] -> [(a,a)]
consecutive [] = []
consecutive l= tail $ zip (undefined:l) l

stutter2 :: [a] -> [a]
stutter2 list = [ y |  x <- list, y <- [x,x] ]

-- for a name n, returns: ("n", n)
withName :: Name -> ExpQ
withName n = [| ($(lift (nameBase n)), $(varE n)) |]
