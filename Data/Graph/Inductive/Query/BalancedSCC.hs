module Data.Graph.Inductive.Query.BalancedSCC where

import Debug.Trace
import Util

import Data.Maybe(fromJust)

import Data.List(union, intersect, elem, delete, sort)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.DFS

import Test.QuickCheck

import Data.Graph.Inductive.Arbitrary

data Parantheses a = Open | Close deriving (Ord, Enum, Eq)
type Annotation b = Maybe (Parantheses b)

merge :: [[Node]] -> [Node] -> [[Node]]
merge [] cycle = [cycle]
merge (c:cs) cycle
  | c `intersect` cycle == [] = c:(merge cs cycle)
  | otherwise                 = merge cs (c `union` cycle)

sccNaive :: DynGraph gr => gr a b -> [[Node]]
sccNaive gr = scc (nodes gr) (edges gr) [[n] | n <- nodes gr] []
  where scc []        uedges sccs []          = sccs
        scc (u:us)    uedges sccs []          = scc (u:us) uedges sccs [u]
        scc unodes    uedges sccs path@(n:ns) = trace ((show path) ++ "\t\t" ++ (show sccs)) $ 
         case es of
          []          -> scc (delete n unodes) uedges sccs ns
          ((n',m):ms) -> if (any (m `elem`) (fmap sccOf path)) then
                           scc unodes (delete (n',m) uedges) (merge sccs (m:cycle)) prefix
                         else
                           scc unodes (delete (n',m) uedges)  sccs                  (m:path)
            where (cycle, prefix) = span (\n -> not $ m `elem` (sccOf n)) path
         where es = [ (n',m) | n' <- sccOf n, m <- suc gr n', (n',m) `elem` uedges ]
               sccOf m =  the (m `elem`) $ sccs


sccIsSccNaive :: Gr () () -> Bool
sccIsSccNaive gr = sccs == sccsNaive
  where -- sccs      = Set.fromList $ (fmap Set.fromList $ scc gr)
        -- sccsNaive = Set.fromList $ (fmap Set.fromList $ sccNaive gr)
        sccs      = sort $ (fmap sort $ scc gr)
        sccsNaive = sort $ (fmap sort $ sccNaive gr)


-- balancedScc :: DynGraph gr => gr a (Annotation b) -> Map Node [Node]
-- balancedScc :: bscc parenstack sccsOf unvisited 

--   w
