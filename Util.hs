{-# LANGUAGE RankNTypes #-}
module Util where

import Debug.Trace

import Data.List (find, nub, nubBy)
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Bits.Bitwise (fromListBE,fromListLE)
import Data.Bits (testBit)

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

-- TODO: replace with Map.filterWithKey Map.restrictKeys in newer containers releases
restrict σ vars = Map.filterWithKey (\var _ ->      var ∈ vars) σ
without σ vars = Map.filterWithKey (\var _ -> not $ var ∈ vars) σ


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
invert'' m = Map.fromListWith (∪) pairs
    where pairs = [(v, Set.singleton k) | (k, vs) <- Map.toList m, v <- Set.toList vs]

invert''' :: (Ord k, Ord v) => Map k (Maybe v) -> Map v (Set k)
invert''' m = Map.fromListWith (∪) pairs
    where pairs = [(v, Set.singleton k) | (k, Just v) <- Map.toList m]


-- dfsTree idom' ns = ns : (concat $ fmap dfs [ m | n <- Set.toList ns, m <- Set.toList $ idom' ! n, not $ m ∈ ns ])
--   where dfs n = Set.fromList [n] : (concat $ Set.map dfs $ Map.findWithDefault Set.empty n idom')


dfsTree :: Ord a => Map a (Set a) -> [Set a] -> [Set a]
dfsTree idom' roots = foldr (:) (dfs [ m | root <- roots, n <- Set.toList root, m <- Set.toList $ Map.findWithDefault Set.empty n idom', not $ m ∈ root ]) roots
  where dfs []       = []
        dfs (n : ns) = (Set.singleton n) : dfs ns'
          where ns' = Set.fold (:) ns $ Map.findWithDefault Set.empty n idom'

treeLevel :: Ord a => Map a (Set a) -> [Set a] -> [[(a,Integer)]]
treeLevel idom' roots = [ foldr (:) (lvl 1 [ m | n <- Set.toList root, m <- Set.toList $ Map.findWithDefault Set.empty n idom', not $ m ∈ root]) [(n,0) | n <- Set.toList root] | root <- roots]
  where lvl l []  = []
        lvl l ns  = foldr (:) (lvl (l+1) [ n' | n <- ns, n' <- Set.toList $ Map.findWithDefault Set.empty n idom']) [(n,l) | n <- ns]


reallyInvert m = fmap (base ∖) m
  where base =      (Map.keysSet m)
             ∪ (∐) (Map.elems   m)

meetFrom :: (Foldable.Foldable f,  MeetSemiLattice a) => a -> f a -> a
meetFrom x l = Foldable.foldr (⊓) x l
                               
foldM1 :: (Monad m) => (a -> a -> m a) -> [a] -> m a
{-# INLINE foldM1 #-}
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


reachableFromSeen :: Ord α => Map α (Set α) -> Set α -> Set α -> Set α
reachableFromSeen m xs seen
    | Set.null xs = seen
    | otherwise   = reachableFromSeen m new (seen ∪ xs)
  where seen' = seen ∪ xs
        -- new   = Set.unions [ (Map.findWithDefault Set.empty x m) ∖ seen' | x <- Set.toList $ xs ]
        new   = Set.unions [ (Map.findWithDefault Set.empty x m) ∖ seen' | x <- Set.toList $ xs ]


reachableFrom :: Ord α => Map α (Set α) -> Set α -> Set α
reachableFrom m xs = reachableFromSeen m xs Set.empty


reachableFromM :: Ord α => Map α (Maybe α) -> Set α -> Set α -> Set α
reachableFromM m xs seen
    | Set.null xs = seen
    | otherwise = xs ∪ reachableFromM m new (seen ∪ xs)
  where new = Set.fromList [ x' | x <- Set.toList xs, not $ x ∈ seen, Just x' <- [ Map.findWithDefault Nothing x m ] ]


reachableFromTree :: Ord α => Map α (Set α) -> α -> Set α
reachableFromTree m x = reachFrom (Set.fromList [x]) Set.empty
  where reachFrom xs seen 
          | Set.null xs = seen
          | otherwise = xs ∪ reachFrom new (seen ∪ xs)
              where new = Set.fromList [ x' | x <- Set.toList xs, Just x's <- [ Map.lookup x m ], x' <- Set.toList $ m ! x]




isReachableFromTree :: Ord α => Map α (Set α) -> α -> α -> Bool
isReachableFromTree m x y = isReach y
  where isReach y
          | x == y    = True
          | otherwise = case Set.toList $ m ! y of
                          []  -> False
                          [z] -> isReach z
                          _   -> error "no tree"

isReachableFromTreeM :: Ord α => Map α (Maybe α) -> α -> α -> Bool
isReachableFromTreeM m x y = isReach y
  where isReach y
          | x == y    = True
          | otherwise = case m ! y of
                          Nothing  -> False
                          Just z -> isReach z

isReachableFromM :: Ord α => Map α (Maybe α) -> α -> α -> Bool
isReachableFromM m x y = isReach y Set.empty
  where isReach y seen
          | x == y    = True
          | y ∈ seen  = False
          | otherwise = case m ! y of
                          Nothing  -> False
                          Just z -> isReach z (Set.insert y seen)


allReachableFromTreeM :: Ord α => Map α (Maybe α) -> Set α -> α -> Bool
allReachableFromTreeM m xs y = allReach (Set.delete y xs) y
  where allReach notseen y
          | Set.null notseen = True
          | otherwise = case m ! y of
                          Nothing -> False
                          Just z  -> allReach (Set.delete z notseen) z


isReachableBeforeFromTreeM :: Ord α => Map α (Maybe α) -> α -> α -> α -> Bool
isReachableBeforeFromTreeM m a x y = isReach y
  where isReach y
          | a == y    = True
          | x == y    = False
          | otherwise = case m ! y of
                          Nothing -> False
                          Just z  -> isReach z


minimalPath :: Ord a => Map a (Set (a,Integer)) -> a -> a -> [[(a,Integer)]]
minimalPath m x y = find (Set.fromList [x]) x
  where find forbidden x
            | x == y = [[]]
            | Set.null zs = []
            | otherwise = do
                            (z,steps) <- Set.toList zs
                            if z ∈ forbidden then mzero
                            else do
                              path <- find (Set.insert z forbidden) z
                              return $ (z,steps) : path
          where zs = m ! x


pathsUpToLength :: Ord a => Map a (Set (a,Integer)) -> Integer -> a -> a -> [[(a,Integer)]]
pathsUpToLength m n x y = find 0 x
  where find stepsX  x
            | x == y ∧ stepsX == n = [[]]
            | x /= y ∧ stepsX == n = []
            |          stepsX  > n = []
            | otherwise            = found ++  morePaths
          where zs = m ! x
                found = if x == y then [[]] else []
                morePaths = do
                              (z,steps) <- Set.toList zs
                              path <- find (stepsX+steps) z
                              return $ (z,steps) : path

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


moreSeeds seed n =  evalRand (s n) (mkStdGen seed)
  where s n = do
          rs <- getRandoms
          return $ take n rs

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



toSet :: Ord a => Maybe a -> Set a
toSet Nothing  = Set.empty
toSet (Just x) = Set.fromList [x]

fromSet :: Ord a => Set a -> Maybe a
fromSet s = case Set.toList s of
  []  -> Nothing
  [x] -> Just x
  otherwise -> error "no singleton/empty"


evalBfun f bs  = testBit f (fromListBE bs)


findMs dom ms xs n = find (n ∈ xs) (Set.delete n xs) False n 
  where find inXs xs found n
            | Set.null xs' = found'
            | otherwise = case dom ! n of
                            Nothing -> False
                            Just z  -> find inXs' xs' found' z
          where  inXs' = if inXs then not $ Set.null xs' else n ∈ xs
                 xs' = Set.delete n xs
                 found' = found ∨ (inXs ∧ n ∈ ms)


findNoMs dom ms xs n = find (n ∈ xs) (Set.delete n xs) False n 
  where find inXs xs found n
            | inXs ∧ found' = False
            | Set.null xs' = True
            | otherwise = case dom ! n of
                            Nothing -> False
                            Just z  -> find inXs' xs' found' z
          where  inXs' = if inXs then not $ Set.null xs' else n ∈ xs
                 xs' = Set.delete n xs
                 found' = found ∨ (inXs ∧ n ∈ ms)


findBoth dom ms xs n = find (n ∈ xs) (Set.delete n xs) False n 
  where find inXs xs found n
            | Set.null xs' = (found', not $ found')
            | otherwise = case dom ! n of
                            Nothing -> (False, False)
                            Just z  -> find inXs' xs' found' z
          where  inXs' = if inXs then not $ Set.null xs' else n ∈ xs
                 xs' = Set.delete n xs
                 found' = found ∨ (inXs ∧ n ∈ ms)


fromIdom  m idom = Map.insert m Set.empty $ Map.fromList [ (n, Set.fromList [m]) | (n,m) <- idom ]
fromIdomM m idom = Map.insert m Nothing   $ Map.fromList [ (n, Just          m ) | (n,m) <- idom ]

findCyclesM :: (Show a, Ord a) => Map a (Maybe a) -> (Map a (Set a), [Set a])
findCyclesM idom
    | Map.null idom = (Map.empty, [])
    | otherwise     = ((foldr Map.union Map.empty [ Map.fromSet (\n -> cycle) cycle | cycle <- cycles]), cycles)
  where (x,_) = Map.findMin idom
        cycles = find [x] (Set.fromList [x]) idom []
        find []         ps idom cycles = assert (Map.null idom) $ cycles
        find path@(x:_) ps idom cycles = case mx' of 
                              Nothing        ->   find     path'                 ps'  idom'          cycles
                              Just Nothing   ->   find     path'                 ps'  idom'          cycles
                              Just (Just x') -> if x' ∈ ps then let cycle = cycleOf x' in
                                                  find     path'                 ps'  idom' (cycle : cycles)
                                                else
                                                  find (x':path)  (Set.insert x' ps)  idomX          cycles
                          where (mx', idomX) = Map.updateLookupWithKey (\_ _ -> Nothing) x idom 
                                (path', idom', ps')
                                    | Map.null idomX = ([], Map.empty, Set.empty)
                                    | otherwise      = ([y], idomX, Set.fromList [y])
                                  where (y,_) = Map.findMin idomX
                                cycleOf x' = Set.insert x' $ Set.fromList $ takeWhile (/= x') path


infix 4 ≡
(≡) m1 m2 = (∀) (Map.elems $ Map.unionWith f m1 m2) Set.null
  where f ns ns'
         | ns == ns'    = Set.empty
         | Set.null ns  = ns'
         | otherwise    = ns
