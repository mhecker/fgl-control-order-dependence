{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, ScopedTypeVariables #-}

module Data.Graph.Inductive.FA where
import Debug.Trace
import Util

import System.Random
import Control.Monad.Random
import Control.Exception.Base (assert)

import Algebra.Lattice hiding (gfpFrom)
import Algebra.PartialOrd (unsafeGfpFrom)

import Unicode

import Data.Maybe(fromJust, isNothing, isJust)

import Data.List(union, intersect, elem, delete, sort, (\\), nub, null)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph hiding (nfilter)  -- TODO: check if this needs to be hidden, or can just be used
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.TransClos (trc)
import Data.Graph.Inductive.Query.Dominators (dom, iDom)


data Transition b = All | Only (Set b) | Epsilon deriving (Eq, Ord)
instance (Show b) => Show (Transition b)
  where show All = "*"
        show (Only xs) = show xs
        show Epsilon = "ε"

instance (Ord b) => MeetSemiLattice (Transition b) where
  Epsilon `meet` Epsilon = Epsilon
  Epsilon `meet` y       = error "rofl1"
  x       `meet` Epsilon = error "rofl2"
  All `meet` y   = y
  x   `meet` All = x
  (Only sx) `meet` (Only sy) = Only (sx ∩ sy)


infix 4 .∈.
(.∈.) :: (Ord a) => a -> Transition a -> Bool
x .∈. All = True
x .∈. (Only xs) = x ∈ xs
x .∈. Epsilon = False

isNone All = False
isNone (Only sx) = Set.null sx
isNone Epsilon = False


data FA gr a b = FA { initial :: Set Node, final :: Set Node, transition :: gr a (Transition b) }

deriving instance (Show (gr a (Transition b)) ) => Show (FA gr a b)

accepts :: (Ord b, Show b, Graph gr) => FA gr a b -> Node -> [b] -> Bool
accepts fa s0 word = not $ null $ acceptsIn fa s0 word

-- TODO: this will loop whenever we have Epsilon-Loops :(
reaches :: (Ord b, Graph gr) => FA gr a b -> Node -> [b] -> [Node]
reaches (FA { initial, final, transition}) s0 word = rc s0 word
  where rc n     []   = [n]
        rc n (x:xs) = normal ++ epsilon
          where successors = lsuc transition n
                normal  = do
                            n' <- [ n' | (n', ok)      <- successors, x .∈. ok]
                            rc n' xs
                epsilon = do
                            n' <- [ n' | (n', Epsilon) <- successors]
                            rc n' (x:xs)


acceptsIn :: (Ord b, Graph gr) => FA gr a b -> Node -> [b] -> [Node]
acceptsIn fa@(FA { initial, final, transition}) s0 word
    | s0 ∈ initial = [ f | f <- reaches fa s0 word, f ∈ final]
    | otherwise    = error $ "not initial:" ++ (show (s0, initial))

sampleWordsFor :: (Eq b, Ord b, DynGraph gr)             => Int -> Set b -> Integer ->   FA gr a b -> [(Node, [b])]
sampleWordsFor seed language k fa = fmap (\(n, w) -> (n, reverse w)) $ evalRand (sampleWord language k fa) (mkStdGen seed)

sampleWord :: forall m gr a b. (MonadRandom m, DynGraph gr, Eq b, Ord b) =>  Set b -> Integer  ->  FA gr a b -> m [(Node, [b])]
sampleWord language  k fa
  | null (nodes transition) = return []
  | otherwise               = sampleSome [] 0
     where
        fa'@(FA { initial, transition, final}) = simplify fa
        sampleT :: MonadRandom m => Transition b -> m [b]
        sampleT (Only xs) = do
          x <- uniform xs 
          return [x]
        sampleT (All) = do
          x <- uniform language
          return [x]
        sampleT (Epsilon) = return []
        
        sampleSome sampled i
          | i >= k            = return $ sampled
          | otherwise         = do
              n0 <- uniform $ Set.toList $ initial
              newTraceM <- sampleTrace n0 n0 []
              case newTraceM of
                Nothing       -> sampleSome (         sampled) (i+1)
                Just newTrace -> sampleSome (newTrace:sampled) (i+1)
        sampleTrace n0 n trace
          | finished && stuck = return $ Just $ (n0, trace)
          | finished          = do
              continue <- uniform [False, True]
              if (continue) then do
                (m,e) <- uniform successors
                letters <- sampleT e
                sampleTrace n0 m (letters ++ trace)
              else
                return $ Just (n0,trace)
          | stuck = do
              n0 <- uniform $ Set.toList $ initial
              sampleTrace n0 n0 []
          | otherwise = do
               (m,e) <- uniform successors
               letters <- sampleT e
               sampleTrace n0 m (letters ++ trace)
         where finished   = n ∈ final
               successors = [ e | e@(m,l) <- lsuc transition n, case l of { Epsilon -> True ; All -> True ; Only xs -> not $ Set.null xs } ]
               stuck      = null successors


simplify :: (Ord b, DynGraph gr) => FA gr a b -> FA gr a b
simplify = simplifyModInitial True

simplifyModInitial :: (Ord b, DynGraph gr) => Bool -> FA gr a b -> FA gr a b
simplifyModInitial modInitial (FA { initial, final, transition}) =
    FA { initial = initial', final = final, transition = transition' }
  where transition'
          | modInitial = subgraph reached filtered
          | otherwise  = insNodes [ (n, l) | n <- Set.toList initial, Just l <- [lab transition n]] $
                         subgraph reached filtered 
        reached = reachedForward `Data.List.intersect` reachedBackward
        initial'
          | modInitial = initial ∩ (Set.fromList reached)
          | otherwise  = initial
        reachedBackward :: [Node]
        reachedBackward = Set.toList $ (∐) [ Set.fromList $ reachable sf (grev filtered) | sf <- Set.toList final ]
        reachedForward :: [Node]
        reachedForward  = Set.toList $ (∐) [ Set.fromList $ reachable s0       filtered | s0 <- Set.toList initial ]
        filtered = labefilter (not . (\(_,_, ts) -> isNone ts))
                 $ transition

intersect :: (Ord b, DynGraph gr) => FA gr a1 b -> FA gr a2 b -> FA gr (a1, a2) b
intersect fa1 fa2 = -- simplifyModInitial False $ 
               FA { initial    = Set.fromList [ nodeMap ! (n1, n2) | n1 <- Set.toList $ initial1,
                                                                     n2 <- Set.toList $ initial2
                                 ],
                    final      = Set.fromList [ nodeMap ! (n1, n2) | n1 <- Set.toList $ final1,
                                                                     n2 <- Set.toList $ final2
                                 ],
                    transition = mkGraph [(nodeMap ! (n1,n2), (a1, a2)) | (n1, a1) <- labNodes transition1, (n2, a2) <- labNodes transition2]
                                         [(n, m, s1 ⊓ s2) | (n1, m1, s1) <- labEdges transition1, (n2, m2, s2) <- labEdges transition2,
                                                             let n = nodeMap ! (n1,n2),
                                                             let m = nodeMap ! (m1,m2)
                                 ]
    }
  where nodeMap = Map.fromList $ zip [(n1,n2) | n1 <- nodes transition1, n2 <- nodes transition2]
                                     [0..]
        (initial1,    initial2)    = (initial    fa1, initial    fa2)
        (final1,      final2)      = (final      fa1, final      fa2)
        (transition1, transition2) = (transition fa1, transition fa2)

intersectWithCommonInitialNodes :: (Ord b, DynGraph gr) => FA gr a1 b -> FA gr a2 b -> FA gr (a1, a2) b
intersectWithCommonInitialNodes fa1 fa2
    -- |   common ⊆ (Set.fromList $ nodes $ transition1)
    --   ∧ common ⊆ (Set.fromList $ nodes $ transition2) = -- simplifyModInitial False $ 
    |   initial1 == initial2 =
               FA { initial    = common,
                    final      = Set.fromList [ nodeMap ! (n1, n2) | n1 <- Set.toList $ final1,
                                                                     n2 <- Set.toList $ final2
                                 ],
                    transition = mkGraph (    [(n                , (a1, a2)) | n <- Set.toList common, let Just a1 = lab transition1 n, let Just a2 = lab transition2 n ]
                                           ++ [(nodeMap ! (n1,n2), (a1, a2)) | (n1, a1) <- labNodes transition1, (n2, a2) <- labNodes transition2]
                                         )
                                         (    [(n, (nodeMap ! (n,n)), Epsilon) | n <- Set.toList common]
                                           ++ [(n, m, s1 ⊓ s2) | (n1, m1, s1) <- labEdges transition1, s1 /= Epsilon,
                                                                 (n2, m2, s2) <- labEdges transition2, s2 /= Epsilon,
                                                                 let n = nodeMap ! (n1,n2),
                                                                 let m = nodeMap ! (m1,m2)
                                              ]
                                           ++ [(n, m, Epsilon) | (n1, m1, Epsilon) <- labEdges transition1,
                                                                 n2 <- nodes transition2,
                                                                 let n = nodeMap ! (n1, n2),
                                                                 let m = nodeMap ! (m1, n2)
                                              ]
                                           ++ [(n, m, Epsilon) | (n2, m2, Epsilon) <- labEdges transition2,
                                                                 n1 <- nodes transition1,
                                                                 let n = nodeMap ! (n1, n2),
                                                                 let m = nodeMap ! (n1, m2)
                                              ]
                                         )
    }
    | otherwise = error "different initial nodes"
  where common = initial1
        maxCommon = if (Set.null common) then -1 else Set.findMax common
        nodeMap = Map.fromList $ -- [((n,n), n) | n <- Set.toList $ common] ++
                                 (
                                   zip [(n1,n2) | n1 <- nodes transition1, 
                                                  n2 <- nodes transition2]
                                       [(maxCommon+1)..]
                                 )
        (initial1,    initial2)    = (initial    fa1, initial    fa2)
        (final1,      final2)      = (final      fa1, final      fa2)
        (transition1, transition2) = (transition fa1, transition fa2)

-- intersectWithCommonNodes :: (Ord b, DynGraph gr) => Set Node -> FA gr a1 b -> FA gr a2 b -> FA gr (a1, a2) b
-- intersectWithCommonNodes common fa1 fa2
--     |   common ⊆ (Set.fromList $ nodes $ transition1)
--       ∧ common ⊆ (Set.fromList $ nodes $ transition2) = -- simplify $ 
--                FA { initial    = commonInitial
--                                ∪ Set.fromList [ nodeMap ! (n1, n2) | n1 <- Set.toList $ initial1, not $ n1 ∈ common,
--                                                                      n2 <- Set.toList $ initial2, not $ n2 ∈ common
--                                  ],
--                     final      = commonFinal
--                                ∪ Set.fromList [ nodeMap ! (n1, n2) | n1 <- Set.toList $ final1, 
--                                                                      n2 <- Set.toList $ final2
--                                  ],
--                     transition = mkGraph (    [(n                , (a1, a2)) | n <- Set.toList common, let Just a1 = lab transition1 n, let Just a2 = lab transition2 n ]
--                                            ++ [(nodeMap ! (n1,n2), (a1, a2)) | (n1, a1) <- labNodes transition1, not $ n1 ∈ common,
--                                                                                (n2, a2) <- labNodes transition2, not $ n2 ∈ common,
--                                                                                traceShow (n1,n2) True
--                                               ]
--                                          )
--                                          (    [(n, m, s1 ⊓ s2) | n <- Set.toList $ common,
--                                                                  (m,  s1) <- lsuc transition1 n, m ∈ common,
--                                                                  (m', s2) <- lsuc transition2 n, m == m'
--                                               ]
--                                            ++ [(n, m, s1 ⊓ s2) | n <- Set.toList $ common,
--                                                                  (m1, s1) <- lsuc transition1 n, not $ m1 ∈ common,
--                                                                  (m2, s2) <- lsuc transition2 n, not $ m2 ∈ common,
--                                                                  let m = nodeMap ! (m1,m2)
--                                               ]
--                                            ++ [(n, m, s1 ⊓ s2) | m <- Set.toList $ common,
--                                                                  (n1, s1) <- lpre transition1 m, not $ n1 ∈ common,
--                                                                  (n2, s2) <- lpre transition2 m, not $ n2 ∈ common,
--                                                                  let n = nodeMap ! (n1,n2)
--                                               ]
--                                            ++ [(n, m, s1 ⊓ s2) | (n1, m1, s1) <- labEdges transition1, not $ n1 ∈ common, not $ m1 ∈ common,
--                                                                  (n2, m2, s2) <- labEdges transition2, not $ n2 ∈ common, not $ m2 ∈ common,
--                                                                  let n = nodeMap ! (n1,n2),
--                                                                  let m = nodeMap ! (m1,m2)
--                                               ]
--                                          )
--     }
--     | otherwise = error "common not a subset of both"
--   where commonInitial = common ∩ (initial1 ∪ initial2)
--         commonFinal   = common ∩ (final1   ∪ final2)
--         maxCommon = if (Set.null common) then -1 else Set.findMax common
--         nodeMap = Map.fromList $ zip [(n1,n2) | n1 <- nodes transition1, not $ n1 ∈ common,
--                                                 n2 <- nodes transition2, not $ n2 ∈ common]
--                                      [(maxCommon+1)..]
--         (initial1,    initial2)    = (initial    fa1, initial    fa2)
--         (final1,      final2)      = (final      fa1, final      fa2)
--         (transition1, transition2) = (transition fa1, transition fa2)




data NumberSystem = Zero | Binary | Decimal | Octal deriving Show

octdecbin :: FA Gr (Maybe NumberSystem) Char
octdecbin = FA { initial, final, transition }
  where 
    initial = Set.fromList [s0]
    s0    = -1
    final = Set.fromList [0,8,2,10]
    transition = mkGraph [(s0, Nothing), (0, Just Zero), (8, Just Octal), (2, Just Binary), (10, Just Decimal)]
                         (   [(s0, 10, Only $ Set.fromList ['1'..'9' ])]
                          ++ [(s0,  0, Only $ Set.fromList ['0'])]
                          ++ [( 0,  8, Only $ Set.fromList ['0'..'7'])]
                          ++ [( 0,  2, Only $ Set.fromList ['b'])]
                          ++ [( 8,  8, Only $ Set.fromList ['0'..'7'])]
                          ++ [( 0,  2, Only $ Set.fromList ['0'..'1'])]
                          ++ [(10, 10, Only $ Set.fromList ['0'..'9'])]
                         )

binary :: FA Gr Bool Char
binary = FA { initial, final, transition }
  where 
    initial = Set.fromList [s0]
    s0 = -1
    final = Set.fromList [0]
    transition = mkGraph [(s0, False), (0, True)]
                         (   [(s0,  0, Only $ Set.fromList ['0'..'1' ])]
                          ++ [( 0,  0, Only $ Set.fromList ['0'..'1' ])]
                         )




