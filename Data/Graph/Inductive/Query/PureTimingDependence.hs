{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.PureTimingDependence where

import Control.Exception.Base (assert)
import Debug.Trace(traceShow)

import Control.Monad (liftM)

import qualified Data.List as List
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd


import Data.Graph.Inductive

import Unicode
import Util(fromSet, without, invert'', invert''', restrict, reachableFrom)

import Data.Graph.Inductive.Util (isCond, fromSuccMap, delSuccessorEdges)
import Data.Graph.Inductive.Query.NTICD (nextCondNode, toNextCondNode, prevCondNodes, prevCondsWithSuccNode, combinedBackwardSlice, isinkDFTwoFinger, nticdF3, nticdSlice, ntscdF3)
import Data.Graph.Inductive.Query.TSCD (itimdomMultipleOfTwoFingerFor, itimdomMultipleOfTwoFinger)


data Reachability  = Unreachable | Unknown | FixedSteps Integer | FixedStepsPlusOther Integer Node | UndeterminedSteps deriving (Show, Eq)
instance JoinSemiLattice Reachability where
  Unreachable   `join` x           = x
  x             `join` Unreachable = x

  FixedSteps x `join` FixedSteps y
    | x == y    = FixedSteps x
    | otherwise = UndeterminedSteps

  FixedStepsPlusOther x n  `join` FixedStepsPlusOther y m
    | x == y ∧ n == m  = FixedStepsPlusOther x n 
    | otherwise = UndeterminedSteps

{-
  FixedStepsPlusOther x n  `join` FixedSteps          y   = {- assert (y >= x) $ -} FixedStepsPlusOther x n
  FixedSteps          x    `join` FixedStepsPlusOther y m = {- assert (x >= y) $ -} FixedStepsPlusOther y m
-}

  x         `join` y         = UndeterminedSteps

instance BoundedJoinSemiLattice Reachability where
  bottom = Unreachable

instance Ord Reachability where
  Unreachable   `compare` Unreachable = EQ
  Unreachable   `compare` x           = LT
  x             `compare` Unreachable = GT

  FixedSteps x `compare` FixedSteps y = compare x y
  FixedStepsPlusOther x n  `compare` FixedStepsPlusOther y m = case cnm of
      EQ -> compare x y
      _  -> cnm
    where cnm  = compare n m

  FixedSteps _ `compare` FixedStepsPlusOther _ _ = LT
  FixedStepsPlusOther _ _ `compare` FixedSteps _ = GT
 
  UndeterminedSteps `compare` UndeterminedSteps = EQ
  UndeterminedSteps `compare` x                 = GT
  x                 `compare` UndeterminedSteps = LT
  

plusAt :: Node -> Reachability -> Integer ->  Reachability
plusAt n r y = r `plus` y where
  (FixedSteps x)            `plus` y = FixedSteps (x+y)
  (FixedStepsPlusOther x m) `plus` y = FixedStepsPlusOther (x+y) m
  (Unreachable)             `plus` y = Unreachable
  (UndeterminedSteps)       `plus` y = FixedStepsPlusOther y n


joinPlus ::  Reachability -> Integer ->  Reachability
joinPlus r y = r `plus` y where
  (FixedSteps x)            `plus` y = FixedSteps (x+y)
  (FixedStepsPlusOther x n) `plus` y = FixedStepsPlusOther (x+y) n
  r                         `plus` y = r


type SmnTimingEquationSystem =
       Map (Node,Node) (Map (Node,Node) Reachability)
type SmnTimingEquationSystemGen gr a b =
       gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node])
    -> SmnTimingEquationSystem

solveTimingEquationSystem ::  SmnTimingEquationSystem -> SmnTimingEquationSystem
solveTimingEquationSystem s = if (s == s') then s else solveTimingEquationSystem s'
          where s' =     Map.fromList [ ((m,p), Map.fromList [ ((p,x), r) | ((p',x), rpx) <- Map.assocs smp,
                                                                            assert (p == p') True,
                                                                            let r = case rpx of
                                                                                      FixedStepsPlusOther i q -> let smq = s ! (m,q)
                                                                                                                     rmq = (∐) [ r | r <- Map.elems smq ]
                                                                                                                 in case rmq of
                                                                                                                      FixedSteps j             -> FixedSteps (1+i+j)
                                                                                                                      FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+i+j) q'
                                                                                                                      _            -> rpx
                                                                                      _                       -> rpx
                                                            ]
                                        )
                                      | ((m,p), smp) <- Map.assocs s ]


timingF3EquationSystem :: DynGraph gr => SmnTimingEquationSystemGen gr a b
timingF3EquationSystem graph condNodes reachable nextCond toNextCond =
                   Map.fromList [ ((m,p), Map.fromList  [ ((p,x), FixedSteps i) | x <- suc graph p,
                                                                                  (i,m2) <- (zip [0..] (toNextCondInOrder x)), m2 == m ]
                                  ) | m <- nodes graph, p <- condNodes]
                 ⊔ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), reachability) | x <- (suc graph p),
                                                                           m ∊ reachable x,
                                                                           Just n <- [nextCond x],
                                                                           let plus = plusAt n,
                                                                           let toNextCondX = toNextCond x,
                                                                           not $ m ∊ toNextCondX,
                                                                           let stepsToN = List.genericLength toNextCondX - 1,
                                                                           let reachabilityFromN = FixedStepsPlusOther 0 n,
                                                                           let reachability = reachabilityFromN `plus` stepsToN
                                               ]
                                  ) | m <- nodes graph, p <- condNodes ]
  where toNextCondInOrder = reverse . toNextCond

timingF3EquationSystem' :: DynGraph gr => SmnTimingEquationSystemGen gr a b
timingF3EquationSystem' graph condNodes _ nextCond toNextCond =
                        Map.fromList [ ((m,p), Map.empty) | m <- nodes graph, p <- condNodes]
                 ⊔ (∐) [ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), FixedSteps i) ]) ]
                         | p <- condNodes, x <- suc graph p,    (i,m) <- (zip [0..] (toNextCondInOrder x))
                       ]
                 ⊔ (∐) [ Map.fromList [ ((m,p), Map.fromList  [ ((p,x), reachability) ]) ]
                         | p <- condNodes, x <- suc graph p,    Just n <- [nextCond x],
                                                                           m <- reachable x graph,
                                                                           let plus = plusAt n,
                                                                           let toNextCondX = toNextCond x,
                                                                           not $ m ∊ toNextCondX,
                                                                           let stepsToN = List.genericLength toNextCondX - 1,
                                                                           let reachabilityFromN = FixedStepsPlusOther 0 n,
                                                                           let reachability = reachabilityFromN `plus` stepsToN
                        ]
  where toNextCondInOrder = reverse . toNextCond


snmTimingEquationSystem :: DynGraph gr => gr a b -> SmnTimingEquationSystemGen gr a b -> SmnTimingEquationSystem
snmTimingEquationSystem graph f = f graph condNodes reachable nextCond toNextCond
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

snmTimingF3 :: DynGraph gr => gr a b -> SmnTimingEquationSystem
snmTimingF3 graph     = snmTimingEquationSystem graph timingF3EquationSystem'

snmTimingSolvedF3 :: DynGraph gr => gr a b -> SmnTimingEquationSystem
snmTimingSolvedF3 graph = snmTimingEquationSystem graph timingSolvedF3EquationSystem
  where timingSolvedF3EquationSystem graph condNodes reachable nextCond toNextCond = solveTimingEquationSystem $ timingF3EquationSystem' graph condNodes reachable nextCond toNextCond

timingF3summary :: DynGraph gr => gr a b -> Map Node (Map Node Reachability)
timingF3summary     = timingXsummary snmTimingF3

timingSolvedF3summary :: DynGraph gr => gr a b -> Map Node (Map Node Reachability)
timingSolvedF3summary = timingXsummary snmTimingSolvedF3

timingXsummary :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Map Node Reachability)
timingXsummary snmTiming graph = 
      Map.fromList [ (n, Map.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Map.fromList [ (m,r `joinPlus` 1 ) | m <- nodes graph,
                                                          m /= n,
                                                          let rmn = s ! (m,n),
                                                          let r = (∐) [ r | r <- Map.elems rmn ]
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


timingF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingF3dependence     = timingXdependence snmTimingF3

timingSolvedF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSolvedF3dependence = timingXdependence snmTimingSolvedF3

timingSolvedF3sparseDependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSolvedF3sparseDependence = timingXsparseDependence snmTimingSolvedF3


timingXdependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
timingXdependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            let rmn = s ! (m,n),
                                            (length [ r | r <- Map.elems rmn, r /= Unreachable ]) > 1,
                                            let r = (∐) [ r | r <- Map.elems rmn ],
                                            r == UndeterminedSteps
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]



timingXsparseDependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
timingXsparseDependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            m /= n,
                                            let rmn = s ! (m,n),
                                            (length [ r | r <- Map.elems rmn, r /= Unreachable ]) > 1,
                                            (∃) (Map.elems rmn) (\r ->
                                              (∃) (Map.elems rmn) (\r' ->  r ⊔ r' == UndeterminedSteps ∧ ( 
                                                                             case (r,r') of
                                                                               (FixedStepsPlusOther _ u, FixedStepsPlusOther _ v)  -> (not $ n ∊ [u,v]) ∧ (u /= v)
                                                                               _                                                   -> True
                                                                           )
                                              )
                                            )
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        trncl = trc graph
        nextCond = nextCondNode graph


type TimeDomFunctionalR = Map Node (Map Node Reachability) ->  Map Node (Map Node Reachability)
type TimeDomFunctionalGenR gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> TimeDomFunctionalR

tdomRLfpF :: DynGraph gr => gr a b -> TimeDomFunctionalGenR gr a b -> Map Node (Map Node Reachability)
tdomRLfpF graph f = {-  fmap (\m -> Set.fromList [ (n, steps) | (n, steps) <- Map.assocs m]) $ -}
        (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Map.fromList [ (x, Unreachable) | x <- nodes graph ]) |  y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

ftdomR :: DynGraph gr => TimeDomFunctionalGenR gr a b
ftdomR graph _ _ nextCond toNextCond = f 
  where f timeDomOf = {- traceShow ((7,timeDomOf ! 7 ! 6), (11,timeDomOf ! 11 ! 6), (13, timeDomOf ! 13 ! 6)) $ -}
                   Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                ⊔  Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                                   | y <- nodes graph
                                   ]
                ⊔  Map.fromList [ (y,    let plus = plusAt n in
                                         fmap (noSelf y) $ 
                                         fmap ( `plus` (steps)) $
                                         (flip without) (Set.fromList $ toNextCond y) $
                                         fmap (noSelf n) $
                                         (∐) [ fmap (flip (plusAt x) 1) $ timeDomOf ! x | x <- suc graph n ]
                                     )
                                                                                   | y <- nodes graph,
                                                                                     Just n <- [nextCond y],
                                                                                     let steps = (toInteger $ length $ toNextCond y) - 1
                                   ]
noSelf n r@(FixedStepsPlusOther _ m)
 | n == m = UndeterminedSteps
 | otherwise = r
noSelf n r = r


tdomROfLfp graph = tdomRLfpF graph ftdomR


tdepR g =
       Map.fromList [ (n, Set.fromList [ m | m <- nodes g, let rs = Set.fromList [ r | x <- suc g n, let r = timdom ! x ! m, r /= Unreachable ], Set.size rs > 1 ])  | n <- condNodes ]
       -- Map.fromList [ (n, Set.fromList [ m | m <- nodes g, let r = timdom ! n ! m,  r == UndeterminedSteps]) | n <- condNodes]
  where timdom = tdomROfLfp g
        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]

tdepRSlice :: (DynGraph gr) => gr a b -> Node -> Set Node
tdepRSlice g = \m -> let nticdSliceM = slicer (Set.fromList [m]) in  Set.fromList [m]  ∪  (㎲⊒) Set.empty (f m nticdSliceM)
  where f m nticdSliceM s = Set.fromList [ n | n <- condNodes, m ∈ tdep ! n ]
              ∪ Set.fromList [ n | n <- condNodes, not $ Set.null $ tdep  ! n  ∩  s  ]
--              ∪ Set.fromList [ n | n <- condNodes, not $ Set.null $ nticd ! n  ∩  s, not $ n ∈ nticdSliceM]
        tdep = tdepR g
        nticd = nticdF3 g
        slicer = nticdSlice g
        condNodes = [ n | n <- nodes g, length (suc g n) > 1 ]

type TimeMayDomFunctional = Map Node (Map Node Reachability) ->  Map Node (Map Node Reachability)
type TimeMayDomFunctionalGen gr a b = gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node]) -> TimeMayDomFunctional

fTimeMayDom :: DynGraph gr => TimeMayDomFunctionalGen gr a b
fTimeMayDom graph _ _ nextCond toNextCond = f 
  where f timeDomOf = -- traceShow timeDomOf $
                      Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                    ⊔ Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                               | y <- nodes graph
                                   ]
                    ⊔ Map.fromList [ (y, let all = (∐) [ Map.keysSet $ timeDomOf ! x | x <- suc graph n ] in
                                         let plus = joinPlus in
                                         fmap (\s -> s `plus` (steps + 1)) $
                                         Map.fromList [ (m, (∐) [  steps  | x <- suc graph n, Just steps <- [Map.lookup m (timeDomOf ! x)]   ]) | m <- Set.toList all, not $ m ∊ toNextCond y ]
                                     )
                                                                                   | y <- nodes graph,
                                                                                     Just n <- [nextCond y],
                                                                                     let steps = (toInteger $ length $ toNextCond y) - 1
                                   ]



type SnTimingEquationSystem =
       Map Node (Map Node Reachability)
type SnTimingEquationSystemGen gr a b =
       gr a b -> [Node] -> (Node -> [Node]) -> (Node -> Maybe Node) -> (Node -> [Node])
    -> SnTimingEquationSystem


timeMayDomEquationSystemGen :: DynGraph gr => SnTimingEquationSystemGen gr a b
timeMayDomEquationSystemGen graph condNodes _ nextCond toNextCond =
                      -- Map.fromList [ (y, Map.fromList [(y, FixedSteps 0    )]) | y <- nodes graph]
                      -- ⊔
                         Map.fromList [ (y, Map.fromList [(n, FixedSteps steps) | (n,steps) <- zip (reverse $ toNextCond y) [0..] ])
                                                                                | p <- condNodes, y <- suc graph p
                         ]

timeMayDomEquationSystem graph = timeMayDomEquationSystemGen graph condNodes reachable nextCond toNextCond
  where condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph



enumerateTimingDependence ::  DynGraph gr => gr a b -> Map Node (Set Node)
enumerateTimingDependence graph =
                     Map.fromList  [ (n, Set.empty) | n <- nodes graph ]
          ⊔   (∐)  [Map.fromList [ (n, Set.fromList [m] )]  | m <- nodes graph, n <- Set.toList $ enumerateTimingForUsing graph prevCondsWithSucc condsOf m ]
  where prevCondsWithSucc = (∐) [ Map.fromList [ (m, Set.fromList [(p,x,steps) ]) ] | p <- condNodes,
                                                                                       x <- suc graph p,
                                                                                       let toNextCondX = toNextCond x,
                                                                                       let m = head toNextCondX,
                                                                                       let steps = (toInteger $ length $ toNextCondX) - 1
                                ]
        condsOf = (∐) [ Map.fromList [ (x, Set.fromList [ p ]) ] | p <- condNodes, x <- suc graph p ]
                ⊔       Map.fromList [ (x, Set.empty         )   | x <- nodes graph ]
        condNodes = [ n | n <- nodes graph, isCond graph n ]
        toNextCond = toNextCondNode graph


enumerateTimingFor ::  DynGraph gr => gr a b -> Node -> Set Node
enumerateTimingFor graph = enumerateTimingForUsing graph prevCondsWithSucc condsOf
  where prevCondsWithSucc = (∐) [ Map.fromList [ (m, Set.fromList [(p,x,steps) ]) ] | p <- condNodes,
                                                                                       x <- suc graph p,
                                                                                       let toNextCondX = toNextCond x,
                                                                                       let m = head toNextCondX,
                                                                                       let steps = (toInteger $ length $ toNextCondX) - 1
                                ]
        condsOf = (∐) [ Map.fromList [ (x, Set.fromList [ p ]) ] | p <- condNodes, x <- suc graph p ]
                ⊔       Map.fromList [ (x, Set.empty         )   | x <- nodes graph ]
        condNodes = [ n | n <- nodes graph, isCond graph n ]
        toNextCond = toNextCondNode graph
enumerateTimingForUsing ::  DynGraph gr => gr a b -> (Map Node (Set (Node,Node,Integer))) -> Map Node (Set Node) -> Node -> Set Node
enumerateTimingForUsing graph prevCondsWithSucc condsOf m =
                             Set.fromList [ p | (p, sp) <- Map.assocs spx,
                                                sp == UndeterminedSteps
                             ]
          where nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                prevConds  = prevCondNodes graph
                -- spx = (∐) [ Map.fromList [ (p, sx) ] | (x,(_,_,sx)) <- Map.assocs $ (Map.union s0 s), p <- Set.toList $ condsOf ! x]
                spx = fmap (\sxs -> (∐) sxs) byCond
                  where byCond :: Map Node [Reachability]
                        byCond = foldr update Map.empty (Map.assocs $ Map.union s0 s)
                        update :: (Node, (Node, Integer, Reachability)) -> Map Node [Reachability] ->  Map Node [Reachability]
                        update (x,(_,_,sx)) m = foldr (Map.alter (cons sx)) m (condsOf ! x)
                          where cons sx  Nothing   = Just [sx]
                                cons sx (Just sxs) = Just (sx:sxs)
                s = solve Map.empty s0 Set.empty
                s0 :: Map Node (Node, Integer, Reachability)
                s0 = Map.fromList [ (x, (undefined, undefined, FixedSteps (toInteger steps))) | (p,x) <- prevCondsWithSuccNode graph m, let Just steps = List.findIndex (==m) (reverse $ toNextCond x)  ]
                solve s latest ps = -- traceShow latest $
                          if (s == s') then s else solve s' new (ps ∪ newPs)
                 where s' = Map.fromList [ (y, (n,steps,r)) | (y,(n,steps,_)) <- Map.assocs $ (Map.union new s),
                                                    let sxm =  (∐) [ sxm | x <- suc graph n, Just (_,_,sxm) <- [lookupEither x s0 s] ],
                                                    let r = case sxm of
                                                              FixedSteps j             -> FixedSteps (1+steps+j)
                                                              FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+steps+j) q'
                                                              UndeterminedSteps        -> FixedStepsPlusOther steps n
                            ]
                       new = Map.fromList $
                             [ (z, (p,steps,undefined))
                                 | p <- Set.toList $ newPs,
                                   Just prevConds <- [ Map.lookup p prevCondsWithSucc ],
                                   (_,z,steps) <- Set.toList $ prevConds,
                                   not $ Map.member z s0,
                                   not $ Map.member z s
                             ]
                       newPs = Set.fromList [ p | y <- Map.keys $ latest, p <- Set.toList $ condsOf ! y, not $ p ∈ ps ]
                lookupEither k m1 m2 = case Map.lookup k m1 of
                  Just v -> Just v
                  Nothing -> Map.lookup k m2

solveSnTimingEquationSystem ::  DynGraph gr => gr a b -> SnTimingEquationSystem -> SnTimingEquationSystem
solveSnTimingEquationSystem graph s = solve s0 0
          where nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                s0 = s
                solve s iterations = -- traceShow (s ! 3) $ traceShow (s ! 4) $ traceShow ("") $
                          if (s == s') then s else solve s' (iterations + 1)
                  where s' = Map.fromList [ (y, Map.union (s0 ! y) r) | (y, sy) <- Map.assocs s,
                                                                        let r = Map.fromList [ (m, case sxm of
                                                                                                     FixedSteps j             -> FixedSteps (1+steps+j)
                                                                                                     FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+steps+j) q'
                                                                                                     UndeterminedSteps        -> FixedStepsPlusOther steps n
                                                                                               )
                                                                                             | Just n <- [nextCond y],
                                                                                               let steps = (toInteger $ length $ toNextCond y) - 1,
                                                                                               let sx =  (∐) [ s ! x | x <- suc graph n ],
                                                                                               (m, sxm) <- Map.assocs sx
                                                                                ]
                            ]


solveSnTimingEquationSystemWorklist ::  forall gr a b. (DynGraph gr) => gr a b -> SnTimingEquationSystem -> SnTimingEquationSystem
solveSnTimingEquationSystemWorklist graph s0 = solve s0 worklist0 (Map.fromList [ (y, 0) | y <- Map.keys s0]) (Map.fromList [ (y, 0) | y <- Map.keys s0])
          where condNodes = [ x | x <- nodes graph, length (suc graph x) > 1 ]
                nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                prevConds   = prevCondNodes graph
                prevCondsWithSucc = prevCondsWithSuccNode graph
                (node2index, index2node) = ( Map.fromList [ (n, i) | (i,n) <- zip [0..] topsorted ],
                                             Map.fromList [ (i, n) | (i,n) <- zip [0..] topsorted ]
                                           )
                  where topsorted = topsort $ (fromSuccMap influencedNodes :: gr () ())
                        -- topsorted = reverse $ topsort graph
                worklist0 = Set.fromList [ node2index ! y | p <- condNodes, x <- suc graph p, (_,y) <- prevCondsWithSucc p]
                influencedNodes = Map.fromList [ (y, Set.fromList [ z | p <- pre graph y, (length $ suc graph p) > 1, (_,z) <- prevCondsWithSucc p ]) | y <- Map.keys s0 ]
                influenced = fmap (Set.map (node2index !)) influencedNodes
                solve :: Map Node (Map Node Reachability) -> Set Node -> Map Node Integer -> Map Node Integer -> Map Node (Map Node Reachability)
                solve s worklist iterations changes
                   | Set.null worklist  = -- traceShow ("SnTimingWorklist: ", iterations, changes, "Graph:\n", if ((length $ nodes graph) < 50 ∧ (Map.fold (+) 0 iterations) > 200) then graph else mkGraph [] [])
                                          s
                   | not changed        =      solve s   worklist'                (Map.update (\i -> Just $ i+1) y iterations)                                  changes
                   | otherwise          =      solve s' (worklist' ⊔ influencedY) (Map.update (\i -> Just $ i+1) y iterations) (Map.update (\i -> Just $ i+1) y changes)
                  where tr = traceShow (y,n, changed, Set.map (index2node !) worklist', Set.map (index2node !) influencedY)
                        (i, worklist') = Set.deleteFindMin worklist
                        y              = index2node ! i
                        toNextCondY = toNextCond y
                        n = head toNextCondY  -- assert (nextCond y == Just n)
                        steps = (toInteger $ length $ toNextCondY) - 1
                        sx =  (∐) [ s ! x | x <- suc graph n ]
                        sy  = (s  ! y)
                        sy' = Map.union (s0 ! y) $
                              Map.fromList [ (m, case sxm of
                                                     FixedSteps j             -> FixedSteps (1+steps+j)
                                                     FixedStepsPlusOther j q' -> FixedStepsPlusOther (1+steps+j) q'
                                                     UndeterminedSteps        -> FixedStepsPlusOther steps n
                                              )
                                            | (m, sxm) <- Map.assocs sx
                              ]
                        changed     = sy /= sy'
                        influencedY = (influenced ! y)
                        s'          = Map.insert y sy' s


solveSnTimingEquationSystemWorklist2 ::  forall gr a b. DynGraph gr => gr a b -> SnTimingEquationSystem -> SnTimingEquationSystem
solveSnTimingEquationSystemWorklist2 graph s0 = -- traceShow (s0, worklist0, finished0, influenced) $
                                                solve s0 worklist0 finished0 0 0
          where condNodes = [ x | x <- nodes graph, length (suc graph x) > 1 ]
                nextCond = nextCondNode graph
                toNextCond = toNextCondNode graph
                prevConds   = prevCondNodes graph
                influencedNodes = Map.fromList [ (y, Set.fromList [ (z, steps, p) | p <- pre graph y, (length $ suc graph p) > 1,
                                                                                         -- assert ((not $ Map.member p prevCondsWithSucc) → (prevCondsWithSuccNode graph p == [])) True,
                                                                                         -- assert (       Map.member p prevCondsWithSucc  → (   (Set.map (\(p,x,_) -> (p,x)) $ prevCondsWithSucc ! p)
                                                                                         --                                                    == (Set.fromList $  prevCondsWithSuccNode graph p)) ) True,
                                                                                         Just prevConds <- [Map.lookup p prevCondsWithSucc],
                                                                                         (_,z,steps) <- Set.toList $ prevConds
                                                             ]
                                            )
                                          | y <- Map.keys s0 ]
                influenced = fmap (Set.map (\(z,steps,p) -> (node2index ! z, steps, p))) influencedNodes

                prevCondsWithSucc = (∐) [ Map.fromList [ (m, Set.fromList [(p,x,steps) ]) ] | p <- condNodes,
                                                                                       x <- suc graph p,
                                                                                       let toNextCondX = toNextCond x,
                                                                                       let m = head toNextCondX,
                                                                                       let steps = (toInteger $ length $ toNextCondX) - 1
                                ]
                (node2index, index2node) = ( Map.fromList [ (n, i) | (i,n) <- zip [0..] topsorted ],
                                             Map.fromList [ (i, n) | (i,n) <- zip [0..] topsorted ]
                                           )
                  where topsorted = topsort $ (fromSuccMap (fmap (Set.map (\(z,_,_) -> z)) influencedNodes) :: gr () ())
                        --topsorted = reverse $ topsort graph
                worklist0 =  Map.fromList [ ((i,m), infl) | p <- condNodes, y <- suc graph p, infl@(i,steps,n) <- Set.toList $ influenced ! y, m <- toNextCond y, not $ (i,m) ∈ finished0]
                finished0 :: Set (Integer, Node)
                finished0 =  Set.fromList [  (i,m)             | p <- condNodes, y <- suc graph p, let i = node2index ! y,                     m <- toNextCond y]
                solve ::  SnTimingEquationSystem ->  Map (Integer, Node) (Integer, Integer, Node) -> Set (Integer, Node) -> Integer -> Integer ->  SnTimingEquationSystem
                solve s worklist finished iterations changes
                   | Map.null worklist  = s
                   | not changed        =      solve s   worklist'                                   finished (iterations+1)  changes
                   | otherwise          =      solve s' (worklist' `Map.union` influencedM)       newFinished (iterations+1) (changes + 1)
                  where tr = assert (n0 == n) $
                             assert (steps0 == steps) $
                             if (y == 180 ∧ m ∊ [-36, -22, 253]) then (
                             traceShow ((y,m),n, steps, changed, finishedY, sym', [ (x,sxm) | x <- suc graph n, Just sxm <- [Map.lookup m (s ! x)]], 
                                                                           Map.fromList [ ((index2node ! i, m), (steps, n)) | ((i,m), (_,steps,n)) <- Map.assocs worklist'],
                                                                           Map.fromList [ ((index2node ! i, m), (steps, n)) | ((i,m), (_,steps,n)) <- Map.assocs influencedM]
                                       )
                             ) else id 
                          where toNextCondY0 = toNextCond y
                                n0 = head toNextCondY0  -- assert (nextCond y == Just n)
                                steps0 = (toInteger $ length $ toNextCondY0) - 1
                        (((i,m),(_,steps,n)), worklist') = Map.deleteFindMin worklist
                        y = index2node ! i
                        msym  = Map.lookup m (s ! y)
                        sxm = (∐) [ sxm | x <- suc graph n, Just sxm <- [Map.lookup m (s ! x)]]
                        (finishedY, sym') = case sxm of
                                             FixedSteps j             -> (False, FixedSteps (1+steps+j))
                                             FixedStepsPlusOther j q' -> (False, FixedStepsPlusOther (1+steps+j) q')
                                             UndeterminedSteps        -> ((∀) (suc graph n) (\x -> case Map.lookup m (s ! x) of { Just (FixedSteps _) -> True ; _ -> False }),  FixedStepsPlusOther steps n)
                                             Unreachable              -> error (show $ (y,m,n))
                        newFinished
                          | finishedY = Set.insert (i, m) finished
                          | otherwise =                   finished
                        changed    = case msym of
                                       Just sym -> sym /= sym'
                                       Nothing  -> True
                        influencedM = Map.fromList [ ((iz,m), infl) | infl@(iz, steps, n) <- Set.toList $ influenced ! y,  not $ (iz,m) ∈ newFinished ]
                        s'          = Map.update (\sy -> Just $ Map.insert m sym' sy) y s

timingSnSolvedDependence :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSnSolvedDependence graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (p, Set.fromList [ m | let sx = (∐) [ s ! x  | x <- suc graph p ],
                                            (m, sxm) <- Map.assocs sx,
                                            sxm == UndeterminedSteps
                                      ]
                     ) | p <- condNodes
                  ]
  where s0 =  timeMayDomEquationSystem graph
        s  =  solveSnTimingEquationSystem graph s0
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


timingSnSolvedDependenceWorklist :: (DynGraph gr) => gr a b -> Map Node (Set Node)
timingSnSolvedDependenceWorklist graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (p, Set.fromList [ m | let sx = (∐) [ s ! x  | x <- suc graph p ],
                                            (m, sxm) <- Map.assocs sx,
                                            sxm == UndeterminedSteps
                                      ]
                     ) | p <- condNodes
                  ]
  where s0 =  timeMayDomEquationSystem graph
        s  =  solveSnTimingEquationSystemWorklist graph s0
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]

timingSnSolvedDependenceWorklist2 :: DynGraph gr => gr a b -> Map Node (Set Node)
timingSnSolvedDependenceWorklist2 graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (p, Set.fromList [ m | let sx = (∐) [ s ! x  | x <- suc graph p ],
                                            (m, sxm) <- Map.assocs sx,
                                            sxm == UndeterminedSteps
                                      ]
                     ) | p <- condNodes
                  ]
  where s0 =  timeMayDomEquationSystem graph
        s  =  solveSnTimingEquationSystemWorklist2 graph s0
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]




tmaydomOfLfp :: DynGraph gr => gr a b -> TimeMayDomFunctionalGen gr a b -> Map Node (Set (Node, Integer ))
tmaydomOfLfp graph f = fmap (\m -> Set.fromList [ (n, steps) | (n, ss) <- Map.assocs m, FixedSteps steps <- [ss] ]) $
-- tmaydomOfLfp :: DynGraph gr => gr a b -> TimeMayDomFunctionalGen gr a b -> Map Node (Set (Node, Reachability))
-- tmaydomOfLfp graph f = fmap (\m ->   Set.fromList [ (n, r) | (n, rs) <- Map.assocs m, r <- [rs] ]) $
        (㎲⊒) init (f graph condNodes reachable nextCond toNextCond)
  where init = Map.fromList [ (y, Map.empty) | y <- nodes graph]
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]
        reachable x = suc trncl x
        nextCond = nextCondNode graph
        toNextCond = toNextCondNode graph
        trncl = trc graph

timmaydomOfLfp graph = tmaydomOfLfp graph fTimeMayDom







alternativeTimingXdependence :: DynGraph gr => (gr a b -> Map (Node, Node) (Map (Node, Node) Reachability)) -> gr a b -> Map Node (Set Node)
alternativeTimingXdependence snmTiming graph = 
      Map.fromList [ (n, Set.empty) | n <- nodes graph]
    ⊔ Map.fromList [ (n, Set.fromList [ m | m <- nodes graph,
                                            let rmn = s ! (m,n),
                                            ((_,nl), rl) <- Map.assocs rmn,
                                            ((_,nr), rr) <- Map.assocs rmn,
                                            if (rl == Unreachable)       then error "unsolved snmTiming" else True,
                                            if (rr == Unreachable)       then error "unsolved snmTiming" else True,
                                            if (rl == UndeterminedSteps) then error "unsolved snmTiming" else True,
                                            if (rr == UndeterminedSteps) then error "unsolved snmTiming" else True,
                                            case (rl,rr) of
                                              (FixedSteps i, FixedSteps j)                         -> (i /= j)
                                              (FixedStepsPlusOther i l', FixedStepsPlusOther j r') -> (i /= j) ∨ (l' /= r')
                                              (FixedSteps i, _)                                    -> True 
                                              (_,            FixedSteps j)                         -> True 
                                              (_,            _)                                    -> False
                                      ]
                     ) | n <- condNodes
                  ]
  where s = snmTiming graph
        condNodes = [ n | n <- nodes graph, length (suc graph n) > 1 ]


alternativeTimingSolvedF3dependence :: DynGraph gr => gr a b -> Map Node (Set Node)
alternativeTimingSolvedF3dependence = alternativeTimingXdependence snmTimingSolvedF3


timingDependenceViaTwoFinger g =
      invert'' $
      Map.fromList [ (m, Set.fromList [ n | (n, Nothing) <- Map.assocs itimdom ])         | m <- nodes g,
                                                                                            let toM  = reachable m gRev,
                                                                                            let toMS = Set.fromList toM,
                                                                                            let (condNodes', noLongerCondNodes) = Map.partition isCond $ fmap (List.filter (∈ toMS)) $ Map.delete m  $ restrict condNodes toMS,
                                                                                            let usingMS = reachableFrom (fmap toSet itimdom) (Set.fromList [m]),
                                                                                            let imdom0' = id
                                                                                                  $ Map.insert m Nothing
                                                                                                  $ Map.union (Map.mapWithKey (\x [z] ->  assert (z /= x) $ Just (z,1)) noLongerCondNodes)
                                                                                                  $ Map.union (Map.mapMaybeWithKey (\x _ -> case itimdom ! x of { Just (z, _) -> if z ∈ usingMS then Just Nothing else Nothing ; _ -> Nothing }) condNodes')
                                                                                                  $ restrict itimdom toMS,
                                                                                            let g' = (flip delSuccessorEdges m) $ subgraph toM $ g,
                                                                                            let worklist0' = Map.filterWithKey (\x _ -> imdom0' ! x == Nothing) condNodes',
                                                                                            let itimdom = itimdomMultipleOfTwoFingerFor g' defaultCost condNodes' worklist0' imdom0' (invert''' $ fmap (liftM fst) $ imdom0'),
                                                                                        assert (itimdom == (fmap fromSet $ itimdomMultipleOfTwoFinger g')) True
                   ]
                                               
  where defaultCost = \_ _ -> 1
        gRev = grev g
        condNodes = Map.fromList [ (x, succs) | x <- nodes g, let succs = suc g x, length succs > 1 ]
        imdom0 =             Map.fromList [ (x, Just (z,1)) | x <- nodes g, [z] <- [suc g x]]
                 `Map.union` Map.fromList [ (x, Nothing   ) | x <- nodes g]
        itimdom = itimdomMultipleOfTwoFingerFor g defaultCost condNodes condNodes imdom0 (invert''' $ fmap (liftM fst) $ imdom0)

        toSet Nothing = Set.empty
        toSet (Just (z, steps)) = Set.singleton z
        isCond []  = False
        isCond [_] = False
        isCond _   = True


nticdTimingSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdTimingSlice graph =  combinedBackwardSlice graph (nticd' ⊔ timing') w
  where nticd'  = isinkDFTwoFinger graph
        timing' = invert'' $ timingDependenceViaTwoFinger graph
        w     = Map.empty


ntscdTimingSlice :: (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdTimingSlice graph =  combinedBackwardSlice graph (ntscd' ⊔ timing') w
  where ntscd'  = invert'' $ ntscdF3 graph
        timing' = invert'' $ timingDependenceViaTwoFinger graph
        w     = Map.empty
