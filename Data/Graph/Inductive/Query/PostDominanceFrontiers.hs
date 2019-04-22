{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
#define require assert

module Data.Graph.Inductive.Query.PostDominanceFrontiers where


import Control.Exception.Base (assert)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS (scc)


import Unicode
import Util(invert', the, invert''', dfsTree, roots, fromSet)
import IRLSOD(CFGNode)
import Program (Program)




import Data.Graph.Inductive.Util (immediateOf, controlSinks)
import Data.Graph.Inductive.Query.Dependence (Dependence)
import Data.Graph.Inductive.Query.PostDominance (domsOf, onedomOf, sinkdomOf, sinkdomsOf, mdomOfLfp, mdomOf, mdomsOf, imdomOfTwoFinger7, isinkdomOfTwoFinger8ForSinks)
import Data.Graph.Inductive.Query.NTICD.Util (cdepGraph, cdepGraphP)



noJoins :: Graph gr => gr a b -> Map Node (Set Node) -> Bool
noJoins g m = (∀) (nodes g) (\x -> (∀) (nodes g) (\z -> (∀) (nodes g) (\v -> (∀) (nodes g) (\s ->
                if (z /= v) ∧ (x ∈ doms ! v) ∧ (x ∈ doms ! z) ∧ (v ∈ m ! s) ∧ (z ∈ m ! s) then (v ∈ doms ! z) ∨ (z ∈ doms ! v) else True
              ))))
  where doms = domsOf g m


noJoinLfps :: Graph gr => gr a b -> Map Node (Set Node) -> [ Map Node (Set Node) ]
noJoinLfps g dom
    | violations == [] = assert (noJoins g dom) [dom]
    | otherwise        = do
                      (x, z, v, s) <- violations
                      (n,n') <- assert (z /= v) [(z,v),(v,z)]
                      let dom' = dom ⊔ Map.fromList [ (n, Set.fromList [n'])] ⊔ Map.fromList [ (m, Set.fromList [n']) | m <- Set.toList $ doms ! n ]
                      noJoinLfps g dom'
 where violations = [ (x, z, v, s) | s <- nodes g, v <- Set.toList $ dom ! s, z  <- Set.toList $ dom ! s, z /= v, x <- nodes g,  x ∈ doms ! v, x ∈ doms ! z,  not (v ∈ doms ! z), not (z ∈ doms ! v)]
       doms = domsOf g dom


stepsCL g dom = (∀) (nodes g) (\x -> (∀) (nodes g) (\y -> (∀) (nodes g) (\x' ->
             if (x' /= y) ∧ (y `elem` pre g x) ∧ (x' ∈ dom ! y) then (x'  ∈ dom ! x) else True
           )))


stepsCLLfp g dom = (㎲⊒) dom f
  where f dom = dom ⊔ Map.fromList [ (x, Set.fromList [ x' | y <- pre g x, x' <- Set.toList $ dom ! y, x' /= y ] ) | x <- nodes g ]
--                  ⊔ Map.fromList [ (y, (∏) [ dom ! y' | y' <- suc g y])                                          | y <- nodes g, suc g y /= [] ]




anyDFLocalDef anydom graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ onedom y  ])
                   | x <- nodes graph ]
  where onedom = onedomOf anydom





anyDFUpGivenXViaAnydomsDef :: forall gr a b. DynGraph gr => Map Node (Set Node) -> gr a b -> Map (Node, Node) (Set Node)
anyDFUpGivenXViaAnydomsDef anydom graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ anydf ! z,
                                                not $ x ∈ onedom y
                                      ]
                     )
                   | z <- nodes graph,  x <- Set.toList $ anydoms ! z]
  where anydoms = domsOf graph anydom
        anydf   = dfFor graph anydom
        onedom  = onedomOf anydom




anyDFFromUpLocalDefViaAnydoms :: forall gr a b. DynGraph gr => Map Node (Set Node) -> gr a b -> Map Node (Set Node)
anyDFFromUpLocalDefViaAnydoms anydom graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, Set.fromList [ y | z <- anydomsInv ! x,
                                            y <- Set.toList $ dfupGivenX ! (x,z),
                                    assert ((not $ z ∈ anydoms ! x)  → ((∃) (suc graph y) (\y' -> x ∈ anydom ! y'))) True,
                                            (∃) (suc graph y) (\y' -> x ∈ anydom ! y')  ] ) | x <- nodes graph]
  where dflocal = anyDFLocalDef anydom graph
        dfupGivenX = anyDFUpGivenXViaAnydomsDef anydom graph
        anydoms    = domsOf graph anydom
        anydomsInv = invert' (fmap Set.toList anydoms) `Map.union` (Map.fromList [ (x, []) | x <- nodes graph ])




sinkDF graph =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈ sinkdom ! p,
                                            not $  x ∈ onedom    y ])
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph
        onedom = onedomOf sinkdom

dfFor graph dom =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈ dom ! p,
                                            not $  x ∈ onedom    y ])
                   | x <- nodes graph ]
  where onedom = onedomOf dom


sinkDFGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFGraphP = cdepGraphP sinkDFGraph

sinkDFGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFGraph = cdepGraph sinkDFcd

sinkDFcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFcd = xDFcd sinkDF


sinkDFLocalDef graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ onedom y  ])
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph
        onedom = onedomOf sinkdom




sinkDFLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFLocal graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            (∀) (suc isinkdom y) (\z -> not $ x ∊ (isinkdomSccOf z))
                                      ]
                     )
                   | x <- nodes graph ]
  where sinkdom = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()
        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs

sinkDFLocalViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFLocalViaSinkdoms graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ sinkdoms ! y
                                      ]
                     )
                   | x <- nodes graph ]
  where sinkdoms = sinkdomsOf graph



sinkDFUpDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUpDef graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                            (∀) (suc isinkdom z) (\c ->  (∀) (isinkdomSccOf c)  (\x -> (not $ x ∈ sinkdom ! y)  ∨  x == y))
                                      ]
                     )
                   | z <- nodes graph, (∃) (suc isinkdom z) (\x -> True)]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs

sinkDFUpDefViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUpDefViaSinkdoms graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                            (∀) (sinkdoms ! z) (\x -> not $ x ∈ onedom y)
                                      ]
                     )
                   | z <- nodes graph,  (∃) (sinkdoms ! z) (\x -> True)]
  where sinkdom  = sinkdomOf graph
        sinkdoms = sinkdomsOf graph
        sinkdf   = sinkDF graph
        onedom = onedomOf sinkdom

sinkDFUpGivenXViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
sinkDFUpGivenXViaSinkdoms graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                not $ x ∈ sinkdoms ! y
                                      ]
                     )
                   | z <- nodes graph,  x <- Set.toList $ sinkdoms ! z]
  where sinkdom  = sinkdomOf graph
        sinkdoms = sinkdomsOf graph
        sinkdf   = sinkDF graph

sinkDFUpGivenX :: forall gr a b. DynGraph gr => gr a b -> Map (Node,Node) (Set Node)
sinkDFUpGivenX graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                (∀) (suc isinkdom y) (\c ->  not $ x ∊ (isinkdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, c <- suc isinkdom z,  x <- isinkdomSccOf c]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs


sinkDFUp :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFUp graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ sinkdf ! z,
                                                assert (
                                                (∀) (suc isinkdom y)                                (/=x)
                                                ↔
                                                (∀) (suc isinkdom y) (\c ->  not $ x ∊ (isinkdomSccOf c))
                                                ) True,
                                                
                                                (∀) (suc isinkdom y) (\c ->  not $ x ∊ (isinkdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, assert ((length $ suc isinkdom z) <= 1) True,  [x] <- [suc isinkdom z]]
  where sinkdom  = sinkdomOf graph
        sinkdf   = sinkDF graph
        isinkdom = immediateOf sinkdom :: gr () ()

        isinkdomSccs = scc isinkdom
        isinkdomSccOf m =   the (m ∊) $ isinkdomSccs




sinkDFFromUpLocalDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocalDef graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- pre isinkdom x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocalDef graph
        dfup = sinkDFUpDef graph
        sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()

sinkDFFromUpLocalDefViaSinkdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocalDefViaSinkdoms graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- sinkdomsInv ! x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocalDef graph
        dfup = sinkDFUpDefViaSinkdoms graph
        sinkdoms  = sinkdomsOf graph
        sinkdomsInv = invert' (fmap Set.toList sinkdoms) `Map.union` (Map.fromList [ (x, []) | x <- nodes graph ]) 




sinkDFFromUpLocalDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFFromUpLocalDefGraphP = cdepGraphP sinkDFFromUpLocalDefGraph

sinkDFFromUpLocalDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFFromUpLocalDefGraph = cdepGraph sinkDFFromUpLocalDefcd

sinkDFFromUpLocalDefcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFFromUpLocalDefcd = xDFcd sinkDFFromUpLocalDef



sinkDFFromUpLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFFromUpLocal graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z | z <- pre isinkdom x  ] ) | x <- nodes graph]
  where dflocal = sinkDFLocal graph
        dfup = sinkDFUp graph
        sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()


sinkDFFromUpLocalGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFFromUpLocalGraphP = cdepGraphP sinkDFFromUpLocalGraph

sinkDFFromUpLocalGraph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFFromUpLocalGraph = cdepGraph sinkDFFromUpLocalcd

sinkDFFromUpLocalcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFFromUpLocalcd = xDFcd sinkDFFromUpLocal


sinkDFF2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
sinkDFF2 graph = idomToDF graph isinkdom
  where sinkdom  = sinkdomOf graph
        isinkdom = immediateOf sinkdom :: gr () ()


sinkDFF2GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
sinkDFF2GraphP = cdepGraphP sinkDFF2Graph

sinkDFF2Graph :: DynGraph gr => gr a b ->  gr a Dependence
sinkDFF2Graph = cdepGraph sinkDFF2cd

sinkDFF2cd :: DynGraph gr => gr a b ->  Map Node (Set Node)
sinkDFF2cd = xDFcd sinkDFF2

xDFcd :: DynGraph gr => (gr a b -> Map Node (Set Node)) -> gr a b ->  Map Node (Set Node)
xDFcd xDF graph                  = Map.fromList [ (n, Set.empty)       | n <- nodes graph]
                                 ⊔ Map.fromList [ (n, Set.delete n ns) | (n,ns) <- Map.assocs $
                                                                            (fmap Set.fromList $ invert' $ fmap Set.toList df )
                                                ]
  
  where df = xDF graph








mDF graph =
      Map.fromList [ (x, Set.fromList [ y | y <- nodes graph,
                                            p <- suc graph y,
                                                   x ∈   mdom ! p,
                                            not $  x ∈ onedom   y ])
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph
        onedom = onedomOf mdom


mDFGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFGraphP = cdepGraphP sinkDFGraph

mDFGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFGraph = cdepGraph mDFcd

mDFcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFcd = xDFcd mDF


mDFLocalDef graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ onedom y  ])
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph
        onedom = onedomOf mdom




mDFLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFLocal graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            (∀) (suc imdom y) (\z -> not $ x ∊ (imdomSccOf z))
                                      ]
                     )
                   | x <- nodes graph ]
  where mdom = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs


mDFLocalViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFLocalViaMdoms graph =
      Map.fromList [ (x, Set.fromList [ y | y <- pre graph x,
                                            not $ x ∈ mdoms ! y
                                      ]
                     )
                   | x <- nodes graph ]
  where mdoms = mdomsOf graph


mDFUpDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUpDef graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                            (∀) (suc imdom z) (\c ->  (∀) (imdomSccOf c) (\x -> (not $ x ∈ mdom ! y)  ∨  x == y))
                                      ]
                     )
                   | z <- nodes graph,  (∃) (suc imdom z) (\x -> True)]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs

mDFUpDefViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUpDefViaMdoms graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                            (∀) (mdoms ! z) (\x -> not $ x ∈ onedom y)
                                      ]
                     )
                   | z <- nodes graph,  (∃) (mdoms ! z) (\x -> True)]
  where mdom  = mdomOf graph
        mdoms = mdomsOf graph
        mdf   = mDF graph
        onedom = onedomOf mdom
        
mDFUpGivenXViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map (Node, Node) (Set Node)
mDFUpGivenXViaMdoms graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                not $ x ∈ mdoms ! y
                                      ]
                     )
                   | z <- nodes graph,  x <- Set.toList $ mdoms ! z]
  where mdom  = mdomOf graph
        mdoms = mdomsOf graph
        mdf   = mDF graph

mDFUpGivenX :: forall gr a b. DynGraph gr => gr a b -> Map (Node,Node) (Set Node)
mDFUpGivenX graph =
      Map.fromList [ ((x,z), Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                (∀) (suc imdom y) (\c ->  not $ x ∊ (imdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, c <- suc imdom z, x <- imdomSccOf c]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs


mDFUp :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFUp graph =
      Map.fromList [ (z, Set.fromList [ y | y <- Set.toList $ mdf ! z,
                                                (∀) (suc imdom y) (\c -> not $ x ∊  (imdomSccOf c))
                                      ]
                     )
                   | z <- nodes graph, assert ((length $ suc imdom z) <= 1) True,  [x] <- [suc imdom z]]
  where mdom  = mdomOfLfp graph
        mdf   = mDF graph
        imdom = immediateOf mdom :: gr () ()
        imdomSccs = scc imdom
        imdomSccOf m =   the (m ∊) $ imdomSccs


mDFFromUpLocalDef :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocalDef graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- pre imdom x  ] ) | x <- nodes graph]
  where dflocal = mDFLocalDef graph
        dfup = mDFUpDef graph
        mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()

mDFFromUpLocalDefViaMdoms :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocalDefViaMdoms graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z  | z <- mdomsInv ! x  ] ) | x <- nodes graph]
  where dflocal = mDFLocalDef graph
        dfup = mDFUpDefViaMdoms graph
        mdoms  = mdomsOf graph
        mdomsInv = invert' (fmap Set.toList mdoms) `Map.union` (Map.fromList [ (x, []) | x <- nodes graph ])


mDFFromUpLocalDefGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFFromUpLocalDefGraphP = cdepGraphP mDFFromUpLocalDefGraph

mDFFromUpLocalDefGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFFromUpLocalDefGraph = cdepGraph mDFFromUpLocalDefcd

mDFFromUpLocalDefcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFFromUpLocalDefcd = xDFcd mDFFromUpLocalDef




mDFFromUpLocal :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFFromUpLocal graph =
      Map.fromList [ (x, dflocal ! x)  | x <- nodes graph]
    ⊔ Map.fromList [ (x, (∐) [ dfup ! z | z <- pre imdom x  ] ) | x <- nodes graph]
  where dflocal = mDFLocal graph
        dfup = mDFUp graph
        mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()


mDFFromUpLocalGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFFromUpLocalGraphP = cdepGraphP mDFFromUpLocalGraph

mDFFromUpLocalGraph :: DynGraph gr => gr a b ->  gr a Dependence
mDFFromUpLocalGraph = cdepGraph mDFFromUpLocalcd

mDFFromUpLocalcd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFFromUpLocalcd = xDFcd mDFFromUpLocal



mDFF2 :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFF2 graph = idomToDF graph imdom
  where mdom  = mdomOfLfp graph
        imdom = immediateOf mdom :: gr () ()

mDFF2GraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
mDFF2GraphP = cdepGraphP mDFF2Graph

mDFF2Graph :: DynGraph gr => gr a b ->  gr a Dependence
mDFF2Graph = cdepGraph mDFF2cd

mDFF2cd :: DynGraph gr => gr a b ->  Map Node (Set Node)
mDFF2cd = xDFcd mDFF2



idomToDF :: forall gr a b. DynGraph gr => gr a b -> gr () () -> Map Node (Set Node)
idomToDF graph idomG = 
      (㎲⊒) (Map.fromList [(x, Set.empty) | x <- nodes graph]) f2
  where f2 df = df ⊔ 
           Map.fromList [ (x, (∐) [ Set.fromList [ y ] | y <- pre graph x,
                                                         (∀) (suc idomG y) (\c -> not $ x ∊ (idomSccOf ! c))
                                   ]
                          )
                        | x <- nodes graph]
         ⊔ Map.fromList [ (x, (∐) [ Set.fromList [ y ] | z <- pre idomG x,
                                                          y <- Set.toList $ df ! z,
                                                         (∀) (suc idomG y) (\c -> not $ x ∊ (idomSccOf ! c))
                                   ])
                        | x <- nodes graph]
        idomSccs = scc idomG
        idomSccOf = Map.fromList [ (c, cycle) | cycle <- idomSccs, c <- cycle ]

idomToDFFastForRoots :: forall gr a b. Graph gr => [[Node]] -> gr a b -> Map Node (Maybe Node) -> Map Node (Set Node)
idomToDFFastForRoots roots graph idom = foldr f2 Map.empty sorting
  where f2 cycle df = Map.fromSet (\x -> combined) cycle `Map.union` df
          where combined = (local ∪ up) ∖ invalid
                local = Set.fromList [ y                | x <- Set.toList cycle, 
                                                          y <- pre graph x
                                   ]
                up    = Set.unions [ us                 | z <- Set.toList invalid,
                                                          Just us <- [Map.lookup z df],
                                                  assert ((not $ Set.null $ us) → (not $ z ∈ cycle)) True
                                   ]
                invalid =  Set.unions [ is | x <- Set.toList cycle, Just is <- [Map.lookup x idom'] ]

        rs = fmap Set.fromList $ roots
        idom' :: Map Node (Set Node)
        idom' = invert''' idom

        sorting :: [Set Node]
        sorting = dfsTree idom' rs

idomToDFFast graph idom = idomToDFFastForRoots (roots idom) graph (fmap fromSet idom)



idomToDFFastLazy :: forall gr a b. Graph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node) -> Map Node (Set Node) -> Node -> (Set Node, Map Node (Set Node))
idomToDFFastLazy graph cycleOf idom' = \df x -> case Map.lookup x df of
    Just dfs -> (dfs, df)
    Nothing  -> let cycle = Map.findWithDefault (Set.singleton x) x cycleOf
                    combined = (local ∪ up) ∖ invalid
                    local = Set.fromList [ y            | x <- Set.toList cycle, 
                                                          y <- pre graph x
                                   ]
                    (up, df') =  Set.fold f (Set.empty, df) (invalid ∖ cycle)
                      where f z (up, df) = let (us,df') = idomToDFFastLazy graph cycleOf idom' df z in (up ∪ us, df')
                    
                    invalid =  Set.unions [ is | x <- Set.toList cycle, Just is <- [Map.lookup x idom'] ]
                in (combined, Map.fromSet (\x -> combined) cycle `Map.union` df')






mDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
mDFTwoFinger graph = idomToDFFast graph $ imdomOfTwoFinger7 graph

imdomTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
imdomTwoFingerGraphP = cdepGraphP imdomTwoFingerGraph

imdomTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
imdomTwoFingerGraph = cdepGraph imdomTwoFingercd

imdomTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
imdomTwoFingercd = xDFcd mDFTwoFinger


isinkDFTwoFingerForSinks :: forall gr a b. DynGraph gr => [[Node]] -> gr a b ->  Map Node (Set Node)
isinkDFTwoFingerForSinks sinks graph =
    require (Set.fromList sinks == Set.fromList (controlSinks graph)) $
    idomToDFFastForRoots roots graph idom
  where 
        sinkNodes        = (∐) [ Set.fromList sink | sink <- sinks]
        nonSinkCondNodes = Map.fromList [ (n, succs) | n <- nodes graph, not $ n ∈ sinkNodes, let succs = suc graph n, length succs > 1 ]

        idom = isinkdomOfTwoFinger8ForSinks sinks sinkNodes nonSinkCondNodes graph
        roots = go (Map.assocs idom) [ sink | sink@(_:_:_) <- sinks ]
          where go []     roots = roots
                go ((n, m):as) roots = case m of 
                  Nothing -> go as ([n]:roots)
                  _       -> go as      roots

isinkDFTwoFinger :: forall gr a b. DynGraph gr => gr a b -> Map Node (Set Node)
isinkDFTwoFinger graph = isinkDFTwoFingerForSinks sinks graph
  where sinks = controlSinks graph


isinkdomTwoFingerGraphP :: DynGraph gr => Program gr -> gr CFGNode Dependence
isinkdomTwoFingerGraphP = cdepGraphP isinkdomTwoFingerGraph

isinkdomTwoFingerGraph :: DynGraph gr => gr a b ->  gr a Dependence
isinkdomTwoFingerGraph = cdepGraph isinkdomTwoFingercd

isinkdomTwoFingercd :: DynGraph gr => gr a b ->  Map Node (Set Node)
isinkdomTwoFingercd = xDFcd isinkDFTwoFinger


nticdSliceLazy :: DynGraph gr => gr a b -> Map Node (Set Node) -> Map Node (Set Node) -> Set Node -> Set Node
nticdSliceLazy graph cycleOf idom' = \ms ->
     let result = slice Map.empty Set.empty ms 
         slice df s workset 
             | Set.null workset = s
             | otherwise        = slice df' s' workset'
           where (m, workset0) = Set.deleteFindMin workset
                 s'  = Set.insert m s
                 new = fromNTICD ∖ s'
                 workset' = workset0 ∪ new

                 (fromNTICD, df') = idomToDFFastLazy graph cycleOf idom' df m
      in result
