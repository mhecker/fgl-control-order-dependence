{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Program.Properties.CDom where

-- import Algebra.Lattice
import Util

import Unicode
import Data.Bool.Unicode

import Program
import Program.For
import Program.MHP
-- import Program.MultiThread
import Program.CDom
import Program.Generator
import Execution
import ExecutionTree

import Debug.Trace (traceShow)

import IRLSOD

-- import Data.Graph.Inductive.Util
-- import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree


import Data.List (takeWhile, dropWhile)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.List(nub, (\\))
import Data.Tree

import Data.Util
-- import Data.Set.Unicode

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util (trr, isTransitive)
import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Query.TimingDependence
import Data.Graph.Inductive.Query.DFS (scc)



domMhpProperty :: DynGraph gr => Program gr -> Bool
domMhpProperty p@(Program {tcfg, entryOf, procedureOf, mainThread}) =
    (∀) (nodes tcfg) (\n ->
      (∀) (reachableFromTree dom n) (\n' -> if n' ∈ mhps ! n then True else
        (∀) (reachableFromTree dom n') (\n'' -> not $ n'' ∈ mhps ! n)
      )
    )
  where dom :: Map Node (Set Node)
        dom = fmap toSet $ Map.insert n0 Nothing $ fmap Just $ Map.fromList $ iDom tcfg n0
        n0 = (entryOf $ procedureOf $ mainThread)

        mhp = mhpSetFor p
        mhps = Map.fromList [ (n, Set.fromList [ m | (n',m) <- Set.toList mhp, n' == n]) | n <- nodes tcfg ]

isMorePreciceThan :: DynGraph gr => Program gr ->  (Program gr ->  Map (Node,Node) Node) ->  (Program gr ->  Map (Node,Node) Node)  -> Bool
isMorePreciceThan p@(Program {tcfg, entryOf, procedureOf, mainThread}) cdc cdc' =
    (∀) (Map.assocs cdom) (\((n,m),c) -> let c' = cdom' ! (n,m) in isReachableFromTreeM dom c' c)
  where dom :: Map Node (Maybe Node)
        dom = Map.insert n0 Nothing $ fmap Just $ Map.fromList $ iDom tcfg n0
        n0 = (entryOf $ procedureOf $ mainThread)
        
        cdom  = cdc  p
        cdom' = cdc' p


isCdom ::  DynGraph gr => Program gr -> (Program gr ->  Map (Node,Node) Node) -> Bool
isCdom p@(Program {tcfg, entryOf, procedureOf, mainThread}) cd =
    (∀) (Map.assocs cdom) (\((n,m),c) ->
      let ok = isReachableFromTreeM dom c m ∧ isReachableFromTreeM dom c n ∧ (not $ c ∈ mhps ! m) ∧ (not $ c ∈ mhps ! n)
      in if ok then ok else traceShow (n,m,c) ok
    )

  where dom :: Map Node (Maybe Node)
        dom = Map.insert n0 Nothing $ fmap Just $ Map.fromList $ iDom tcfg n0

        n0 = (entryOf $ procedureOf $ mainThread)

        mhp = mhpSetFor p
        mhps = Map.fromList [ (n, Set.fromList [ m | (n',m) <- Set.toList mhp, n' == n]) | n <- nodes tcfg ]

        cdom = cd p



cdomIsDomViolations :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsDomViolations p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          e <- θ,
          let hb = someHappensBeforeAll e,
          (not (occurencesOf e n == [] ∨  c `hb` n))
          ∨
          (not (occurencesOf e m == [] ∨  c `hb` m))
    ]
  where cdom = cd p



cdomIsCdomViolations :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsCdomViolations p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          e <- θ,
          not $
          (∀) (occurencesOf e n) (\(i,n) ->
          (∀) (occurencesOf e m) (\(j,m) ->
          (∃) (occurencesOf e c) (\(k,c) -> k <= i
                                         && k <= j)))
    ]
  where cdom = cd p

cdomIsCdomViolations' :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsCdomViolations' p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          e <- θ,
          not $
          (∀) (occurencesOf e n) (\(i,n) ->
          (∀) (occurencesOf e m) (\(j,m) ->
              (¬) ((∃) (occurencesOf e c) (\(k,c) -> i < k && k < j))
          ))
    ]
  where cdom = cd p


cdomIsCdomViolations'For :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> Node -> Node -> [(Node,Node,Trace)]
cdomIsCdomViolations'For p@(Program {tcfg}) θ cd n m =
    [ (n,m, toTrace e) |
          let  c = cdom ! (n,m),
          e <- θ,
          not $
          (∀) (occurencesOf e n) (\(i,n) ->
          (∀) (occurencesOf e m) (\(j,m) ->
              (¬) ((∃) (occurencesOf e c) (\(k,c) -> i < k && k < j))
          ))
    ]
  where cdom = cd p


cdomIsBeforeViolations :: DynGraph gr => Program gr -> [ExecutionTrace] -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node,Trace)]
cdomIsBeforeViolations p@(Program {tcfg}) θ cd =
    [ (n,m, toTrace e) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          e <- θ,
          let  c  = cdom ! (n,m),
          let  hb = happensBefore e,
          (not (occurencesOf e n == [] ∨  c `hb` n))
          ∨
          (not (occurencesOf e m == [] ∨  c `hb` m))
    ]
  where cdom = cd p


occurencesOf e n = [ (i,n') | (i,(_,(n',_,_),_)) <- e', n' == n]
  where e' = zip [1..] e

someHappensBeforeAll :: ExecutionTrace -> Node -> Node -> Bool
someHappensBeforeAll e n m =
          ((∃) (take 1 $ occurencesOf e n) (\(i,n) ->
           (∀) (         occurencesOf e m) (\(j,m) -> i <= j)))

happensBefore :: ExecutionTrace -> Node -> Node -> Bool
happensBefore e n m =
          ((∃) (take 1 $ occurencesOf e n) (\(i,n) ->
           (∃) (         occurencesOf e m) (\(j,m) -> i <= j)))


cdomIsTreeDomViolations :: DynGraph gr => Program gr -> [ExecutionTree] -> (Program gr -> Map (Node,Node) Node) -> [(Node,Node,ExecutionTree)]
cdomIsTreeDomViolations p@(Program {tcfg}) θ cd =
    [ (n,m, t) |
          n <- nodes tcfg,
          m <- nodes tcfg,
          let  c = cdom ! (n,m),
          t <- θ,
          let tpaths = Set.fromList $ paths t,
          (not $ (∀) tpaths (c `allOrderedBeforeAll` n)) ∨
          (not $ (∀) tpaths (c `allOrderedBeforeAll` m))
    ]
  where cdom = cd p
        allOrderedBeforeAll c n path =
              (c == n ∧ length [ n' | n' <- ns, n == n'] == 1)
            ∨ (not $ (c ∊ dropWhile (/=n) ns))
          where ns = [ n' | (n',e,tlσ) <- path ] 



chopPathsAreDomPaths :: DynGraph gr => (Program gr ->  Map (Node,Node) Node) -> Program gr -> Bool
chopPathsAreDomPaths cd p@(Program { tcfg, observability, entryOf, procedureOf, mainThread }) =
    (∀) [ (n,m) | (n,m) <- Set.toList mhp]
        (\(n,m) -> let c = idom ! (n,m) in
                                                                                                          (chop c n) ∩ (Set.fromList (pre timing n)) ==
                   (Set.unions [ chop a b |  (a,b) <- consecutive $ [ y |  x <- domPathBetween n c , y <- [x,x] ] ]) ∩ (Set.fromList (pre timing n))
        )
 where dom :: Map Node Node
       dom = Map.fromList $ iDom tcfg (entryOf $ procedureOf $ mainThread)

       domPathBetween dominated dominator
                 | dominated  == dominator = [dominated]
                 | otherwise               = domPathBetween dominated' dominator ++ [dominated]
          where Just dominated' = Map.lookup dominated dom

       idom = cd p
       mhp = mhpSetFor p
       trnsclos = trc tcfg
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance


chopPathsAreDomPaths2 :: DynGraph gr => (Program gr ->  Map (Node,Node) Node) -> Program gr -> Bool
chopPathsAreDomPaths2 cd p@(Program { tcfg, observability, entryOf, procedureOf, mainThread }) =
    (∀) [ (n,m) | (n,m) <- Set.toList mhp]
        (\(n,m) -> let c = idom ! (n,m) in
                                                                                                          (chop c n) ∩ (Set.fromList (pre timing n)) ==
                   (Set.unions [ chop a b ∩ (Set.fromList (pre timing b)) |  (a,b) <- consecutive $ [ y |  x <- domPathBetween dom n c , y <- [x,x] ] ])
        )
 where dom :: Map Node Node
       dom = Map.fromList $ iDom tcfg (entryOf $ procedureOf $ mainThread)
       idom = cd p
       mhp = mhpSetFor p
       trnsclos = trc tcfg
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance

-- chopPathsAreDomPathsViolations :: DynGraph gr => Program gr -> (Program gr ->  Map (Node,Node) Node) -> [(Node,Node)]
chopPathsAreDomPathsViolations cd p@(Program { tcfg, observability, entryOf, procedureOf, mainThread }) =
    [ (n,m,c,chop1, chop2, path) | (n,m) <- Set.toList mhp,
              let c = idom ! (n,m),
              let chop1 = (chop c n) ∩ (Set.fromList (pre timing n)),
              let path = domPathBetween dom n c,
              let chop2 = (Set.unions [ chop a b |  (a,b) <- consecutive $ [ y |  x <- domPathBetween dom n c , y <- [x,x] ] ]) ∩ (Set.fromList (pre timing n)),
              chop1 /= chop2
    ]
 where dom :: Map Node Node
       dom = Map.fromList $ iDom tcfg (entryOf $ procedureOf $ mainThread)

       idom = cd p
       mhp = mhpSetFor p
       trnsclos = trc tcfg
       timing = timingDependenceGraphP p
       chop :: Node -> Node -> Set Node
       chop s t =   (Set.fromList $ suc trnsclos s)
                  ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance




idomIsTreeGraph ::  forall gr. DynGraph gr => gr CFGNode CFGEdge -> Node -> Map (Node,Node) Node -> Bool
idomIsTreeGraph tcfg entry idom =
    (∀) (scc tree)               (\scc -> length scc == 1)
 ∧  (isTransitive tree)
 ∧  (∀) (nodes tree  \\ [entry]) (\n   -> (hasEdge tree' (entry,n)) ∧ (length (pre tree0 n) == 1))
   where tree :: gr CFGNode ()
         tree =  mkGraph (labNodes tcfg)
                         (nub [ (c,m,()) | ((n,n'),c) <- Map.assocs idom, m  <- [ n, n']])
         tree' = trc tree
         tree0 = trr tree


idomIsTree ::  forall gr. DynGraph gr => Program gr -> Map (Node,Node) Node -> Bool
idomIsTree p@(Program { tcfg, observability, entryOf, procedureOf, mainThread }) idom = idomIsTreeGraph tcfg entry idom
   where entry = entryOf $ procedureOf $ mainThread

idomIsTreeProgram :: (Program Gr -> Map (Node,Node) Node) -> Program Gr -> Bool
idomIsTreeProgram cdomComputation p = idomIsTree p idom
  where idom = cdomComputation  p


-- asserts that conversion from a cdom relation to an underlying domination tree via idomToTree is "sound",
-- in that at least for the naiive cdom relation "idomChef", exactly the underlying domTree is returned
idomChefTreeIsDomTree :: Program Gr -> Bool
idomChefTreeIsDomTree p = (toMap $ idomToTree (idomChef p)) == (invert dom)
  where dom :: Map Node Node
        dom = Map.fromList $ iDom (tcfg p) (entryOf p $ procedureOf p $ mainThread p)

toMap :: Graph gr => gr Node () -> Map Node (Set Node)
toMap tree = Map.fromList [ (n,Set.fromList sucs) | n <- nodes tree, let sucs = suc tree n, (¬) (null sucs) ]

chopsCdomArePrefixes :: (Program Gr -> Map (Node,Node) Node) -> Program Gr -> Bool
chopsCdomArePrefixes cdomComputation p =
    -- (∀) (Map.assocs cdom) (\((n,n'),c) -> let [ndom]  = pre idom n
    --                                           [ndom'] = pre idom n'
    --                                       in  (not $ null $ pre idom n )
    --                                         ∧ (not $ null $ pre idom n')
    --                                         ∧ (∃) (pre idom n ) (\ndom  -> (c == n  ∨ chop c n  == (chop c ndom ) ∪ (chop ndom  n )))
    --                                         ∧ (∃) (pre idom n') (\ndom' -> (c == n' ∨ chop c n' == (chop c ndom') ∪ (chop ndom' n')))
    --                       )
    (∀) (Map.assocs cdom) (\((n,n'),c) -> let [ndom]  = pre idom n
                                              [ndom'] = pre idom n'
                                          in  (length (pre idom n) == 1) ∧ (length (pre idom n') == 1)
                                            ∧ (c == n  ∨ chop c n  == (chop c ndom ) ∪ (chop ndom  n ))
                                            ∧ (c == n' ∨ chop c n' == (chop c ndom') ∪ (chop ndom' n'))
                          )
  where cdom = cdomComputation p

        idom = insEdge (entry,entry,()) $ idomToTree cdom

        entry = entryOf p $ procedureOf p $ mainThread p

        trnsclos = trc $ tcfg p

        chop :: Node -> Node -> Set Node
        chop s t =   (Set.fromList $ suc trnsclos s)
                   ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance

chopsCdomArePrefixesGenerated :: (Program Gr -> Map (Node,Node) Node) -> GeneratedProgram -> Bool
chopsCdomArePrefixesGenerated cdomComputation gen = chopsCdomArePrefixes cdomComputation p
  where p :: Program Gr
        p = toProgram gen

        

chopsCdomAreExclChops :: (Program Gr -> Map (Node,Node) Node) -> Program Gr -> Bool
chopsCdomAreExclChops cdomComputation p =
    (∀) (Map.assocs cdom) (\((n,n'),c) -> let [ndom]  = pre idom n
                                              [ndom'] = pre idom n'
                                          in  (length (pre idom n) == 1) ∧ (length (pre idom n') == 1)
                                            ∧ (c == n  ∨ chop c n  ==   (exclChp c ndom ) ∪ (exclChp ndom  n )
                                                                      ∪ (exclChp c c) ∪ (exclChp ndom  ndom ) ∪ (exclChp n  n )
                                              )
                                            ∧ (c == n' ∨ chop c n' ==   (exclChp c ndom') ∪ (exclChp ndom' n')
                                                                      ∪ (exclChp c c) ∪ (exclChp ndom' ndom') ∪ (exclChp n' n')
                                              )
                          )
  where cdom = cdomComputation p

        idom = insEdge (entry,entry,()) $ idomToTree cdom

        entry = entryOf p $ procedureOf p $ mainThread p

        trnsclos = trc $ tcfg p

        exclChp s t = (exclChop $ tcfg p) s t

        chop :: Node -> Node -> Set Node
        chop s t =   (Set.fromList $ suc trnsclos s)
                   ∩ (Set.fromList $ pre trnsclos t)  -- TODO: Performance


--chopsCdomAreExclChopsGenerated :: (Program Gr -> Map (Node,Node) Node) -> GeneratedProgram -> Bool
chopsCdomAreExclChopsGenerated cdomComputation gen = chopsCdomAreExclChops cdomComputation p
  where p :: Program Gr
        p = toProgram gen



simulChopIsChop ::  Gr () () -> Bool
simulChopIsChop gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             (chop $ gr ) s t == (simul ! (s,t))
      )
    )
  where simul = simulChop gr

simulChopIsInclChop ::  Gr () () -> Bool
simulChopIsInclChop gr =
    (∀) (nodes $ gr) (\s ->
      (∀) (nodes $ gr) (\t ->
             inclChop gr s t  == (simul ! (s,t))
      )
    )
  where simul = simulChop gr

inclChopIsChop :: Program Gr -> Bool
inclChopIsChop p =
    let pchop = chop (tcfg p) in
    (∀) (nodes $ tcfg p) (\s ->
      (∀) (nodes $ tcfg p) (\t ->
             pchop s t == (inclChop $ tcfg p) s t
      )
    )


exclChopContainedinclChop :: Program Gr -> Bool
exclChopContainedinclChop p =
    (∀) (nodes $ tcfg p) (\s ->
      (∀) (nodes $ tcfg p) (\t ->
             (exclChop $ tcfg p) s t ⊆ (inclChop $ tcfg p) s t
      )
    )

selfChopsSame :: Program Gr -> Bool
selfChopsSame p =
    (∀) (nodes $ tcfg p) (\s ->
             (exclChop $ tcfg p) s s ==  (inclChop $ tcfg p) s s -- == (chop $ tcfg p) s s via inclChopIsChop
    )
  where normalChop s = (chop $ tcfg p) s s

selfChopsSCC :: Program Gr -> Bool
selfChopsSCC p =
    (∀) (nodes $ tcfg p) (\s ->
             (exclChop $ tcfg p) s s ==  (Set.fromList $ sccOf s)                 -- == (chop $ tcfg p) s s via inclChopIsChop
    )
  where sccs    = scc $ tcfg p
        sccOf s =  the (s ∊) $ sccs
