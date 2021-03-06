{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Program.TransitionSystem where


-- import Algebra.Lattice

import Unicode

import Program
import Util
-- import Program.CDom
-- import Program.MHP
import IRLSOD

import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.TransClos
-- import Data.Util

import Data.Maybe (fromJust)
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.List ((\\))

import Program.Analysis
import Program.For
import Program.Generator (toProgram, toProgramSimple, SimpleProgram(..), GeneratedProgram(..), Generated(..))

-- import Data.Bool.Unicode
-- import Data.Eq.Unicode

-- -- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.PatriciaTree (Gr)
-- -- import Data.Graph.Inductive.Util
-- -- import Data.Graph.Inductive.Query.Dataflow
-- import Data.Graph.Inductive.Query.Dominators
-- import Data.Graph.Inductive.Query.TransClos

-- import Data.Graph.Inductive.Query.ProgramDependence
-- import Data.Graph.Inductive.Query.DataConflict
-- import Data.Graph.Inductive.Query.TimingDependence

-- import IRLSOD
-- -- import Unicode


data Dependent               = InitialVar Name
--                             | Edge (LEdge Bool) (Set Dependent) -- For total generality, one might have to use "Edge (LEdge CFGEdge) (Set Dependent)" Instead

                               deriving (Eq,Ord,Show)
type SymbolicDefUseNode      = (Map Name (Set Dependent), Node, Set Dependent)
type SymbolicDefUseSystem gr = gr SymbolicDefUseNode ()


fromSimpleProgram :: DynGraph gr => Program gr -> SymbolicDefUseSystem gr
fromSimpleProgram p@(Program { tcfg, staticThreads, mainThread, procedureOf, entryOf, exitOf })
    | Set.size staticThreads /= 1 = error "not simple: more than one thread"
    | otherwise                   = unrollFrom tcfg (mkGraph [(entry, initial)] [])
  where entry   = entryOf $ procedureOf $ mainThread
        exit    = exitOf  $ procedureOf $ mainThread
        cfg     = tcfg
        initial = (Map.fromList [ (v, Set.fromList [InitialVar v] ) | v <- Set.toList $ names p ], entry, Set.empty)


unrollFrom :: DynGraph gr => gr CFGNode CFGEdge -> SymbolicDefUseSystem gr -> SymbolicDefUseSystem gr
unrollFrom cfg system
    | noNodes newSystem == noNodes system &&
      noEdges newSystem == noEdges system     = system
    | otherwise                               = unrollFrom cfg newSystem
  where noEdges g = length $ edges g
        newSystem = mkGraph allNodes [ (fromJust $ lookup nl  allNodes',
                                            fromJust $ lookup nl' allNodes',
                                            ()
                                           ) | (nl,nl',()) <- allEdges
                                     ]
        allEdges = [ (nl,nl',()) | (i,nl@(varDeps, nCfg, controlDeps)) <- labNodes system,
                                   (nCfg',eCfg) <- lsuc cfg nCfg,
                                   let nl' = case eCfg of
                                               Guard  b _ -> (varDeps,
                                                              nCfg',
                                                              controlDeps ∪
                                                              (Set.fromList [ d | v <- Set.toList $ useE eCfg,
                                                                                  d <- Set.toList $ varDeps ! v ]
                                                              )
                                                             )
                                               Assign _ _ -> ((Map.fromList [ (d, (Set.map InitialVar $ useE eCfg)
                                                                                  ∪
                                                                                  controlDeps
                                                                              )
                                                                            | d <- Set.toList $ defE eCfg ]
                                                              ) `Map.union` varDeps,
                                                              nCfg',
                                                              controlDeps)
                                               NoOp       -> (varDeps, nCfg', controlDeps)
                                               _          -> error "not simple"

                   ]
        allNodes = zip [1..]
                       (Set.toList $ (Set.fromList [ nl  | (nl,_  ,_) <- allEdges ])
                                   ∪ (Set.fromList [ nl' | (_ ,nl',_) <- allEdges ]))
        allNodes' = fmap (\(a,b) -> (b,a)) allNodes


varsIn :: Dependent -> Set Name
varsIn (InitialVar v)                       = Set.fromList [v]
--varsIn (Edge _ deps)  = Set.unions $ Set.toList $ Set.map varsIn deps

secureSymbolicDefUseSystem :: Graph gr => Node -> Set Name -> Set Name -> SymbolicDefUseSystem gr -> Bool
secureSymbolicDefUseSystem exit low high system = (∀) exitstates (\(varDeps, _,_) ->
                                (∀) low (\l -> (Set.unions $ Set.toList $ Set.map varsIn (varDeps ! l)) ∩ high  == Set.empty)
                              )
  where exitstates = [ nl | (i,nl@(_,nCfg,_)) <- labNodes system,
                            nCfg == exit
                     ]


secureSymbolic :: DynGraph gr => Set Name -> Set Name -> Program gr -> Bool
secureSymbolic low high p@(Program { mainThread, exitOf, procedureOf }) = secureSymbolicDefUseSystem exit low high system
  where system  = fromSimpleProgram p
        exit    = exitOf  $ procedureOf $ mainThread


type TwoValue = Bool

data Reason = VarValue Name TwoValue
            | CfgEdge Edge  -- For total generality, one might have to use "Edge (LEdge CFGEdge) (Set Dependent)" Instead
            deriving (Show, Eq, Ord)

type TwoValueDefUseNode   = (Map Name (Set Reason), Node)
type TwoValueDefUseSystem gr = gr TwoValueDefUseNode ()


initialTwoValueStates :: Set Name -> [Map Name (Set Reason)]
initialTwoValueStates vars = [ fmap (Set.singleton) $ Map.fromList σ | σ <- 
  chooseOneEach [ (var, [VarValue var val  | val <- [False, True]])
                                           | var <- Set.toList $ vars
                ]
 ]


twoValueFromSimpleProgram :: DynGraph gr => Program gr -> TwoValueDefUseSystem gr
twoValueFromSimpleProgram p@(Program { tcfg, staticThreads, mainThread, entryOf, procedureOf, exitOf })
    | Set.size staticThreads /= 1 = error "not simple: more than one thread"
    | otherwise                   =
        twoValueUnrollFrom tcfg (mkGraph [ (i,(σ,entry))
                                         | (i,σ) <- zip [1..]
                                                        (initialTwoValueStates $ names p)
                                         ]
                                         []
                                )
  where entry   = entryOf $ procedureOf $ mainThread


twoValueUnrollFrom :: DynGraph gr => gr CFGNode CFGEdge -> TwoValueDefUseSystem gr -> TwoValueDefUseSystem gr
twoValueUnrollFrom cfg system
    | noNodes newSystem == noNodes system &&
      noEdges newSystem == noEdges system     = system
    | otherwise                               = twoValueUnrollFrom cfg newSystem
  where noEdges g = length $ edges g
        newSystem = mkGraph allNodes [ (fromJust $ lookup nl  allNodes',
                                            fromJust $ lookup nl' allNodes',
                                            ()
                                           ) | (nl,nl',()) <- allEdges
                                     ]
        allEdges = [ (nl,nl',()) | (i,nl@(σ, nCfg)) <- labNodes system,
                                   (nCfg',eCfg) <- lsuc cfg nCfg,
                                   let nl' = case eCfg of
                                               Guard  b _ -> (σ, nCfg')
                                               Assign _ _ -> ((Map.fromList [ (vDef, Set.fromList [CfgEdge (nCfg,nCfg')] ∪  Set.unions[ σ ! vUse | vUse <- Set.toList $ useE eCfg]
                                                                              )
                                                                            | vDef <- Set.toList $ defE eCfg ]
                                                              ) `Map.union` σ,
                                                              nCfg'
                                                             )
                                               NoOp       -> (σ, nCfg')
                                               _          -> error "not simple"

                   ]
        allNodes = zip [1..]
                       (Set.toList $ (Set.fromList [ nl  | (nl,_  ,_) <- allEdges ])
                                   ∪ (Set.fromList [ nl' | (_ ,nl',_) <- allEdges ]))
        allNodes' = fmap (\(a,b) -> (b,a)) allNodes



at cfgNode (σ, cfgNode') = cfgNode == cfgNode'

secureTwoValueDefUseSystem :: DynGraph gr => Set Name -> Node -> Node -> Set Name -> TwoValueDefUseSystem gr -> Bool
secureTwoValueDefUseSystem vars entry exit low system = (∀) entrystates (\(i,n) -> (length $ suc observable i) == 1)
  where entrystates = [ (i,n) | (i,n) <- labNodes observable,
                            at entry n
                      ]
        observable  = observablePartOfTwoValueDefUseSimple vars entry exit low system



secureTwoValueDefUse :: DynGraph gr => Set Name -> Program gr -> Bool
secureTwoValueDefUse low p@(Program { mainThread, exitOf, entryOf, procedureOf}) = secureTwoValueDefUseSystem variables entry exit low system
  where system    = twoValueFromSimpleProgram p
        entry     = entryOf $ procedureOf $ mainThread
        exit      = exitOf  $ procedureOf $ mainThread
        variables = names p


observablePartOfTwoValueDefUseSimple  vars entry exit low system = nmap lowOnly $ eqGraph (obsInitial ++ obsFinal) closure
  where closure = trc system

        initial  = [ (i,n) | (i,n@(σ,_)) <- labNodes system,
                             σ ∊ (initialTwoValueStates vars)
                   ]
        final    = [ (i,n) | (i,n) <- labNodes system,
                             at exit n
                   ]
        obsInitial = [  [ i | (i,(σ,_)) <- initial, (restrict σ low) == σLow]
                     | σLow <- (initialTwoValueStates $ low) ]
        obsFinal = Map.elems $ collectEqClasses final
        collectEqClasses lnodes = foldr (\(i,(σ,nCfg)) eqClasses -> Map.insertWith (\i is -> i ++ is) (restrict σ low) [i] eqClasses) Map.empty lnodes
        lowOnly (i:_) = (restrict σ low, nCfg)
          where (σ,nCfg) = fromJust $ lab system i
        lowOnly []    = (Map.empty, -1)






type OneValue = ()
data OneReason = OneVarValue Name OneValue
            | OneCfgEdge Edge  -- For total generality, one might have to use "Edge (LEdge CFGEdge) (Set Dependent)" Instead
            deriving (Show, Eq, Ord)

type OneValueDefUseNode   = (Map Name (Set OneReason), Node)
type OneValueDefUseSystem gr = gr OneValueDefUseNode ()


initialOneValueStates :: Set Name -> [Map Name (Set OneReason)]
initialOneValueStates vars = [ fmap (Set.singleton) $ Map.fromList σ | σ <- 
  chooseOneEach [ (var, [OneVarValue var val  | val <- [()]])
                                           | var <- Set.toList $ vars
                ]
 ]


oneValueFromSimpleProgram :: DynGraph gr => Program gr -> OneValueDefUseSystem gr
oneValueFromSimpleProgram p@(Program { tcfg, staticThreads, mainThread, entryOf, procedureOf, exitOf })
    | Set.size staticThreads /= 1 = error "not simple: more than one thread"
    | otherwise                   =
        oneValueUnrollFrom tcfg (mkGraph [ (i,(σ,entry))
                                         | (i,σ) <- zip [1..]
                                                        (initialOneValueStates $ names p)
                                         ]
                                         []
                                )
  where entry   = entryOf $ procedureOf $ mainThread


oneValueUnrollFrom :: DynGraph gr => gr CFGNode CFGEdge -> OneValueDefUseSystem gr -> OneValueDefUseSystem gr
oneValueUnrollFrom cfg system
    | noNodes newSystem == noNodes system &&
      noEdges newSystem == noEdges system     = system
    | otherwise                               = oneValueUnrollFrom cfg newSystem
  where noEdges g = length $ edges g
        newSystem = mkGraph allNodes [ (fromJust $ lookup nl  allNodes',
                                            fromJust $ lookup nl' allNodes',
                                            ()
                                           ) | (nl,nl',()) <- allEdges
                                     ]
        allEdges = [ (nl,nl',()) | (i,nl@(σ, nCfg)) <- labNodes system,
                                   (nCfg',eCfg) <- lsuc cfg nCfg,
                                   let nl' = case eCfg of
                                               Guard  b _ -> (σ, nCfg')
                                               Assign _ _ -> ((Map.fromList [ (vDef, Set.fromList [OneCfgEdge (nCfg,nCfg')] ∪  Set.unions[ σ ! vUse | vUse <- Set.toList $ useE eCfg]
                                                                              )
                                                                            | vDef <- Set.toList $ defE eCfg ]
                                                              ) `Map.union` σ,
                                                              nCfg'
                                                             )
                                               NoOp       -> (σ, nCfg')
                                               _          -> error "not simple"

                   ]
        allNodes = zip [1..]
                       (Set.toList $ (Set.fromList [ nl  | (nl,_  ,_) <- allEdges ])
                                   ∪ (Set.fromList [ nl' | (_ ,nl',_) <- allEdges ]))
        allNodes' = fmap (\(a,b) -> (b,a)) allNodes


secureOneValueDefUseSystem :: DynGraph gr => Set Name -> Node -> Node -> Set Name -> OneValueDefUseSystem gr -> Bool
secureOneValueDefUseSystem vars entry exit low system = (∀) exitstates (\(i,(σ,nCfg)) ->
                                                                         (∀) low (\var ->
                                                                                 (∀) [ var' | OneVarValue var' () <- Set.toList $ σ ! var] (\var' -> var' ∈ low)
                                                                         )
                                                        )
                                                        ∧
                                                        (∀) entrystates (\(i,n) -> (length $ suc observable i) == 1)
  where entrystates = [ (i,n) | (i,n) <- labNodes observable,
                            at entry n
                      ]
        exitstates  = [ (i,n) | (i,n) <- labNodes observable,
                            at exit n
                      ]
        observable  = observablePartOfOneValueDefUseSimple vars entry exit low system



secureOneValueDefUse :: DynGraph gr => Set Name -> Program gr -> Bool
secureOneValueDefUse low p@(Program { mainThread, exitOf, entryOf, procedureOf }) = secureOneValueDefUseSystem variables entry exit low system
  where system    = oneValueFromSimpleProgram p
        entry     = entryOf $ procedureOf $ mainThread
        exit      = exitOf  $ procedureOf $ mainThread
        variables = names p


observablePartOfOneValueDefUseSimple  vars entry exit low system = nmap lowOnly $ eqGraph (obsInitial ++ obsFinal) closure
  where closure = trc system

        initial  = [ (i,n) | (i,n@(σ,_)) <- labNodes system,
                             σ ∊ (initialOneValueStates vars)
                   ]
        final    = [ (i,n) | (i,n) <- labNodes system,
                             at exit n
                   ]
        obsInitial = [  [ i | (i,(σ,_)) <- initial, (restrict σ low) == σLow]
                     | σLow <- (initialOneValueStates $ low) ]
        obsFinal = Map.elems $ collectEqClasses final
        collectEqClasses lnodes = foldr (\(i,(σ,nCfg)) eqClasses -> Map.insertWith (\i is -> i ++ is) (restrict σ low) [i] eqClasses) Map.empty lnodes
        lowOnly (i:_) = (restrict σ low, nCfg)
          where (σ,nCfg) = fromJust $ lab system i
        lowOnly []    = (Map.empty, -1)







securePDG :: Set Var -> Set Var -> Set Var -> SimpleProgram -> Bool
securePDG vars low high simple =  isSecureTimingClassificationDomPaths p'
  where p'       = toProgram       simple' :: Program Gr
        simple' = let (SimpleProgram procedureOf code) = simple
                      (Generated for _ _ _)    = (Map.!) code ((Map.!) procedureOf 1)
                      prefix  = foldl Seq Skip $ [ReadFromChannel var       lowIn1 | var <- Set.toList $ (vars ∖ high) ] ++
                                                 [ReadFromChannel var       stdIn  | var <- Set.toList $ high]
                      postfix = foldr Seq Skip   [PrintToChannel  (Var var) stdOut | var <- Set.toList $ low ]
                      for'    = prefix `Seq` for `Seq` postfix
                  in  (GeneratedProgram (Map.fromList [(1, "1")]) (Map.fromList [("1", Generated for' undefined undefined undefined)]))










type Concrete = GlobalState
concreteDomain = [0,1]

concreteArrDomain = [arrayEmpty, fmap (+1) arrayEmpty]


type ConcreteNode   = (Concrete, Node)
type ConcreteSystem gr = gr ConcreteNode ()


initialConcreteStates :: Set Name -> [GlobalState]
initialConcreteStates vars = [ GlobalState (Map.fromList σv) (Map.fromList σa) | 
  σv <- chooseOneEach [ (var, [val  | val <- concreteDomain])    | (VarName   var) <- Set.toList $ vars],
  σa <- chooseOneEach [ (var, [val  | val <- concreteArrDomain]) | (ArrayName var) <- Set.toList $ vars]
   
 ]


concreteFromSimpleProgram :: DynGraph gr => Program gr -> ConcreteSystem gr
concreteFromSimpleProgram p@(Program { tcfg, staticThreads, mainThread, entryOf, procedureOf, exitOf })
    | Set.size staticThreads /= 1 = error "not simple: more than one thread"
    | otherwise                   =
        concreteUnrollFrom tcfg (mkGraph [ (i,(σ,entry))
                                         | (i,σ) <- zip [1..]
                                                        (initialConcreteStates $ names p)
                                         ]
                                         []
                                )
  where entry   = entryOf $ procedureOf $ mainThread


concreteUnrollFrom :: DynGraph gr => gr CFGNode CFGEdge -> ConcreteSystem gr -> ConcreteSystem gr
concreteUnrollFrom cfg system
    | noNodes newSystem == noNodes system &&
      noEdges newSystem == noEdges system     = system
    | otherwise                               = concreteUnrollFrom cfg newSystem
  where noEdges g = length $ edges g
        newSystem = mkGraph allNodes [ (fromJust $ lookup nl  allNodes',
                                            fromJust $ lookup nl' allNodes',
                                            ()
                                           ) | (nl,nl',()) <- allEdges
                                     ]
        allEdges = [ (nl,nl',()) | (i,nl@(σ, nCfg)) <- labNodes system,
                                   (nCfg',eCfg) <- lsuc cfg nCfg,
                                   case eCfg of Guard True  b ->       evalB σ Map.empty b
                                                Guard False b -> not $ evalB σ Map.empty b
                                                _             -> True,
                                   let nl' = case eCfg of
                                               Guard  _ _ -> (σ, nCfg')
                                               Assign v f -> let [(GlobalState σv' σa', _, _)] = stepFor eCfg (σ, Map.empty, undefined) in (GlobalState (fmap bit σv') (fmap (fmap bit) σa'), nCfg')
                                               NoOp       -> (σ, nCfg')
                                               _          -> error "not simple"

                   ]
        allNodes = zip [1..]
                       (Set.toList $ (Set.fromList [ nl  | (nl,_  ,_) <- allEdges ])
                                   ∪ (Set.fromList [ nl' | (_ ,nl',_) <- allEdges ]))
        allNodes' = fmap (\(a,b) -> (b,a)) allNodes

        bit x = abs $ x `mod` 2




-- secureTwoValueDefUseSystem :: DynGraph gr => Set Var -> Node -> Node -> Set Var -> TwoValueDefUseSystem gr -> Bool
-- secureTwoValueDefUseSystem vars entry exit low system = (∀) entrystates (\(i,n) -> (length $ suc observable i) == 1)
--   where entrystates = [ (i,n) | (i,n) <- labNodes observable,
--                             at entry n
--                       ]
--         observable  = observablePartOfTwoValueDefUseSimple vars entry exit low system



-- secureTwoValueDefUse :: DynGraph gr => Set Var -> Program gr -> Bool
-- secureTwoValueDefUse low p@(Program { mainThread, exitOf, entryOf }) = secureTwoValueDefUseSystem variables entry exit low system
--   where system    = twoValueFromSimpleProgram p
--         entry     = entryOf mainThread
--         exit      = exitOf  mainThread
--         variables = vars p



observablePartOfConcrete vars entry exit low system = nmap lowOnly $ eqGraph (obsInitial ++ obsFinal ++ (fmap (\(i,n) -> [i]) other)) closure
  where closure = system

        initial  = [ (i,n) | (i,n@(σ,_)) <- labNodes system,
                             σ ∊ (initialConcreteStates vars),
                             at entry n
                   ]
        final    = [ (i,n) | (i,n) <- labNodes system,
                             at exit n
                   ]
        other = (labNodes system \\ initial) \\ final
        obsInitial = [  [ i | (i,(σ,_)) <- initial, (restr σ low) == σLow]
                     | σLow <- (initialConcreteStates $ low) ]
        obsFinal = Map.elems $ collectEqClasses final

        collectEqClasses lnodes = foldr (\(i,(σ,nCfg)) eqClasses -> Map.insertWith (\i is -> i ++ is) (restr σ low) [i] eqClasses) Map.empty lnodes
        lowOnly (i:_)
          | i ∊ (fmap fst initial) ∨
            i ∊ (fmap fst final  ) = (restr σ low, nCfg)
          | otherwise           = (σ,nCfg)
          where (σ,nCfg) = fromJust $ lab system i
        lowOnly []    = (globalEmpty, -1)


        restr (GlobalState {σv, σa}) low =
          GlobalState { σv = (Map.filterWithKey (\var _ -> VarName   var ∈ low) σv ),
                        σa = (Map.filterWithKey (\arr _ -> ArrayName arr ∈ low) σa )
          }
