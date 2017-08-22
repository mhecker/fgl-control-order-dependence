module IRLSOD where

import Util
import Unicode
import Algebra.Lattice

import Data.Graph.Inductive.Graph


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (partition,delete)

data Var = Global String | ThreadLocal String deriving (Show, Eq, Ord)
type Val = Integer
type InputChannel = String
type OutputChannel = String
type Channel = String

stdIn :: InputChannel
stdIn = "stdIn"

stdIn2 :: InputChannel
stdIn2 = "stdIn"

stdOut :: OutputChannel
stdOut = "stdOut"

lowIn1 = "lowIn1"
lowIn2 = "lowIn2"

highOut1 = "highOut1"
highOut2 = "highOut2"

type GlobalState = Map Var Val
type ThreadLocalState = Map Var Val
type CombinedState = Map Var Val

data BoolFunction = CTrue   | CFalse | Leq VarFunction VarFunction | And BoolFunction BoolFunction | Not BoolFunction | Or BoolFunction BoolFunction deriving (Show, Eq, Ord)
data VarFunction   = Val Val | Var Var | Plus VarFunction VarFunction | Times VarFunction VarFunction | Neg VarFunction deriving (Show, Eq, Ord)

evalB :: CombinedState -> BoolFunction -> Bool
evalB _ CTrue     = True
evalB _ CFalse    = False
evalB σ (Leq x y) = evalV σ x <= evalV σ y
evalB σ (And b1 b2) = evalB σ b1 && evalB σ b2
evalB σ (Or  b1 b2) = evalB σ b1 || evalB σ b2
evalB σ (Not b)     = not $ evalB σ b


useB CTrue       = Set.empty
useB CFalse      = Set.empty
useB (Leq x y)   = useV x ∪ useV y
useB (And b1 b2) = useB b1 ∪ useB b2
useB (Or  b1 b2) = useB b1 ∪ useB b2
useB (Not b)     = useB b

evalV :: CombinedState -> VarFunction -> Val
evalV σ (Val  x)    = x
evalV σ (Var  x)
 | Map.member x σ   = σ ! x
 | otherwise        = error $ show σ ++ "does not contain:    " ++ (show x)
evalV σ (Plus  x y) = evalV σ x + evalV σ y
evalV σ (Times x y) = evalV σ x * evalV σ y
evalV σ (Neg x)     = - evalV σ x

useV :: VarFunction -> Set Var
useV (Val  x)    = Set.empty
useV (Var  x)    = Set.fromList [x]
useV (Plus  x y) = useV x ∪ useV y
useV (Times x y) = useV x ∪ useV y
useV (Neg x)     = useV x


data CFGEdge = Guard  Bool BoolFunction
             | Assign Var  VarFunction
             | Read   Var          InputChannel
             | Print  VarFunction  OutputChannel
             | NoOp
             | Spawn
             deriving (Show, Eq, Ord)


useE :: CFGEdge -> Set Var
useE (Guard   _ bf) = useB bf
useE (Assign  _ vf) = useV vf
useE (Read    _ _)  = Set.empty
useE Spawn          = Set.empty
useE (Print vf _)   = useV vf
useE NoOp           = Set.empty

defE :: CFGEdge -> Set Var
defE (Guard   _ _) = Set.empty
defE (Assign  x _) = Set.singleton x
defE (Read    x _) = Set.singleton x
defE Spawn         = Set.empty
defE (Print   _ _) = Set.empty
defE NoOp          = Set.empty

use :: Graph gr => gr CFGNode CFGEdge -> CFGNode -> Set Var
use gr n = Set.unions [ useE e | (n',e) <- lsuc gr n ]

def :: Graph gr => gr CFGNode CFGEdge -> CFGNode -> Set Var
def gr n = Set.unions [ defE e | (n',e) <- lsuc gr n ]

-- vars :: Graph gr => gr CFGNode CFGEdge -> Set Var
-- vars gr  = Set.unions [ useE e ∪ defE e | (_,_,e) <- labEdges gr ]

type CFGNode = Int

true :: CFGEdge
true  = Guard True  $ CTrue

false :: CFGEdge
false = Guard False $ CTrue

nop :: CFGEdge
nop = NoOp

nopPrint :: CFGEdge
nopPrint = Print (Val 42) $ stdOut

spawn :: CFGEdge
spawn = Spawn



wellformed :: Graph gr => gr CFGNode CFGEdge -> Bool
wellformed gr =
     and [  length [ n'  | (n', Assign _ _) <- lsuc gr n ] <= 1           | n <- nodes gr]
  && and [  length [ n'  | (n', Guard  _ _) <- lsuc gr n ] `elem` [0,1,2] | n <- nodes gr]
  && and [ (length [ n'  | (n', Assign _ _) <- lsuc gr n ] == 1)
            →   (  length [ n'  | (n', Guard _ _)  <- lsuc gr n ] == 0
                 && length [ n'  | (n', Spawn)      <- lsuc gr n ] == 0 ) | n <- nodes gr]
  && and [ (length [ n'  | (n', Guard _ _) <- lsuc gr n ] == 1)
            →   (  length [ n'  | (n', Guard True _) <- lsuc gr n ] == 0
                 && length [ n'  | (n', Assign _ _) <- lsuc gr n ] == 0
                 && length [ n'  | (n', Spawn)      <- lsuc gr n ] == 1 ) | n <- nodes gr]
  && and [ (length [ n'  | (n', Guard _ _) <- lsuc gr n ] == 2)
            →   (  length [ n'  | (n', Guard True  _) <- lsuc gr n ] == 1
                 && length [ n'  | (n', Guard False _) <- lsuc gr n ] == 1
                 && length [ n'  | (n', Assign _ _) <- lsuc gr n ] == 0
                 && length [ n'  | (n', Spawn)      <- lsuc gr n ] == 0 ) | n <- nodes gr]


type Input = Map InputChannel [Val]
type ControlState = [Node]
type ThreadLocalStates = [ThreadLocalState]
type Configuration = (ControlState,GlobalState,ThreadLocalStates,Input)
data Event = PrintEvent Val OutputChannel
           | ReadEvent  Val InputChannel
           | Tau
           deriving (Eq, Ord, Show)

fromEdge :: CombinedState -> Input -> CFGEdge -> Event
fromEdge σ i (Guard b bf)
  | b == evalB σ bf = Tau
  | otherwise       = undefined
fromEdge σ i (Assign x  vf) = Tau
fromEdge σ i (Read   x  ch) = ReadEvent  (head $ i ! ch)   ch
fromEdge σ i (Print  vf ch) = PrintEvent (evalV σ vf) ch
fromEdge σ i (Spawn      ) = Tau
fromEdge σ i (NoOp       ) = Tau


data SecurityLattice = Low | High deriving (Show, Ord, Eq, Bounded, Enum)

instance JoinSemiLattice SecurityLattice where
  Low       `join` x         = x
  High      `join` x         = High

instance MeetSemiLattice SecurityLattice where
  Low `meet` x = Low
  High `meet` x = x

instance BoundedJoinSemiLattice SecurityLattice where
  bottom = Low


-- type ChannelClassification = (InputChannel -> SecurityLattice, OutputChannel -> SecurityLattice)
type ObservationalSpecification = Node -> Maybe SecurityLattice

type ExecutionTrace = [(Configuration, (Node,Event,Int), Configuration)]
type Trace          = [(CombinedState, (Node,Event), CombinedState)]

eventStep :: Graph gr => gr CFGNode CFGEdge -> Configuration -> [((Node,Event,Int),Configuration)]
eventStep icfg config@(control,globalσ,tlσs,i) = do
       (n,tlσ,index) <- zip3 control tlσs [0..]
       let σ = globalσ `Map.union` tlσ
       let (spawn,normal) = partition (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False }) $ lsuc icfg n

       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       let configs' = concat $ fmap (\(n',cfgEdge) -> fmap (\(globalσ',tlσ', i') -> ((n,fromEdge σ i cfgEdge),(n',globalσ',tlσ', i'))) (stepFor cfgEdge (globalσ,tlσ,i)) ) normal


       case (spawn, configs') of (_ ,[((_,event),(n',globalσ', tlσ', i'))]) ->
                                                                         return ((n,event,index),(n'   : ([spawned   | (spawned, Spawn) <- spawn] ++ (deleteAt index control)),
                                                                                                  globalσ',
                                                                                                  tlσ' : ([Map.empty | (spawned, Spawn) <- spawn] ++ (deleteAt index tlσs   )),
                                                                                                  i'
                                                                                ))
                                 ([],[])                              -> return ((n,Tau,index),  (                                                    deleteAt index control,
                                                                                                  globalσ,
                                                                                                                                                      deleteAt index tlσs,
                                                                                                  i
                                                                                ))
                                 (_ ,[])                              -> error "spawn an exit-node"
                                 (_ ,_)                               -> error "nichtdeterministisches Programm"



step :: Graph gr => gr CFGNode CFGEdge -> Configuration -> [Configuration]
step icfg config@(control,globalσ,tlσs,i) = do
       (n,tlσ,index) <- zip3 control tlσs [0..]
       let σ = globalσ `Map.union` tlσ
       let (spawn,normal) = partition (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False }) $ lsuc icfg n

       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       let configs' = concat $ fmap (\(n',cfgEdge) -> fmap (\(globalσ',tlσ', i') -> (n',globalσ', tlσ', i')) (stepFor cfgEdge (globalσ,tlσ,i)) ) normal
       
       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       case (spawn, configs') of (_,[(n',globalσ', tlσ', i')]) ->
                                                            return (n'   : ([spawned   | (spawned, Spawn) <- spawn] ++ (deleteAt index control)),
                                                                    globalσ',
                                                                    tlσ' : ([Map.empty | (spawned, Spawn) <- spawn] ++ (deleteAt index tlσs   )),
                                                                    i'
                                                            )
                                 ([],[])                 -> return (                                                    deleteAt index control,
                                                                    globalσ,
                                                                                                                        deleteAt index tlσs,
                                                                    i
                                                            )
                                 (_,[])                  -> error "spawn an exit-node"
                                 (_,_)                   -> error "nichtdeterministisches Programm"


stepFor :: CFGEdge -> (GlobalState,ThreadLocalState,Input) -> [(GlobalState,ThreadLocalState,Input)]
stepFor e (globalσ,tlσ,i)  = step e where
      σ = globalσ `Map.union` tlσ
      step :: CFGEdge ->  [(GlobalState,ThreadLocalState,Input)]
      step (Guard b bf)
        | b == evalB σ bf                = [(                             globalσ,                              tlσ,                    i)]
        | otherwise                      = []
      step (Assign x@(Global _)      vf) = [(Map.insert x (evalV σ vf)    globalσ,                              tlσ,                    i)]
      step (Assign x@(ThreadLocal _) vf) = [(                             globalσ, Map.insert x (evalV σ vf)    tlσ,                    i)]
      step (Read   x@(Global _)      ch) = [(Map.insert x (head $ i ! ch) globalσ,                              tlσ, Map.adjust tail ch i)]
      step (Read   x@(ThreadLocal _) ch) = [(                             globalσ, Map.insert x (head $ i ! ch) tlσ, Map.adjust tail ch i)]
      step (Print  x ch)                 = [(                             globalσ,                              tlσ,                    i)]
      step (Spawn      )                 = undefined
      step (NoOp       )                 = [(                             globalσ,                              tlσ,                    i)]

hide (a,b,c,d) = (a,b,c)

toTrace :: ExecutionTrace -> Trace
toTrace eTrace = [ (globalσ `Map.union` (tlσs !! index) , (n,e), globalσ' `Map.union` (tlσs' !! 0)) | ((_,globalσ,tlσs,_), (n,e,index), (_,globalσ',tlσs',_)) <- eTrace ]




observable :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> SecurityLattice -> Trace -> Trace
observable icfg obs l trace = [ (restrict σ (use icfg n), (n,e), restrict σ' (def icfg n)) | (σ, (n,e), σ') <- trace, Just l' <- [obs n], l' ⊑ l ]

(≈) :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> SecurityLattice -> Trace -> Trace -> Bool
(≈) icfg obs l t t' = (observable icfg obs l t) == (observable icfg obs l t')


-- lsod :: Graph gr => 

-- irlsod :: Graph gr => Program gr -> 
