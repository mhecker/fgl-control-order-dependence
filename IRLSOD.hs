module IRLSOD where


import Unicode
import Algebra.Lattice

import Data.Graph.Inductive.Graph


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode
import Data.List (partition,delete)

type Var = String
type Val = Integer
type InputChannel = String
type OutputChannel = String

unused :: Var
unused = "unused"

stdIn :: InputChannel
stdIn = "stdIn"

stdOut :: OutputChannel
stdOut = "stdOut"

type GlobalState = Map Var Val


data BoolFunction = CTrue   | CFalse | Leq Var Var | And BoolFunction BoolFunction | Not BoolFunction | Or BoolFunction BoolFunction deriving (Show, Eq, Ord)
data VarFunction   = Val Val | Var Var | Plus VarFunction VarFunction | Times VarFunction VarFunction | Neg VarFunction deriving (Show, Eq, Ord)

evalB :: GlobalState -> BoolFunction -> Bool
evalB _ CTrue     = True
evalB _ CFalse    = False
evalB σ (Leq x y) = evalV σ (Var x)  <= evalV σ (Var y)
evalB σ (And b1 b2) = evalB σ b1 && evalB σ b2
evalB σ (Or  b1 b2) = evalB σ b1 || evalB σ b2
evalB σ (Not b)     = not $ evalB σ b


useB CTrue       = Set.empty
useB CFalse      = Set.empty
useB (Leq x y)   = Set.fromList [x,y]
useB (And b1 b2) = useB b1 ∪ useB b2
useB (Or  b1 b2) = useB b1 ∪ useB b2
useB (Not b)     = useB b

evalV :: GlobalState -> VarFunction -> Val
evalV σ (Val  x)    = x
evalV σ (Var  x)    = σ ! x
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
             | Read   Var  InputChannel
             | Print  Var  OutputChannel
             | Spawn
             deriving (Show, Eq, Ord)


useE :: CFGEdge -> Set Var
useE (Guard   _ bf) = useB bf
useE (Assign  _ vf) = useV vf
useE (Read    _ _)  = Set.empty
useE Spawn          = Set.empty
useE (Print x _)    = Set.singleton x


defE :: CFGEdge -> Set Var
defE (Guard   _ _) = Set.empty
defE (Assign  x _) = Set.singleton x
defE (Read    x _) = Set.singleton x
defE Spawn         = Set.empty
defE (Print   _ _) = Set.empty

use :: Graph gr => gr CFGNode CFGEdge -> CFGNode -> Set Var
use gr n = Set.unions [ useE e | (n',e) <- lsuc gr n ]

def :: Graph gr => gr CFGNode CFGEdge -> CFGNode -> Set Var
def gr n = Set.unions [ defE e | (n',e) <- lsuc gr n ]

type CFGNode = Int

true :: CFGEdge
true  = Guard True  $ CTrue

false :: CFGEdge
false = Guard False $ CTrue

nop :: CFGEdge
nop = Assign unused $ Val 42

nopuse :: CFGEdge
nopuse = Assign unused $ Var unused

nopread :: CFGEdge
nopread = Read unused $ stdIn

nopPrint :: CFGEdge
nopPrint = Print unused $ stdOut

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
type Configuration = (ControlState,GlobalState,Input)
data Event = PrintEvent Val OutputChannel
           | ReadEvent  Val InputChannel
           | Tau
           deriving (Eq, Ord, Show)

fromEdge :: GlobalState -> Input -> CFGEdge -> Event
fromEdge σ i (Guard b bf)
  | b == evalB σ bf = Tau
  | otherwise       = undefined
fromEdge σ i (Assign x vf) = Tau
fromEdge σ i (Read   x ch) = ReadEvent  (head $ i ! ch)   ch
fromEdge σ i (Print  x ch) = PrintEvent (evalV σ (Var x)) ch
fromEdge σ i (Spawn      ) = Tau


data SecurityLattice = Undefined | Low | High deriving (Show, Ord, Eq, Bounded, Enum)

instance JoinSemiLattice SecurityLattice where
  Undefined `join` x = x
  Low       `join` Undefined = Low
  Low       `join` x         = x
  High      `join` x         = High

instance MeetSemiLattice SecurityLattice where
  Undefined `meet` x = Undefined
  Low `meet` Undefined = Undefined
  Low `meet` x = Low
  High `meet` x = x

instance BoundedJoinSemiLattice SecurityLattice where
  bottom = Low


-- type ChannelClassification = (InputChannel -> SecurityLattice, OutputChannel -> SecurityLattice)
type ProgramClassification = Node -> SecurityLattice

type ExecutionTrace = [(Configuration, (Node,Event), Configuration)]
type Trace          = [(GlobalState,   (Node,Event), GlobalState)]

eventStep :: Graph gr => gr CFGNode CFGEdge -> Configuration -> [((Node,Event),Configuration)]
eventStep icfg config@(control,σ,i) = do
       n <- control
       let (spawn,normal) = partition (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False }) $ lsuc icfg n

       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       let configs' = concat $ fmap (\(n',cfgEdge) -> fmap (\(σ',i') -> ((n,fromEdge σ i cfgEdge),(n',σ',i'))) (stepFor cfgEdge (σ,i)) ) normal


       case (spawn, configs') of (_ ,[((_,event),(n',σ', i'))]) -> return ((n,event),(n' : ([spawned | (spawned, Spawn) <- spawn] ++ (delete n control)), σ',i'))
                                 ([],[])                        -> return ((n,Tau),  (                                                delete n control  , σ, i ))
                                 (_ ,[])                        -> error "spawn an exit-node"
                                 (_ ,_)                         -> error "nichtdeterministisches Programm"



step :: Graph gr => gr CFGNode CFGEdge -> Configuration -> [Configuration]
step icfg config@(control,σ,i) = do
       n <- control
       let (spawn,normal) = partition (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False }) $ lsuc icfg n

       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       let configs' = concat $ fmap (\(n',cfgEdge) -> fmap (\(σ',i') -> (n',σ',i')) (stepFor cfgEdge (σ,i)) ) normal

       case (spawn, configs') of (_,[(n',σ', i')]) -> return (n' : ([spawned | (spawned, Spawn) <- spawn] ++ (delete n control)), σ',i')
                                 ([],[])           -> return (                                               (delete n control),  σ, i )
                                 (_,[])            -> error "spawn an exit-node"
                                 (_,_)             -> error "nichtdeterministisches Programm"


stepFor :: CFGEdge -> (GlobalState,Input) -> [(GlobalState,Input)]
stepFor (Guard b bf) (σ,i)
  | b == evalB σ bf = [(σ,i)]
  | otherwise       = []
stepFor (Assign x vf) (σ,i)  = [(Map.insert x (evalV σ vf)    σ, i)]
stepFor (Read   x ch) (σ,i)  = [(Map.insert x (head $ i ! ch) σ, Map.adjust tail ch i)]
stepFor (Print  x ch) (σ,i)  = [(σ,i)]
stepFor (Spawn      ) (σ,i)  = undefined

hide (a,b,c) = (a,b)

toTrace :: ExecutionTrace -> Trace
toTrace eTrace = [ (σ, o, σ') | ((_,σ,_), o, (_,σ',_)) <- eTrace ]




observable :: Graph gr => gr CFGNode CFGEdge -> ProgramClassification -> SecurityLattice -> Trace -> Trace
observable icfg cl l trace = [ (restrict σ (use icfg n), (n,e), restrict σ' (def icfg n)) | (σ, (n,e), σ') <- trace, cl n <= l ]
  where restrict σ vars = Map.filterWithKey (\var _ -> var ∈ vars) σ

(≈) :: Graph gr => gr CFGNode CFGEdge -> ProgramClassification -> SecurityLattice -> Trace -> Trace -> Bool
(≈) icfg cl l t t' = (observable icfg cl l t) == (observable icfg cl l t')



