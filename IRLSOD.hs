module IRLSOD where


import Unicode

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph


import Control.Monad(forM)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode
import Data.List (partition)


type Var = String
type Val = Integer
type InputChannel = String

unused :: Var
unused = "unused"

defaultChannel :: InputChannel
defaultChannel = "default"

type GlobalState = Map Var Val

--
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
             | Spawn
             deriving (Show, Eq, Ord)


useE :: CFGEdge -> Set Var
useE (Guard   _ bf) = useB bf
useE (Assign  _ vf) = useV vf
useE (Read    _ _)  = Set.empty
useE Spawn          = Set.empty

defE :: CFGEdge -> Set Var
defE (Guard   _ _) = Set.empty
defE (Assign  x _) = Set.singleton x
defE (Read    x _) = Set.singleton x
defE Spawn         = Set.empty

use :: Graph gr => gr CFGNode CFGEdge -> CFGNode -> Set Var
use gr n = Set.unions [ useE e | (n',e) <- lsuc gr n ]

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
nopread = Read unused $ defaultChannel


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

step :: Graph gr => gr CFGNode CFGEdge -> Configuration -> [Configuration]
step graph config@(control,σ,i) = do
       n <- control
       let (spawn,normal) = partition (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False }) $ lsuc graph n

       -- Unter den Normalen Nachfolgern gibt es genau einen der passierbar ist
       let configs' = concat $ fmap (\(n',cfgEdge) -> fmap (\(σ',i') -> (n',σ',i')) (stepFor cfgEdge (σ,i)) ) normal

       case configs' of [(n',σ', i')] -> return (n' : [spawned | (spawned, Spawn) <- spawn], σ',i') 
                        _             -> error "Nicht genau 1 normaler nachfolger"


stepFor :: CFGEdge -> (GlobalState,Input) -> [(GlobalState,Input)]
stepFor (Guard b bf) (σ,i)
  | b == evalB σ bf = [(σ,i)]
  | otherwise       = []
stepFor (Assign x vf) (σ,i)  = [(Map.insert x (evalV σ vf)    σ, i)]
stepFor (Read   x ch) (σ,i)  = [(Map.insert x (head $ i ! ch) σ, Map.adjust tail ch i)]
stepFor (Spawn      ) (σ,i)  = undefined

hide (a,b,c) = (a,b)
