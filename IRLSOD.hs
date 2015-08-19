module IRLSOD where


import Unicode

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode

type Var = String
type Val = Integer

unused :: Var
unused = "unused"

type GlobalState = Var -> Val

--
data BoolFunction = CTrue   | CFalse | Leq Var Var | And BoolFunction BoolFunction | Not BoolFunction | Or BoolFunction BoolFunction deriving (Show, Eq, Ord)
data VarFunction   = Val Val | Var Var | Plus VarFunction VarFunction | Times VarFunction VarFunction | Neg VarFunction deriving (Show, Eq, Ord)

-- data StateFunction t = StateFunction {
--     useF  :: Set Var,
--     eval  :: GlobalState -> t
--   }

-- data CFGEdge = Guard  Bool (StateFunction Bool)
--              | Assign Var  (StateFunction Val)   | Spawn

-- useE :: CFGEdge -> Set Var
-- useE (Guard   _ sf) = useF sf
-- useE (Assign  _ sf) = useF sf
-- useE Spawn          = Set.empty

-- defE :: CFGEdge -> Set Var
-- defE (Guard   _ _) = Set.empty
-- defE (Assign  x _) = Set.singleton x
-- defE Spawn         = Set.empty

-- use :: Graph gr => gr CFGNode CFGEdge -> CFGNode -> Set Var
-- use gr n = unions [ useE e | (n',e) <- lsuc gr n ]

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
evalV σ (Var  x)    = σ x
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
             | Assign Var  VarFunction  | Spawn deriving (Show, Eq, Ord)

useE :: CFGEdge -> Set Var
useE (Guard   _ bf) = useB bf
useE (Assign  _ vf) = useV vf
useE Spawn          = Set.empty

defE :: CFGEdge -> Set Var
defE (Guard   _ _) = Set.empty
defE (Assign  x _) = Set.singleton x
defE Spawn         = Set.empty

use :: Graph gr => gr CFGNode CFGEdge -> CFGNode -> Set Var
use gr n = Set.unions [ useE e | (n',e) <- lsuc gr n ]

-- instance Show CFGEdge where
--   show (Guard True  _) = "Guard True"
--   show (Guard False _) = "Guard False"
--   show (Assign _ _)    = "Op"
--   show (Spawn)         = "Spawn"

type CFGNode = Int


true :: CFGEdge
true  = Guard True  $ CTrue

false :: CFGEdge
false = Guard False $ CTrue

nop :: CFGEdge
nop = Assign unused $ Val 42

nopread :: CFGEdge
nopread = Assign unused $ Var unused


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

