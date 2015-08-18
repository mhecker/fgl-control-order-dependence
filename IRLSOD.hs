module IRLSOD where


type Var = String
type Val = Integer

type GlobalState = Var -> Val

data CFGEdge = Guard (GlobalState -> Bool) | Op (GlobalState -> GlobalState) | Spawn

instance Show CFGEdge where
  show (Guard _) = "Guard"
  show (Op _)    = "Op"
  show (Spawn)   = "Spawn"

type CFGNode = Int


true :: CFGEdge
true = Guard (\_ -> True)

false :: CFGEdge
false = Guard (\_ -> False)

nop :: CFGEdge
nop = Op id
