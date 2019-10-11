{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
module IRLSOD where

import Util
import Unicode
import Algebra.Lattice

import Data.Graph.Inductive.Graph

import Control.Exception.Base (assert)

import GHC.Generics (Generic)
import Control.DeepSeq

import Data.Bits (xor, (.&.), shiftL, shiftR)

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.List (partition,delete)
import qualified Data.List as List

data Var = Global String | ThreadLocal String | Register Int deriving (Show, Eq, Ord, Generic, NFData)

isGlobal (Global _) = True
isGlobal _          = False

arrayMaxIndex :: Int
arrayMaxIndex = 255

arrayEmpty = Map.fromList [(i,0) | i <- [0..arrayMaxIndex] ]

arrayIndex i =  (abs i) `mod` (arrayMaxIndex + 1)
isArrayIndex i = (0 <= i ∧ i <= arrayMaxIndex)


data Array = Array String deriving (Show, Eq, Ord, Generic, NFData)

class SimpleShow a where
  simpleShow :: a -> String

instance SimpleShow Integer
  where simpleShow x = show x

instance SimpleShow ()
  where simpleShow () = ""

instance (SimpleShow a,SimpleShow b) => SimpleShow (a,b) where
  simpleShow (a,b) = "(" ++ simpleShow a ++ ", " ++ simpleShow b ++ ")"

instance (SimpleShow a,SimpleShow b, SimpleShow c) => SimpleShow (a,b,c) where
  simpleShow (a,b,c) = "(" ++ simpleShow a ++ ", " ++ simpleShow b ++ ", " ++ simpleShow c ++ ")"


instance SimpleShow a => SimpleShow [a] where
  simpleShow xs = "[" ++ (concat $ List.intersperse "," $ fmap simpleShow xs) ++ "]"


instance SimpleShow a => SimpleShow (Set a) where
  simpleShow xs = "{" ++ (concat $ List.intersperse "," $ fmap simpleShow $ Set.toList xs) ++ "}"


instance (SimpleShow k, SimpleShow v       ) => SimpleShow (Map k v) where
  simpleShow xs = "[" ++ (concat $ List.intersperse "," $ fmap simpleShow $ Map.toList xs) ++ "]"



instance SimpleShow Var where
  simpleShow (Global x) = x
  simpleShow (ThreadLocal x) = x ++ " (thread local)"
  simpleShow (Register i) = "r" ++ (show i) ++ ""

instance SimpleShow Array where
  simpleShow (Array x) = x ++ "[]"

type Val = Int

centralValue :: Val
centralValue = 0


type ArrayVal = Map Int Val

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

data GlobalState = GlobalState {
    σv :: (Map Var Val),
    σa :: (Map Array ArrayVal)
  } deriving (Show, Eq, Ord, Generic, NFData)

globalEmpty :: GlobalState
globalEmpty = GlobalState { σv = Map.empty, σa = Map.empty }

nonZeroOnly :: GlobalState -> GlobalState
nonZeroOnly σ@(GlobalState { σv, σa }) = σ{ σv = Map.filter (/=0) σv, σa = fmap (Map.filter (/=0)) σa }

instance SimpleShow GlobalState where
  simpleShow (GlobalState { σv, σa }) = "{ v = " ++ simpleShow σv ++ ", a = " ++ simpleShow σa ++ "}"

type ThreadLocalState = Map Var Val
-- type CombinedState = Map Var Val

data BoolFunction = CTrue   | CFalse | Leq VarFunction VarFunction | And BoolFunction BoolFunction | Not BoolFunction | Or BoolFunction BoolFunction deriving (Show, Eq, Ord)
data VarFunction   = Val Val | Var Var | Plus VarFunction VarFunction | Times VarFunction VarFunction | Div VarFunction VarFunction | Mod VarFunction VarFunction | Xor VarFunction VarFunction | BAnd VarFunction VarFunction | Shl VarFunction VarFunction | Shr VarFunction VarFunction | Neg VarFunction | ArrayRead Array VarFunction | AssertRange Val Val VarFunction deriving (Show, Eq, Ord)

eeq a b = (a `Leq` b) `And` (b `Leq` a)

instance SimpleShow BoolFunction where
  simpleShow CTrue  = "true"
  simpleShow CFalse = "false"
  simpleShow (Leq a b) = "(" ++ simpleShow a ++ " <= " ++ simpleShow b ++ ")"
  simpleShow (Or  a b) = "(" ++ simpleShow a ++ " || " ++ simpleShow b ++ ")"
  simpleShow (And a b) =        simpleShow a ++ " && " ++ simpleShow b
  simpleShow (Not a  ) = "!" ++ simpleShow a

instance SimpleShow VarFunction where
  simpleShow (Val x) = show x
  simpleShow (Var x) = simpleShow x
  simpleShow (Plus  a b) = "(" ++ simpleShow a ++ " + " ++ simpleShow b ++ ")"
  simpleShow (Xor   a b) = "(" ++ simpleShow a ++ " ^ " ++ simpleShow b ++ ")"
  simpleShow (BAnd  a b) =        simpleShow a ++ " & " ++ simpleShow b       
  simpleShow (Times a b) =        simpleShow a ++ " * " ++ simpleShow b
  simpleShow (Div   a b) =        simpleShow a ++ " / " ++ simpleShow b
  simpleShow (Mod   a b) =        simpleShow a ++ " % " ++ simpleShow b
  simpleShow (Shl   a b) =        simpleShow a ++ " << " ++ simpleShow b
  simpleShow (Shr   a b) =        simpleShow a ++ " >> " ++ simpleShow b
  simpleShow (Neg   a  ) = "-" ++ simpleShow a
  simpleShow (ArrayRead (Array a) b) = a ++ "[" ++ simpleShow b ++ "]"
  simpleShow (AssertRange min max a) = simpleShow a ++ " within [" ++ (show min) ++ ", " ++ (show max) ++ "]"


evalB :: GlobalState -> ThreadLocalState -> BoolFunction -> Bool
evalB _  _ CTrue     = True
evalB _  _ CFalse    = False
evalB σg σl (Leq x y) = evalV σg σl  x <= evalV σg σl  y
evalB σg σl (And b1 b2) = evalB σg σl  b1 && evalB σg σl  b2
evalB σg σl (Or  b1 b2) = evalB σg σl  b1 || evalB σg σl  b2
evalB σg σl (Not b)     = not $ evalB σg σl  b

useB = useBFor useV

useBFor useV CTrue       = Set.empty
useBFor useV CFalse      = Set.empty
useBFor useV (Leq x y)   = useV x ∪ useV y
useBFor useV (And b1 b2) = useBFor useV b1 ∪ useBFor useV b2
useBFor useV (Or  b1 b2) = useBFor useV b1 ∪ useBFor useV b2
useBFor useV (Not b)     = useBFor useV b

evalV :: GlobalState -> ThreadLocalState -> VarFunction -> Val
evalV σg σl vf = (evalVM σg σl vf) `rem` 16 -- lets keep values small :O
evalVM :: GlobalState -> ThreadLocalState -> VarFunction -> Val
evalVM _  _  (Val  x)    = x
evalVM σg@(GlobalState { σv }) σl (Var  x) = case Map.lookup x σl of
  Nothing -> case Map.lookup x σv of
    Nothing -> error $ show (σg, σl) ++ "does not contain:    " ++ (show x)
    Just val -> val
  Just val -> val
evalVM σg@(GlobalState { σa }) σl (ArrayRead a x) =
  let index = evalVM σg σl x in case Map.lookup a σa of
    Nothing -> error $ show (σg) ++ "does not contain array:    " ++ (show a)
    Just array -> case Map.lookup index array of
      Nothing -> error $ "array index out of bounds:    " ++ (show a) ++ ", " ++ (show index) ++ ", " ++ (show array)
      Just val -> val

evalVM σg σl (Plus  x y) = evalVM σg σl  x + evalVM σg σl  y
evalVM σg σl (Times x y) = evalVM σg σl  x * evalVM σg σl  y
evalVM σg σl (Div   x y) = evalVM σg σl  x `div` evalVM σg σl  y
evalVM σg σl (Mod x y)   = evalVM σg σl  x `mod` evalVM σg σl  y
evalVM σg σl (Shl   x y) = evalVM σg σl  x `shiftL` evalVM σg σl  y
evalVM σg σl (Shr   x y) = evalVM σg σl  x `shiftR` evalVM σg σl  y
evalVM σg σl (Xor   x y) = evalVM σg σl  x `xor` evalVM σg σl  y
evalVM σg σl (BAnd  x y) = evalVM σg σl  x .&. evalVM σg σl  y

evalVM σg σl (Neg x)     = - evalVM σg σl  x
evalVM σg σl (AssertRange _ _ x) = evalVM σg σl  x


data Name = VarName Var | ArrayName Array deriving (Eq, Show, Ord)

isGlobalName (VarName var)   = isGlobal var
isGlobalName (ArrayName arr) = True


useV :: VarFunction -> Set Name
useV (ArrayRead a i) = Set.insert (ArrayName a) $ useV i
useV (Val  x)    = Set.empty
useV (Var  x)    = Set.fromList [VarName x]
useV (Plus  x y) = useV x ∪ useV y
useV (Times x y) = useV x ∪ useV y
useV (Div   x y) = useV x ∪ useV y
useV (Mod   x y) = useV x ∪ useV y
useV (Shl   x y) = useV x ∪ useV y
useV (Shr   x y) = useV x ∪ useV y
useV (Xor   x y) = useV x ∪ useV y
useV (BAnd  x y) = useV x ∪ useV y
useV (Neg x)     = useV x
useV (AssertRange _ _ x) = useV x


data CFGEdge = Guard  Bool BoolFunction
             | Assign Var  VarFunction
             | AssignArray Array VarFunction VarFunction
             | Read   Var          InputChannel
             | Print  VarFunction  OutputChannel
             | Call
             | CallSummary
             | Use    [Name]
             | Def    [Name]
             | Return
             | NoOp
             | Spawn
             deriving (Show, Eq, Ord)

instance SimpleShow CFGEdge where
  simpleShow (Guard True  bf) =         simpleShow bf
  simpleShow (Guard False bf) = "!" ++ simpleShow bf
  simpleShow (Assign x vf)    = simpleShow x ++ " := " ++ simpleShow vf
  simpleShow (AssignArray (Array x) i vf) = x ++ "[" ++ simpleShow i ++ "] := " ++ simpleShow vf
  simpleShow (NoOp) = ""
  simpleShow e = show e

instance (SimpleShow Node) where
  simpleShow = show

isIntraCFGEdge :: CFGEdge -> Bool
isIntraCFGEdge Call    = False
isIntraCFGEdge Return  = False
isIntraCFGEdge Spawn   = False
isIntraCFGEdge _       = True

useE :: CFGEdge -> Set Name
useE = useEFor useV useB

useEFor useV useB (Guard   _ bf) = useB bf
useEFor useV useB (AssignArray a i vf) = useV i ∪ useV vf
useEFor useV useB (Assign  _ vf) = useV vf
useEFor useV useB (Read    _ _)  = Set.empty
useEFor useV useB Spawn          = Set.empty
useEFor useV useB (Print vf _)   = useV vf
useEFor useV useB NoOp           = Set.empty
useEFor useV useB (Def _)        = Set.empty
useEFor useV useB (Use xs)       =   (∐) [ useV $ ArrayRead a (Val 0) | ArrayName a <- xs ]
                                   ∪ (∐) [ useV $ Var v               | VarName   v <- xs ] -- == Set.fromList xs
useEFor useV useB CallSummary    = Set.empty
useEFor useV useB Call           = Set.empty
useEFor useV useB Return         = Set.empty

defE :: CFGEdge -> Set Name
defE (Guard   _ _) = Set.empty
defE (Assign  x _) = Set.singleton $ VarName x
defE (AssignArray a _ _) = Set.singleton $ ArrayName a
defE (Read    x _) = Set.singleton $ VarName x
defE Spawn         = Set.empty
defE (Print   _ _) = Set.empty
defE NoOp          = Set.empty
defE (Def xs)      = Set.fromList xs
defE (Use _)       = Set.empty
defE CallSummary   = Set.empty
defE Call          = Set.empty
defE Return        = Set.empty


use :: Graph gr => gr a CFGEdge -> CFGNode -> Set Name
use gr n = Set.unions [ useE e | (n',e) <- lsuc gr n ]

def :: Graph gr => gr a CFGEdge -> CFGNode -> Set Name
def gr n = Set.unions [ defE e | (n',e) <- lsuc gr n ]

-- varsInCfg :: Graph gr => gr CFGNode CFGEdge -> Set Var
-- varsInCfg gr  = Set.unions [ useE e ∪ defE e | (_,_,e) <- labEdges gr ]

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
  && and [  length [ n'  | (n', Guard  _ _) <- lsuc gr n ] ∊ [0,1,2] | n <- nodes gr]
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
  && and [ (length [ n'  | (n', Call) <- lsuc gr n ] /= 0)
            →   (  length [ n'  | (n', Call)        <- lsuc gr n ] == 1
                 && length [ n'  | (n', CallSummary) <- lsuc gr n ] == 1
                 && length [ n'  | (n', _)           <- lsuc gr n ] == 2 ) | n <- nodes gr]
  && and [ (length [ n'  | (n', Return) <- lsuc gr n ] /= 0)
            →   (  length [ n'  | (n', Return)        <- lsuc gr n ] == (length $ lsuc gr n)) | n <- nodes gr]


type Input = Map InputChannel [Val]
type ThreadLocalControlState = (Node, [(Node, Node)]) -- (node, [(callNode, entryNode)])
type ControlState = [ThreadLocalControlState]
type ThreadLocalStates = [ThreadLocalState]
type Configuration = (ControlState,GlobalState,ThreadLocalStates,Input)
data Event = PrintEvent Val OutputChannel
           | ReadEvent  Val InputChannel
           | Tau
           deriving (Eq, Ord, Show, Generic, NFData)

fromEdge :: GlobalState -> ThreadLocalState -> Input -> CFGEdge -> Event
fromEdge σg σl i (Guard b bf)
  | b == evalB σg σl  bf = Tau
  | otherwise            = undefined
fromEdge σg σl i (Assign x  vf) = Tau
fromEdge σg σl i (AssignArray _ _ _) = Tau
fromEdge σg σl i (Read   x  ch) = ReadEvent  (head $ i ! ch)   ch
fromEdge σg σl i (Print  vf ch) = PrintEvent (evalV σg σl vf) ch
fromEdge σg σl i (Spawn      ) = Tau
fromEdge σg σl i (NoOp       ) = Tau
fromEdge σg σl i (Call       ) = Tau
fromEdge σg σl i (CallSummary) = error "control flow cannot pass CallSummary"


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
type Trace          = [((GlobalState, ThreadLocalState), (Node,Event), (GlobalState, ThreadLocalState))]

eventStep :: Graph gr => gr CFGNode CFGEdge -> Configuration -> [((Node,Event,Int),Configuration)]
eventStep icfg config@(control,globalσ,tlσs,i) = do
       ((n,callString),tlσ,index) <- zip3 control tlσs [0..]
       let (spawn,normal) = partition (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False }) $ [ (n',e) | (n', e) <- lsuc icfg n, e /= CallSummary ]

       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       let configs' = [ ((n,fromEdge globalσ tlσ i cfgEdge), (control',globalσ', tlσ', i'))  | (n', cfgEdge) <- normal,
                                                                                         (globalσ',tlσ', i') <- stepFor cfgEdge (globalσ,tlσ,i),
                                                                                         control' <- controlStateFor (n', cfgEdge) (n, callString)
                      ]


       case (spawn, configs') of (_ ,[((_,event),((n',stack), globalσ', tlσ', i'))]) ->
                                                                         return ((n,event,index),((n', stack)   : ([(spawned,[])   | (spawned, Spawn) <- spawn] ++ (deleteAt index control)),
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


eventStepAt :: Graph gr => Int ->  gr CFGNode CFGEdge -> Configuration -> ((Node,Event,Int),Configuration)
eventStepAt index icfg config@(control,globalσ,tlσs,i) =
       let (nCs@(n,callString),tlσ) = (zip control tlσs) !! index
           c = (globalσ,tlσ,i)
           succs = lsuc icfg n
           spawn = filter (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False}) succs

           resultFast = go succs
             where go []                     = case spawn of [] ->              ((n,Tau,index),  (                                                    deleteAt index control,
                                                                                                  globalσ,
                                                                                                                                                      deleteAt index tlσs,
                                                                                                  i
                                                                                ))
                                                             _  -> error "spawn an exit-node"
                   go (e@(n', cfgEdge) : es) = case cfgEdge of
                     Spawn ->       go es
                     CallSummary -> go es
                     _           -> case stepFor cfgEdge c of
                                      [(globalσ', tlσ', i')] -> case controlStateFor e nCs of
                                        [control'] -> let event = fromEdge globalσ tlσ i cfgEdge in
                                                                                ((n,event,index),(control' : ([(spawned,[])   | (spawned, _) <- spawn] ++ (deleteAt index control)),
                                                                                                  globalσ',
                                                                                                  tlσ'     : ([Map.empty      | (spawned, _) <- spawn] ++ (deleteAt index tlσs   )),
                                                                                                  i'
                                                                                ))
                                        _ -> go es
                                      _ -> go es
       in resultFast



step :: Graph gr => gr CFGNode CFGEdge -> Configuration -> [Configuration]
step icfg config@(control,globalσ,tlσs,i) = do
       ((n, callString),tlσ,index) <- zip3 control tlσs [0..]
       let (spawn,normal) = partition (\(n', cfgEdge) -> case cfgEdge of { Spawn -> True ; _ -> False }) $  [ (n',e) | (n', e) <- lsuc icfg n, e /= CallSummary ]

       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       let configs' = [ (control',globalσ', tlσ', i')  | (n', cfgEdge) <- normal,
                                                         (globalσ',tlσ', i') <- stepFor cfgEdge (globalσ,tlσ,i),
                                                         control' <- controlStateFor (n', cfgEdge) (n, callString)
                      ]

       -- Falls es normale normale nachfolger gibt, dann genau genau einen der passierbar ist
       case (spawn, configs') of (_,[((n',stack), globalσ', tlσ', i')]) ->
                                                            return ((n',stack) : ([(spawned,[])  | (spawned, Spawn) <- spawn] ++ (deleteAt index control)),
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


controlStateFor :: (Node, CFGEdge) -> ThreadLocalControlState -> [ThreadLocalControlState]
controlStateFor (m, Call)   (n, stack) =  [(m, (n, m):stack)]
controlStateFor (m, Return) (n, (m', n'):stack)
  | n == n' && m == m'  = [(m, stack)]
  | otherwise           = []
controlStateFor (m, CallSummary) _ = error "cannot pass CallSummary"
controlStateFor (m, _)      (n, stack) = [(m, stack)]

stepFor :: CFGEdge -> (GlobalState,ThreadLocalState,Input) -> [(GlobalState,ThreadLocalState,Input)]
stepFor e c@(globalσ@(GlobalState {σv, σa}), tlσ, i)  = step e where
      step :: CFGEdge ->  [(GlobalState,ThreadLocalState,Input)]
      step (Guard b bf)
        | b == evalB globalσ tlσ bf      = [c]
        | otherwise                      = []
      step (Assign x@(Global _)      vf) = [( globalσ{σv = Map.insert x val σv},                              tlσ,                    i)]
        where val = evalV globalσ tlσ vf
      step (Assign x                 vf) = [( globalσ                          , Map.insert x val             tlσ,                    i)]
        where val = evalV globalσ tlσ vf
      step (Read   x@(Global _)      ch) = [( globalσ{σv = Map.insert x val σv},                              tlσ, Map.adjust tail ch i)]
        where val = head $ i ! ch
      step (Read   x                 ch) = [( globalσ                          , Map.insert x (head $ i ! ch) tlσ, Map.adjust tail ch i)]
      step (AssignArray a ix         vf) = [( globalσ{σa = insert a index val },                              tlσ,                    i)]
        where val   = evalV globalσ tlσ vf
              index = arrayIndex $
                      evalV globalσ tlσ ix
              insert a i val = Map.alter f a σa
                where f (Nothing) = Just $ Map.insert i val $ arrayEmpty
                      f ( Just a) = Just $ Map.insert i val $ a
      step (Print  x ch)                 = [c]
      step (Spawn      )                 = undefined
      step (NoOp       )                 = [c]
      step (Call       )                 = [c]
      step (Return     )                 = [c]

hide (a,b,c,d) = (a,b,c)

toTrace :: ExecutionTrace -> Trace
toTrace eTrace = [ ((globalσ, tlσs !! index), (n,e), (globalσ', if not $ List.null tlσs' then tlσs' !! 0 else Map.empty)) | ((_,globalσ,tlσs,_), (n,e,index), (_,globalσ',tlσs',_)) <- eTrace ]




observable :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> SecurityLattice -> Trace -> Trace
observable icfg obs l trace = [ (restr σ (use icfg n), (n,e), restr σ' (def icfg n)) | (σ, (n,e), σ') <- trace, Just l' <- [obs n], l' ⊑ l ]
  where restr :: (GlobalState, ThreadLocalState) -> (Set Name) -> (GlobalState, ThreadLocalState)
        restr (GlobalState {σv, σa}, tlσ) use =
          ( GlobalState (Map.filterWithKey (\var _ -> VarName   var ∈ use) σv )
                        (Map.filterWithKey (\arr _ -> ArrayName arr ∈ use) σa ),
                        (Map.filterWithKey (\var _ -> VarName   var ∈ use) tlσ)
          )

(≈) :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification -> SecurityLattice -> Trace -> Trace -> Bool
(≈) icfg obs l t t' = (observable icfg obs l t) == (observable icfg obs l t')


-- lsod :: Graph gr => 

-- irlsod :: Graph gr => Program gr -> 
