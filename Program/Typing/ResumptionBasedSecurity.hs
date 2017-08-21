{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Program.Typing.ResumptionBasedSecurity where

import Algebra.Lattice
import qualified Algebra.PartialOrd as PartialOrd

import Unicode
import Util

-- import Program
import qualified Program.For
import Program.Generator (GeneratedProgram(..), Generated(..), toCode)

import IRLSOD

import Debug.Trace

import Control.Monad.State.Lazy

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (nub, intersperse)
import Data.Maybe (isJust)
import Program.Defaults (defaultChannelObservability)

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.DFS(topsort, scc)
import Data.Graph.Inductive.Query.TransClos


type VarTyping  = Var ->  SecurityLattice
type ChannelTyping = Channel -> SecurityLattice
type ExpBTyping = BoolFunction -> SecurityLattice
type ExpVTyping = VarFunction -> SecurityLattice





data For = If   BoolFunction For For
         | Ch   Double For For
         | Ass  Var VarFunction
         | ForC Val For
         | ForV Var For
         | While (BoolFunction) For
         | Seq For For
         | Skip
         | ReadFromChannel Var         InputChannel
         | PrintToChannel  VarFunction OutputChannel
         | Par  [For]
         | ParT [For]
         | ClassifyGlobally Var SecurityLattice
  deriving Show


for2ResumptionFor :: Map ThreadId Program.For.For -> ThreadId -> Maybe For
for2ResumptionFor code mainThread =  f2f [mainThread] False [] (code ! mainThread)
  where f2f spawnString inLoop []     (Program.For.Skip)    = return $ Skip
        f2f spawnString inLoop (c:cs) (Program.For.Skip)    = do
            c' <- f2f spawnString inLoop cs c
            return $ Skip `Seq` c'

        f2f spawnString inLoop []     (Program.For.Ass x e) = return $ Ass x e
        f2f spawnString inLoop (c:cs) (Program.For.Ass x e) = do
            c' <- f2f spawnString inLoop cs c
            return $ (Ass x e) `Seq` c'


        f2f spawnString inLoop []     (Program.For.ReadFromChannel x ch) = return $ ReadFromChannel x ch
        f2f spawnString inLoop (c:cs) (Program.For.ReadFromChannel x ch) = do
            c' <- f2f spawnString inLoop cs c
            return $ (ReadFromChannel x ch) `Seq` c'

        f2f spawnString inLoop []     (Program.For.PrintToChannel e ch) = return $ PrintToChannel e ch
        f2f spawnString inLoop (c:cs) (Program.For.PrintToChannel e ch) = do
            c' <- f2f spawnString inLoop cs c
            return $ (PrintToChannel e ch) `Seq` c'


        f2f spawnString inLoop []     (Program.For.If b c1 c2) = do
            c1' <- f2f spawnString inLoop [] c1
            c2' <- f2f spawnString inLoop [] c2
            return $ If b c1' c2'
        f2f spawnString inLoop (c:cs) (Program.For.If b c1 c2)
            | any isSpawn (foldMap Program.For.subCommands [c1,c2]) = do
                    c1' <- f2f spawnString inLoop cs c1
                    c2' <- f2f spawnString inLoop cs c2
                    return $ If b c1' c2'
            | otherwise                                             = do
                    c1' <- f2f spawnString inLoop [] c1
                    c2' <- f2f spawnString inLoop [] c2
                    c'  <- f2f spawnString inLoop cs c
                    return $ (If b c1' c2') `Seq` c'
          where isSpawn (Program.For.SpawnThread _) = True
                isSpawn _                           = False
        f2f spawnString inLoop []     (Program.For.ForC x c0)
            | x > 0     = do
                    c0' <- f2f spawnString inLoop [] c0
                    return $ foldr1 Seq (take (fromInteger x) $ repeat c0')
            | otherwise = return Skip
          where 
        f2f spawnString inLoop (c:cs) (Program.For.ForC x c0)
            | x > 0     = do
                    c0' <- f2f spawnString inLoop [] c0
                    c'  <- f2f spawnString inLoop cs c
                    return $ foldr1 Seq (take (fromInteger x) $ repeat c0') `Seq` c'
            | otherwise = f2f spawnString inLoop cs c
          where 
        f2f spawnString inLoop []     (Program.For.ForV x c0) = do
                    c0' <-f2f spawnString True [] c0
                    return $ ForV x c0'
        f2f spawnString inLoop (c:cs) (Program.For.ForV x c0) = do
                    c0' <- f2f spawnString True [] c0
                    c'  <- f2f spawnString inLoop cs c
                    return $ ForV x c0' `Seq` c'

        f2f spawnString inLoop cs     (Program.For.Seq c1 c2) = f2f spawnString inLoop (c2:cs) c1

        f2f spawnString inLoop []     (Program.For.SpawnThread θ)
            | (not inLoop) ∧ (not $ θ ∈ spawnString) = do
                    cθ <- f2f (θ:spawnString) False [] (code ! θ)
                    return $ Par [cθ]
            | otherwise                              = mzero
        f2f spawnString inLoop (c:cs) (Program.For.SpawnThread θ)
            | (not inLoop) ∧ (not $ θ ∈ spawnString) = do
                    cθ <- f2f (θ:spawnString) False [] (code ! θ)
                    c' <- f2f spawnString inLoop cs c
                    return $ Par ([cθ, c'])
            | otherwise                              = mzero
          where 


subCommands :: For -> [For]
subCommands c@(If _ c1 c2) = c:(subCommands c1 ++ subCommands c2)
subCommands c@(Ch _ c1 c2) = c:(subCommands c1 ++ subCommands c2)
subCommands c@(ForC _ c1)  = c:(subCommands c1)
subCommands c@(ForV _ c1)  = c:(subCommands c1)
subCommands c@(While _ c1) = c:(subCommands c1)
subCommands c@(Seq c1 c2)  = c:(subCommands c1++ subCommands c2)
subCommands c@(Par  cs)     = c:(foldMap subCommands cs)
subCommands c@(ParT cs)     = c:(foldMap subCommands cs)
subCommands c = [c]




exampleInitialize =
      ClassifyGlobally "h"  High    `Seq`
      ClassifyGlobally "h'" High    `Seq`
      ClassifyGlobally "l"  Low     `Seq`
      ClassifyGlobally "l'" Low

exampleD0Body =
    Ass "h'" (Val 0)                           `Seq`
    While (Not $ ((Var "h") `Leq` (Val 0))) (
        Ch 0.5
           (Ass "h"   (Val 0))
           (Ass "h'"  ((Var "h'") `Plus` (Val 1)))
    )
exampleD0 = exampleInitialize `Seq` exampleD0Body

exampleD1Body =
    While (Not $ ((Var "h") `Leq` (Val 0))) (
        Ch 0.5
           (Ass "h"   ((Var "h") `Plus` (Val (-1))))
           (Ass "h"   ((Var "h") `Plus` (Val   1 )))
    )
exampleD1 = exampleInitialize `Seq` exampleD1Body

exampleD2Body =
    If ((Var "l") `Leq` (Val 0))
        (Ass "l'" (Val 1))
        exampleD0Body
exampleD2 = exampleInitialize `Seq` exampleD2Body


exampleD3Body =
    Ass "h" (Val 5)                          `Seq`
    ParT [ exampleD0Body, Ass "l" (Val 1) ]  
exampleD3 = exampleInitialize `Seq` exampleD3Body


exampleD3'Body =
    Ass "h" (Val 5)                          `Seq`
    Par [ exampleD0Body, Ass "l" (Val 1) ]  
exampleD3' = exampleInitialize `Seq` exampleD3'Body


exampleD4Body =
    If ((Var "h") `Leq` (Val 0))
       (Ass "h" (Val 1)  `Seq` Ass "h" (Val 2))
       (Ass "h" (Val 3)                       )   `Seq`
    Ass "l" (Val 4)
exampleD4 = exampleInitialize `Seq` exampleD4Body

exampleD4'Body =
    If ((Var "h") `Leq` (Val 0))
       (Ass "h" (Val 1)  `Seq` Ass "h" (Val 2))
       (Ass "h" (Val 3)                       )   `Seq`
    Ass "h" (Val 4)
exampleD4' = exampleInitialize `Seq` exampleD4'Body



exampleD5Body = ParT [ exampleD4, Ass "l" (Val 5) ]
exampleD5 = exampleInitialize `Seq` exampleD5Body


exampleD5'Body = ParT [ exampleD4', Ass "l" (Val 5) ]
exampleD5' = exampleInitialize `Seq` exampleD5'Body




example0 :: Map ThreadId For
example0 = Map.fromList $ [
  (1, Ass "x" (Val 1))
 ]
var0 "x" = High
main0 = 1

example1 :: Map ThreadId For
example1 = Map.fromList $ [
  (1, Ass "x" (Val 1))
 ]
var1 "x" = Low
main1 = 1

example2 :: Map ThreadId For
example2 = Map.fromList $ [
  (1, If ((Var "h") `Leq` (Val 0)) (
        Ass "l" (Val 1)
      ) {-else-} (
        Ass "l" (Val 2)
      )
   )
 ]
var2 "l" = Low
var2 "h" = High
main2 = 1



expBTypingFrom :: VarTyping -> ExpBTyping
expBTypingFrom var e = (∐) [ var v | v <- Set.toList $ useB e]

expVTypingFrom :: VarTyping -> ExpVTyping
expVTypingFrom var e = (∐) [ var v | v <- Set.toList $ useV e]

data Criterion = Impossible | Discr | Siso | StrongBisimilarity | ZeroOneBisimilarity | None deriving (Show, Eq)


instance JoinSemiLattice Criterion where
  Impossible             `join` x                   = x
  x                      `join` Impossible          = x

  Discr                  `join` Siso                = StrongBisimilarity
  Siso                   `join` Discr               = StrongBisimilarity

  Discr                  `join` x                   = x
  x                      `join` Discr               = x

  Siso                   `join` x                   = x
  x                      `join` Siso                = x

  StrongBisimilarity     `join` x                   = x
  x                      `join` StrongBisimilarity  = x

  ZeroOneBisimilarity    `join` x                   = x
  x                      `join` ZeroOneBisimilarity = x

  x          `join`             y                   = None


instance BoundedJoinSemiLattice Criterion where
  bottom = Impossible


instance PartialOrd.PartialOrd Criterion where
  c1 `leq` c2 =  c1 ⊔ c2 == c2


data ProgramTyping = ProgramTyping {
 var :: Map Var SecurityLattice,
 criterion :: Criterion
} deriving (Show, Eq)








-- Monade für Berechnungen, bei deren Ausführung frische Werte (z.B. Typvariablen) generiert und verbraucht werden.
type LevelVariable = Node
-- data Level  =  SecurityLevel SecurityLattice | LevelVariable LevelVariable deriving (Show, Eq, Ord)
type Fresh s = State [LevelVariable] s

freshVar :: Fresh LevelVariable
freshVar =
    do (fresh:rest) <- get
       put rest
       return fresh

evalFresh f = evalState f [0..]


nLow = -2
nHigh = -1
nVarStart = -3
nLevel Low = nLow
nLevel High = nHigh




pres :: ChannelTyping -> Map Var LevelVariable -> For -> Gr ConstraintNode ConstraintEdge -> Gr ConstraintNode ConstraintEdge 
pres _   _      Skip     deps = deps
pres _   var c@(Ass x _) deps =
      insEdges [ (var ! x ,                       nHigh,                          Pres c) ]
    $ insEdges [ (nHigh,                          var ! x ,                       Pres c) ]
    $ deps
pres obs var c@(ReadFromChannel x ch) deps =
      insEdges [ (nLevel $ obs ch,                var ! x,                        Pres c) ]
    $ insEdges [ (var ! x ,                       nHigh,                          Pres c) ]
    $ insEdges [ (nHigh,                          var ! x ,                       Pres c) ]
      -- in the LSOD-Setting, a low read is always visible.
      -- Hence, in order to obtain "fair"(™) comparison,
      -- we demand that low read cannot be regarded preserving by reading into a high variable
    $ insEdges [ (var ! x,                        nLevel $ obs ch,                  Cpt c) ]
    $ deps
pres obs var c@(PrintToChannel  e ch) deps =
      insEdges [ (var ! x,                        nLevel $ obs ch,                Pres c) | x <- Set.toList $ useV e ]
    $ insEdges [ (var ! x ,                       nHigh,                          Pres c) | x <- Set.toList $ useV e ]
    $ insEdges [ (nHigh,                          var ! x ,                       Pres c) | x <- Set.toList $ useV e ]
    $ deps
pres obs var c@(ClassifyGlobally x lvl) deps =
      insEdges [ (var ! x,                        nLvl,                           Pres c) ]
    $ insEdges [ (nLvl,                           var ! x ,                       Pres c) ]
    $ deps
 where nLvl = case lvl of
         Low -> nLow
         High -> nHigh
pres _   _   _                        _    = undefined


cpt :: ChannelTyping -> Map Var LevelVariable -> For -> Gr ConstraintNode ConstraintEdge -> Gr ConstraintNode ConstraintEdge 
cpt _   _      Skip     deps = deps
cpt _   var c@(Ass x e) deps =
      insEdges [ (var ! x',                       var ! x,                          Cpt c) | x' <- Set.toList $ useV e ]
    $ deps
cpt obs var c@(ReadFromChannel x ch) deps =
      insEdges [ (nLevel $ obs ch,                var ! x,                          Cpt c) ]
      -- in the LSOD-Setting, a low read is always visible.
      -- Hence, in order to obtain "fair"(™) comparison,
      -- we demand that low read cannot be regarded compatible by reading into a high variable
    $ insEdges [ (var ! x,                        nLevel $ obs ch,                  Cpt c) ]
    $ deps
cpt obs var c@(PrintToChannel  e ch) deps =
      insEdges [ (var ! x,                        nLevel $ obs ch,                  Cpt c) | x <- Set.toList $ useV e ]
    $ deps
cpt obs var c@(ClassifyGlobally x lvl) deps =
      insEdges [ (var ! x,                        nLvl,                           Pres c) ]
    $ insEdges [ (nLvl,                           var ! x ,                       Pres c) ]
    $ deps
 where nLvl = case lvl of
         Low -> nLow
         High -> nHigh
cpt _   _   _                        _    = undefined


cptE ::  Map Var LevelVariable -> BoolFunction -> Gr ConstraintNode ConstraintEdge -> Gr ConstraintNode ConstraintEdge
cptE var b deps = 
      insEdges [ (var ! x',                       nLow,                             CptE b) | x' <- Set.toList $ useB b ]
    $ deps





data ForProgram = ForProgram {
  code :: For,
  channelTyping :: ChannelTyping
 }
type ThreadId = Integer


isSecureResumptionBasedSecurity :: Criterion -> GeneratedProgram -> Maybe Bool
isSecureResumptionBasedSecurity maximalCriterion gen =  do
        typings <- principalTypingOfGen maximalCriterion gen
        return $ not $ null $ [ criterion | (ProgramTyping { criterion }, _) <- typings , criterion ⊑ maximalCriterion]


isSecureResumptionBasedSecurityFor ::  Criterion -> ForProgram -> Bool
isSecureResumptionBasedSecurityFor maximalCriterion  p = not $ null $ [ criterion | (ProgramTyping { criterion }, _) <- principalTypingOf    maximalCriterion p,   criterion ⊑ maximalCriterion]


principalTypingOfGen :: Criterion -> GeneratedProgram -> Maybe [(ProgramTyping, Gr ConstraintNode ConstraintEdge)]
principalTypingOfGen  maximalCriterion  gen = do
        let code = toCode gen
        code' <- for2ResumptionFor code 1
        return $ principalTypingOf  maximalCriterion (ForProgram { code = code', channelTyping = defaultChannelObservability })

data ConstraintNode = ConstLevel SecurityLattice | VarLevel Var deriving Show
data ConstraintEdge = Pres For | Cpt For | CptE BoolFunction | OtherE deriving Show

principalTypingOf ::  Criterion -> ForProgram ->  [(ProgramTyping, Gr ConstraintNode ConstraintEdge)]
principalTypingOf  maximalCriterion p@(ForProgram { code }) = principalTypingUsing  maximalCriterion initial var p
    where initial = mkGraph ([(nLow,ConstLevel Low), (nHigh,ConstLevel High)] ++ [ (n,VarLevel v) | (v,n) <- Map.assocs var ])
                            [(nLow,nHigh,OtherE)]
          var =  varsToLevelVariable code

varsToLevelVariable :: For -> Map Var LevelVariable
varsToLevelVariable p = Map.fromList [
    (x,n) | (x,n) <- zip (nub $ [ x |
                                  x <- [ x | Ass  x' e            <- subCommands p, x <- [x'] ++ (Set.toList $ useV e)]
                                    ++ [ x | ForV x  _            <- subCommands p]
                                    ++ [ x | If e _ _             <- subCommands p, x <-         (Set.toList $ useB e)]
                                    ++ [ x | ReadFromChannel x _  <- subCommands p]
                                    ++ [ x | PrintToChannel  e _  <- subCommands p, x <-         (Set.toList $ useV e)]
                                    ++ [ x | ClassifyGlobally x l <- subCommands p]
                                ]
                          )
                          [nVarStart, nVarStart -1 ..]
  ]


principalTypingUsing :: Criterion -> Gr ConstraintNode ConstraintEdge -> Map Var LevelVariable -> ForProgram -> [(ProgramTyping, Gr ConstraintNode ConstraintEdge)]
principalTypingUsing maximalCriterion initial var p@(ForProgram { code, channelTyping })  =
 do  (criterion, varDependencies :: Gr ConstraintNode ConstraintEdge) <- (varDependenciesOf maximalCriterion var channelTyping code initial)

     let deps = trc varDependencies
     let sccs = scc varDependencies
     let sccOf node = the (node `elem`) $ sccs
     let solvable = all (\component -> not $ (nHigh ∈ component ∧ nLow ∈ component)) sccs

     if (solvable) then
       return (
         ProgramTyping {
          var = Map.fromList [ (x, if (nHigh `elem` pre deps nX) then High else Low ) | (x,nX) <- Map.assocs var],
          criterion = criterion
         },
         varDependencies
        )
      else
        return (ProgramTyping { var = Map.empty, criterion = None}, varDependencies)


varDependenciesOfAtm :: Criterion -> (Map Var LevelVariable) -> ChannelTyping -> For ->  Gr ConstraintNode ConstraintEdge -> [(Criterion, Gr ConstraintNode ConstraintEdge)]
varDependenciesOfAtm  maximalCriterion var obs c deps
    | maximalCriterion == Impossible = []
    | maximalCriterion == Discr      = presConstraints
    | maximalCriterion == Siso       = cptConstraints
    | otherwise                      = presConstraints ++ cptConstraints
  where presConstraints = [(Discr, pres obs var c deps)]
        cptConstraints  = [(Siso,  cpt  obs var c deps)]


varDependenciesOf :: Criterion -> (Map Var LevelVariable) -> ChannelTyping -> For ->  Gr ConstraintNode ConstraintEdge -> [(Criterion, Gr ConstraintNode ConstraintEdge)]
varDependenciesOf Impossible       var obs _ deps = []
varDependenciesOf maximalCriterion var obs c@(Skip)                   deps = varDependenciesOfAtm maximalCriterion var obs c deps
varDependenciesOf maximalCriterion var obs c@(Ass x e)                deps = varDependenciesOfAtm maximalCriterion var obs c deps
varDependenciesOf maximalCriterion var obs c@(ReadFromChannel x ch)   deps = varDependenciesOfAtm maximalCriterion var obs c deps
varDependenciesOf maximalCriterion var obs c@(PrintToChannel  e ch)   deps = varDependenciesOfAtm maximalCriterion var obs c deps
varDependenciesOf maximalCriterion var obs c@(ClassifyGlobally x lvl) deps = varDependenciesOfAtm maximalCriterion var obs c deps
varDependenciesOf Discr            var obs (If b c1 c2) deps = do
    (_, deps1) <- varDependenciesOf Discr var obs c1 deps
    (_, deps2) <- varDependenciesOf Discr var obs c2 deps1
    return (Discr, deps2)
varDependenciesOf maximalCriterion var obs (If b c1 c2) deps = do
    let deps0 = cptE var b deps
    (criterion1, deps1) <- varDependenciesOf maximalCriterion var obs c1 deps0
    (criterion2, deps2) <- varDependenciesOf maximalCriterion var obs c2 deps1
    return (criterion1 ⊔ criterion2, deps2)


varDependenciesOf maximalCriterion var obs (Ch d c1 c2) deps = do
    (criterion1, deps1) <- varDependenciesOf maximalCriterion var obs c1 deps
    (criterion2, deps2) <- varDependenciesOf maximalCriterion var obs c2 deps1
    return (criterion1 ⊔ criterion2, deps2)


varDependenciesOf Discr            var obs   (ForV x d) deps = do
    (_, deps') <- varDependenciesOf Discr var obs d deps
    return (Discr, deps')
varDependenciesOf Siso             var obs   (ForV x d) deps = do
    let deps0 = cptE var ((Val 0) `Leq` (Var x)) deps
    (_, deps') <- varDependenciesOf Siso var obs d deps0
    return (Siso, deps')
varDependenciesOf _                var obs c@(ForV x d) deps =  disc ++ siso
  where disc = varDependenciesOf Discr var obs c deps
        siso = varDependenciesOf Siso  var obs c deps


varDependenciesOf Discr            var obs   (While e d) deps = do
    (_, deps') <- varDependenciesOf Discr var obs d deps
    return (Discr, deps')
varDependenciesOf Siso             var obs   (While e d) deps = do
    let deps0 = cptE var e deps
    (_, deps') <- varDependenciesOf Siso var obs d deps0
    return (Siso, deps')
varDependenciesOf _                var obs c@(While e d) deps =  disc ++ siso
  where disc = varDependenciesOf Discr var obs c deps
        siso = varDependenciesOf Siso  var obs c deps



varDependenciesOf Discr            var obs (ForC _ d) deps = do
    (_, deps') <- varDependenciesOf Discr var obs d deps
    return (Discr, deps')
varDependenciesOf Siso             var obs (ForC _ d) deps = do
    (_, deps') <- varDependenciesOf Siso var obs d deps
    return (Siso, deps')
varDependenciesOf maximalCriterion var obs (ForC _ d) deps = left ++ right
  where left = do
                  (_, deps') <- varDependenciesOf Siso  var obs d deps
                  return (Siso, deps')
        right = do
                  (_, deps') <- varDependenciesOf Discr var obs d deps
                  return (Siso, deps')


varDependenciesOf Discr            var obs (Seq c1 c2) deps = do
    (_, deps1) <- varDependenciesOf Discr var obs c1 deps
    (_, deps2) <- varDependenciesOf Discr var obs c2 deps1
    return (Discr, deps2)
varDependenciesOf Siso             var obs (Seq c1 c2) deps = do
    (_, deps1) <- varDependenciesOf Siso var obs c1 deps
    (_, deps2) <- varDependenciesOf Siso var obs c2 deps1
    return (Siso, deps2)
varDependenciesOf maximalCriterion var obs (Seq c1 c2) deps = left ++ right
  where left = do
                  (_, deps1)          <- varDependenciesOf Siso             var obs c1 deps
                  (criterion2, deps2) <- varDependenciesOf maximalCriterion var obs c2 deps1
                  return (Siso ⊔ criterion2 , deps2)
        right = do
                  (criterion1, deps1) <- varDependenciesOf maximalCriterion var obs c1 deps
                  (_, deps2)          <- varDependenciesOf Discr            var obs c2 deps1
                  return (criterion1 ⊔ Discr, deps2)

varDependenciesOf maximalCriterion var obs (Par cs) deps = do
    (criterion', deps') <- foldM f (Impossible,deps) cs
    return (criterion', deps')
  where f (criterion, deps) c = do
          (criterion', deps') <- varDependenciesOf maximalCriterion var obs c deps
          return (criterion ⊔ criterion', deps')


varDependenciesOf Siso               var obs (ParT cs) deps = []
varDependenciesOf None               var obs (ParT cs) deps = varDependenciesOf ZeroOneBisimilarity var obs (ParT cs) deps
varDependenciesOf StrongBisimilarity var obs (ParT cs) deps = varDependenciesOf Discr var obs (ParT cs) deps
varDependenciesOf maximalCriterion   var obs (ParT cs) deps = do
    (criterion', deps') <- foldM f (Impossible, deps) cs
--    traceShow (maximalCriterion, criterion') $
    id $ 
      if (criterion' ⊑ Discr) then
        return (Discr, deps')
      else if (criterion' ⊑ ZeroOneBisimilarity  ∧  ZeroOneBisimilarity ⊑  maximalCriterion) then
        return (ZeroOneBisimilarity, deps')
      else mzero
  where f (criterion, deps) c = do
          (criterion', deps') <- varDependenciesOf None var obs c deps
          return (criterion ⊔ criterion', deps')

