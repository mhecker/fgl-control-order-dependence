{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Program.Typing.FlexibleSchedulerIndependent where

import Algebra.Lattice

import Unicode
import Util

-- import Program
import Program.For


import IRLSOD


import Control.Monad.State.Lazy

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.DFS(topsort, scc)
import Data.Graph.Inductive.Query.TransClos


type VarTyping  = Var ->  SecurityLattice
type ChannelTyping = Channel -> (SecurityLattice, SecurityLattice)
type ExpBTyping = BoolFunction -> SecurityLattice
type ExpVTyping = VarFunction -> SecurityLattice






example0 :: Program
example0 = Map.fromList $ [
  (1, Ass "x" (Val 1))
 ]
var0 "x" = High
main0 = 1

example1 :: Program
example1 = Map.fromList $ [
  (1, Ass "x" (Val 1))
 ]
var1 "x" = Low
main1 = 1

example2 :: Program
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




-- exampleStock :: (Program, VarTyping, ThreadId)
(exampleStock, varStock, mainStock) = (
    Map.fromList $ [
       (initialThread,
          Ass networkOut (Val 0)                 `Seq`
          Ass stockPrices (Var networkIn)        `Seq`
          SpawnThread writeStockPricesToDatabase `Seq`
          Ass networkOut (Val 0)                 `Seq`
          Ass fundPrices (Var networkIn)         `Seq`
          SpawnThread writeFundPricesToDatabase  `Seq`
          SpawnThread computeAccountOverview
       ),
       (writeStockPricesToDatabase,
          Ass i (Val 0)                                                                 `Seq`
          ForV stockPrices (
              Ass database (((Var database) `Plus` (Var stockPrices)) `Plus` (Var i))
          )                                                                             `Seq`
          Ass i ((Var i) `Plus` (Val 1))
       ),
       (writeFundPricesToDatabase,
          Ass i (Val 0)                                                                 `Seq`
          ForV fundPrices (
              Ass database (((Var database) `Plus` (Var fundPrices)) `Plus` (Var i))
          )                                                                             `Seq`
          Ass j ((Var j) `Plus` (Val 1))
       ),
       (computeAccountOverview,
          Ass k (Val 0)                                                                 `Seq`
          Ass overview (Val 0)                                                          `Seq`
          ForV userPortfolio (
             Ass title ((Var userPortfolio) `Plus` (Var k))                             `Seq`
             If ((Var title) `Leq` (Val 42)) (
                 Ass price ((Var stockPrices) `Plus`
                            (Var title) `Plus`
                            (Var userPortfolio) `Plus`
                            (Var k)
                           )
                 ) (
                 Ass price ((Var fundPrices) `Plus`
                            (Var title) `Plus`
                            (Var userPortfolio) `Plus`
                            (Var k)
                           )
                 )                                                                      `Seq`
             Ass oldPrice ((Var database) `Plus` (Var title))                           `Seq`
             If ((Var oldPrice) `Leq` (Var price)) (
                 Ass tendency (Val 17)
                ) (
                 Ass tendency (Val 42)
                )                                                                       `Seq`
             Ass overview  ((Var overview) `Plus`
                            (Var title) `Plus`
                            (Var price) `Plus`
                            (Var tendency)
                           )                                                            `Seq`
             Ass k ((Var k) `Plus` (Val 1))
         )
       )
    ],
    var,
    initialThread
 )
    where networkOut  = "networkOut"
          networkIn   = "networkIn"
          stockPrices = "stockPrices"
          fundPrices  = "fundPrices"
          i           = "i"
          j           = "j"
          database    = "database"
          k           = "k"
          overview    = "overview"
          title       = "title"
          price       = "price"
          oldPrice    = "oldPrice"
          tendency    = "tendency"
          userPortfolio = "userPortfolio"
          var x
           | x == networkOut  = Low
           | x == networkIn   = Low
           | x == stockPrices = Low
           | x == fundPrices  = Low
           | x == i           = Low
           | x == j           = Low
           | x == database    = Low
           | x == k           = High
           | x == overview    = High
           | x == title       = High
           | x == price       = High
           | x == oldPrice    = High
           | x == tendency    = High
           | x == userPortfolio = High
          initialThread = 1
          writeStockPricesToDatabase = 2
          writeFundPricesToDatabase = 3
          computeAccountOverview = 4

expBTypingFrom :: VarTyping -> ExpBTyping
expBTypingFrom var e = (∐) [ var v | v <- Set.toList $ useB e]

expVTypingFrom :: VarTyping -> ExpVTyping
expVTypingFrom var e = (∐) [ var v | v <- Set.toList $ useV e]

data ProgramTyping = ProgramTyping {
 pc  :: SecurityLattice,
 stp :: SecurityLattice
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
nLevel Low = nLow
nLevel High = nHigh

type Program = Map ThreadId For
type ThreadId = Integer
principalTypingOf ::  VarTyping -> Program -> ThreadId -> Fresh (Maybe ProgramTyping)
--principalTypingOf :: VarTyping -> For -> Fresh (Maybe ProgramTyping, Gr () ())
principalTypingOf var p θ =
 do  nPc  <- freshVar
     nStp <- freshVar

     let initial' = insNodes [ (n,()) | n <- [nPc, nStp] ] initial
     varDependencies :: Gr () () <- (varDependenciesOf nPc nStp var p (p ! θ) initial')

     let deps = trc varDependencies
     let sccs = scc varDependencies
     let sccOf node = the (node ∊) $ sccs
     let solvable = all (\component -> not $ (nHigh ∈ component ∧ nLow ∈ component)) sccs

     if (solvable) then return $
--      (
       Just $ ProgramTyping {
          pc =      if (      nHigh ∊ pre deps nPc ) then High
               else if (      nPc   ∊ pre deps nLow) then Low
               else if (not $ nPc   ∊ pre deps nStp) then High
               else                                            Low,
          stp =     if (      nHigh ∊ pre deps nStp) then High
               else if (      nStp  ∊ pre deps nLow) then Low
               else Low
         }
--       , varDependencies )
--      else return (Nothing, varDependencies)
      else return Nothing
 where initial = mkGraph [(nLow,()), (nHigh,())] [(nLow,nHigh,())]

varDependenciesOf :: LevelVariable -> LevelVariable -> VarTyping -> Program -> For ->  Gr () () -> Fresh (Gr () ())
varDependenciesOf nPc nL var p (Skip)    deps =
    return deps
varDependenciesOf nPc nStpJoinTau var p (If b c1 c2) deps = do
    nStp <- freshVar
    let deps' = insNodes [ (n,()) | n <- [nStp] ] deps

    deps1 <- varDependenciesOf nPc nStp  var p c1 deps'
    deps2 <- varDependenciesOf nPc nStp  var p c2 deps1
    return $ insEdge (nLevel $ (expBTypingFrom var $ b),  nPc,                            ())
           $ insEdge (nStp,                               nStpJoinTau,                        ())
           $ insEdge (nLevel $ (expBTypingFrom var $ b),  nStpJoinTau,                        ())
           $ deps2
varDependenciesOf nPc nStpJoinTau var p (ForV x c) deps = do
    nStp <- freshVar
    let deps' = insNodes [ (n,()) | n <- [nStp] ] deps
    let nTau = nLevel $ var x
    deps'' <- varDependenciesOf nPc nStp var p c deps'
    return $ insEdge (nStp,                               nPc,                             ())
           $ insEdge (nTau,                               nPc,                             ())
           $ insEdge (nStp,                               nStpJoinTau,                     ())
           $ insEdge (nTau,                               nStpJoinTau,                     ())
           $ deps''
varDependenciesOf nPc nStpJoinTau var p (ForC _ c) deps = do
    nStp <- freshVar
    let deps' = insNodes [ (n,()) | n <- [nStp] ] deps
    let nTau = nLevel $ Low
    deps'' <- varDependenciesOf nPc nStp var p c deps'
    return $ insEdge (nStp,                               nPc,                             ())
           $ insEdge (nTau,                               nPc,                             ())
           $ insEdge (nStp,                               nStpJoinTau,                     ())
           $ insEdge (nTau,                               nStpJoinTau,                     ())
           $ deps''
varDependenciesOf nPc1MeetPc2 nStp1JoinStp2 var p (Seq c1 c2) deps = do
    nPc1  <- freshVar
    nStp1 <- freshVar
    let deps' = insNodes [ (n,()) | n <- [nPc1, nStp1] ] deps
    deps1 <- varDependenciesOf nPc1 nStp1 var p c1 deps'

    nPc2  <- freshVar
    nStp2 <- freshVar
    let deps1' = insNodes [ (n,()) | n <- [nPc2, nStp2] ] deps1
    deps2 <- varDependenciesOf nPc2 nStp2 var p c2 deps1'
    return $ insEdge (nStp1,                              nStp1JoinStp2,                  ())
           $ insEdge (nStp2,                              nStp1JoinStp2,                  ())
           $ insEdge (nPc1MeetPc2,                        nPc1,                            ())
           $ insEdge (nPc1MeetPc2,                        nPc2,                            ())
           $ insEdge (nStp1,                              nPc2,                           ())
           $ deps2


varDependenciesOf nPc nStp var p (Ass x e) deps =
    return $ insEdge (nPc,                               nLevel $ var x,                   ())
           $ insEdge (nLevel $ (expVTypingFrom var $ e), nLevel $ var x,                   ())
           $ insEdge (nLevel $ Low,                      nStp,                             ())
             deps


varDependenciesOf nPc nStp var p (SpawnThread θ) deps = do
    nStp1 <- freshVar
    let deps' = insNodes [ (n,()) | n <- [nStp1] ] deps
    deps1 <- varDependenciesOf nPc nStp1 var p c1 deps'
    return $ insEdge (nLevel $ Low,                      nStp,                             ())
             deps1
  where c1 = (p ! θ)


