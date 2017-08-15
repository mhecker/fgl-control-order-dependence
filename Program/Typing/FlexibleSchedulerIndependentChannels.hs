{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Program.Typing.FlexibleSchedulerIndependentChannels where

import Algebra.Lattice

import Unicode
import Util

-- import Program
import Program.For
import Program.Generator (GeneratedProgram(..), Generated(..), toCode)

import IRLSOD


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




-- exampleStock :: (ForProgram, VarTyping, ThreadId)
(exampleStock, varStock, obsStock, mainStock) = (
    Map.fromList $ [
       (initialThread,
          ReadFromChannel stockPrices networkIn  `Seq`
          SpawnThread writeStockPricesToDatabase `Seq`
          ReadFromChannel userPortfolio chUserPortfolio `Seq`
          ReadFromChannel fundPrices  networkIn  `Seq`
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
    obsStock,
    initialThread
 )
    where networkIn   = "networkIn"
          chUserPortfolio = "chUserPortFolio"
          obsStock ch
           | ch == networkIn = Low
           | ch == chUserPortfolio = High

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
 stp :: SecurityLattice,
 var :: Map Var SecurityLattice
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




data ForProgram = ForProgram {
  code :: Map ThreadId For,
  channelTyping :: ChannelTyping,
  mainThreadFor :: ThreadId
 }
type ThreadId = Integer


isSecureFlexibleSchedulerIndependentChannel :: GeneratedProgram -> Bool
isSecureFlexibleSchedulerIndependentChannel gen = isJust $ fst $ principalTypingOfGen gen


isSecureFlexibleSchedulerIndependentChannelFor ::  ForProgram -> Bool
isSecureFlexibleSchedulerIndependentChannelFor p = isJust $ fst $ evalFresh $ principalTypingOf p


principalTypingOfGen :: GeneratedProgram -> (Maybe ProgramTyping, Gr ConstraintNode ConstraintEdge)
principalTypingOfGen gen = evalFresh $ principalTypingOf (ForProgram { code = code, channelTyping = defaultChannelObservability, mainThreadFor = 1})
  where code = toCode gen


data Rule = FSIskip | FSIass | FSIif | FSIwhile | FSIspawn | FSIseq | FSIsub
          | FSIread | FSIprint
          deriving Show
data ConstraintNode = ConstLevel SecurityLattice | VarLevel Var | Other | AssAt [For] | StpAt [For] 
data ConstraintEdge = RuleApplication Rule | OtherE deriving Show

instance Show ConstraintNode where
    show (ConstLevel l) = "ConstLevel " ++ (show l)
    show (VarLevel v)   = "VarLevel " ++ (show v)
    show Other          = "Other"
    show (AssAt fors)   = "AssAt " ++ (concat $ intersperse ", " $ fmap showShallow fors)
    show (StpAt fors)   = "StpAt " ++ (concat $ intersperse ", " $ fmap showShallow fors)
    


showShallow (If bexp c1 c2) = "If " ++ (show bexp) ++ " _ _"
showShallow (Ass x exp)     = "Ass " ++ (show x) ++ " " ++ (show exp)
showShallow (ForC x c)      = "For " ++ (show x) ++ " _"
showShallow (ForV x c)      = "For " ++ (show x) ++ " _"
showShallow (Seq c1 c2)     = "Seq _ _"
showShallow (Skip)          = "Skip"
showShallow (ReadFromChannel x ch) = "ReadFromChannel " ++ (show x) ++ " " ++ (show ch)
showShallow (PrintToChannel e ch)  = "PrintToChannel " ++ (show e) ++ " " ++ (show ch)
showShallow (SpawnThread tid)      = "SpawnThread " ++ (show tid)

principalTypingOf ::  ForProgram ->  Fresh (Maybe ProgramTyping, Gr ConstraintNode ConstraintEdge)
principalTypingOf p@(ForProgram { code }) = principalTypingUsing initial var p
    where initial = mkGraph ([(nLow,ConstLevel Low), (nHigh,ConstLevel High)] ++ [ (n,VarLevel v) | (v,n) <- Map.assocs var ])
                            [(nLow,nHigh,OtherE)]
          var =  varsToLevelVariable code

varsToLevelVariable :: (Map ThreadId For) -> Map Var LevelVariable
varsToLevelVariable ps = Map.fromList [
    (x,n) | (x,n) <- zip (nub $ [ x | p <- Map.elems ps,
                                  x <- [ x | Ass  x' e            <- subCommands p, x <- [x'] ++ (Set.toList $ useV e)]
                                    ++ [ x | ForV x  _            <- subCommands p]
                                    ++ [ x | If e _ _             <- subCommands p, x <-         (Set.toList $ useB e)]
                                    ++ [ x | ReadFromChannel x _  <- subCommands p]
                                    ++ [ x | PrintToChannel  e _  <- subCommands p, x <-         (Set.toList $ useV e)]
                                ]
                          )
                          [nVarStart, nVarStart -1 ..]
  ]


--principalTypingUsing ::  Gr () () -> Map Var LevelVariable -> ForProgram -> Fresh (Maybe ProgramTyping)
principalTypingUsing :: Gr ConstraintNode ConstraintEdge -> Map Var LevelVariable -> ForProgram -> Fresh (Maybe ProgramTyping, Gr ConstraintNode ConstraintEdge)
principalTypingUsing initial var p@(ForProgram { code, channelTyping, mainThreadFor})  =
 do  nPc  <- freshVar
     nStp <- freshVar

     let initial' = insNodes [ (nPc, AssAt [code ! mainThreadFor]), (nStp, StpAt [code ! mainThreadFor]) ] initial
     varDependencies :: Gr ConstraintNode ConstraintEdge <- (varDependenciesOf nPc nStp var code channelTyping (code ! mainThreadFor) initial')

     let deps = trc varDependencies
     let sccs = scc varDependencies
     let sccOf node = the (node `elem`) $ sccs
     let solvable = all (\component -> not $ (nHigh ∈ component ∧ nLow ∈ component)) sccs

     if (solvable) then return $
      (
       Just $ ProgramTyping {
          pc =      if (      nHigh `elem` pre deps nPc ) then High
               else if (      nPc   `elem` pre deps nLow) then Low
               else if (not $ nPc   `elem` pre deps nStp) then High
               else                                            Low,
          stp =     if (      nHigh `elem` pre deps nStp) then High
               else if (      nStp  `elem` pre deps nLow) then Low
               else Low,
          var = Map.fromList [ (x, if (nHigh `elem` pre deps nX) then High else Low ) | (x,nX) <- Map.assocs var]
         }
       , varDependencies )
      else return (Nothing, varDependencies)
varDependenciesOf :: LevelVariable -> LevelVariable -> (Map Var LevelVariable) -> (Map ThreadId For) -> ChannelTyping -> For ->  Gr ConstraintNode ConstraintEdge -> Fresh (Gr ConstraintNode ConstraintEdge)
varDependenciesOf nPc nL var obs p (Skip)    deps =
    return deps
varDependenciesOf nPc nStpJoinTau var p obs (If b c1 c2) deps = do
    nStp <- freshVar
    let deps' = insNodes [ (n, StpAt [c1, c2]) | n <- [nStp] ] deps

    deps1 <- varDependenciesOf nPc nStp  var p obs c1 deps'
    deps2 <- varDependenciesOf nPc nStp  var p obs c2 deps1
    return $ insEdges [ (var ! x,                         nPc,                                RuleApplication FSIif) | x <- Set.toList $ useB b]
           $ insEdge (nStp,                               nStpJoinTau,                        RuleApplication FSIif)
           $ insEdges [ (var ! x,                         nStpJoinTau,                        RuleApplication FSIif) | x <- Set.toList $ useB b]
           $ deps2
varDependenciesOf nPc nStpJoinTau var p obs (ForV x c) deps = do
    nStp <- freshVar
    let deps' = insNodes [ (n, StpAt [c]) | n <- [nStp] ] deps
    let nTau = var ! x
    deps'' <- varDependenciesOf nPc nStp var p obs c deps'
    return $ insEdge (nStp,                               nPc,                             RuleApplication FSIwhile)
           $ insEdge (nTau,                               nPc,                             RuleApplication FSIwhile)
           $ insEdge (nStp,                               nStpJoinTau,                     RuleApplication FSIwhile)
           $ insEdge (nTau,                               nStpJoinTau,                     RuleApplication FSIwhile)
           $ deps''
varDependenciesOf nPc nStpJoinTau var p obs (ForC _ c) deps = do
    nStp <- freshVar
    let deps' = insNodes [ (n, StpAt [c]) | n <- [nStp] ] deps
    let nTau = nLevel $ Low
    deps'' <- varDependenciesOf nPc nStp var p obs c deps'
    return $ insEdge (nStp,                               nPc,                             RuleApplication FSIwhile)
           $ insEdge (nTau,                               nPc,                             RuleApplication FSIwhile)
           $ insEdge (nStp,                               nStpJoinTau,                     RuleApplication FSIwhile)
           $ insEdge (nTau,                               nStpJoinTau,                     RuleApplication FSIwhile)
           $ deps''
varDependenciesOf nPc1MeetPc2 nStp1JoinStp2 var p obs (Seq c1 c2) deps = do
    nPc1  <- freshVar
    nStp1 <- freshVar
    let deps' = insNodes [ (nPc1, AssAt [c1]), (nStp1, StpAt [c1]) ] deps
    deps1 <- varDependenciesOf nPc1 nStp1 var p obs c1 deps'

    nPc2  <- freshVar
    nStp2 <- freshVar
    let deps1' = insNodes [ (nPc2, AssAt [c2]), (nStp2, StpAt [c2]) ] deps1
    deps2 <- varDependenciesOf nPc2 nStp2 var p obs c2 deps1'
    return $ insEdge (nStp1,                              nStp1JoinStp2,                  RuleApplication FSIseq)
           $ insEdge (nStp2,                              nStp1JoinStp2,                  RuleApplication FSIseq)
           $ insEdge (nPc1MeetPc2,                        nPc1,                           RuleApplication FSIseq)
           $ insEdge (nPc1MeetPc2,                        nPc2,                           RuleApplication FSIseq)
           $ insEdge (nStp1,                              nPc2,                           RuleApplication FSIseq)
           $ deps2


varDependenciesOf nPc nStp var p obs (Ass x e) deps =
    return $ insEdge (nPc,                               var ! x,                          RuleApplication FSIass)
           $ insEdges [ (var ! x',                       var ! x,                          RuleApplication FSIass) | x' <- Set.toList $ useV e ]
           $ insEdge (nLevel $ Low,                      nStp,                             RuleApplication FSIass)
             deps


varDependenciesOf nPc nStp var p obs (ReadFromChannel x ch) deps =
    return $ insEdge (nPc,                               var ! x,                          RuleApplication FSIread)
           $ insEdge (nLevel $ obs ch,                   var ! x,                          RuleApplication FSIread)

           -- in the LSOD-Setting, a low read is always visible.
           -- Hence, in order to obtain "fair"(™) comparison,
           -- we demand that low read cannot be made invisible-in-the-RuleApplication FSI-sense by assigning to a high variable:
           $ insEdge (var ! x,                           nLevel $ obs ch,                  RuleApplication FSIread)

           $ insEdge (nLevel $ Low,                      nStp,                             RuleApplication FSIread)
             deps

varDependenciesOf nPc nStp var p obs (PrintToChannel  e ch) deps =
    return $ insEdges [ (var ! x,                        nLevel $ obs ch,                  RuleApplication FSIprint) | x <- Set.toList $ useV e ]

           -- in the LSOD-Setting, a low print is always visible.
           -- Hence, in order to obtain "fair"(™) comparison,
           -- we demand that low print is visible-in-the-RuleApplication FSI-sense by treating it like an assignment to a low variable:
           $ insEdge (nPc,                               nLevel $ obs ch,                   RuleApplication FSIprint)
             deps



varDependenciesOf nPc nStp var p obs (SpawnThread θ) deps = do
    nStp1 <- freshVar
    let deps' = insNodes [ (n, StpAt [c1]) | n <- [nStp1] ] deps
    deps1 <- varDependenciesOf nPc nStp1 var p obs c1 deps'
    return $ insEdge (nLevel $ Low,                      nStp,                             RuleApplication FSIspawn)
             deps1
  where c1 = (p ! θ)


