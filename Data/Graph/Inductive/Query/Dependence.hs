module Data.Graph.Inductive.Query.Dependence where

import IRLSOD

import Data.Graph.Inductive

data Dependence = ControlDependence | DataDependence | SummaryDependence | SpawnDependence | CallDependence | InterThreadDependence | ParameterInDependence | ParameterOutDependence | SpawnInDepdendence deriving (Show, Eq, Enum, Ord, Bounded)


data Independence = DataIndependence deriving (Show, Eq, Enum, Ord, Bounded)



data SDGNode = CFGNode CFGNode
             | FormalIn Var
             | FormalOut Var
             | ActualIn Var (Node, Node)  -- var, callSite == (call, return)
             | ActualOut Var (Node, Node) -- car, callSite == (call, return)
             | SpawnIn Var Node           -- var, spawnSite == spawnNode
             | Dummy
  deriving (Show, Eq, Ord)
