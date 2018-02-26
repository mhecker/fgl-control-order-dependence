module Data.Graph.Inductive.Query.Dependence where

import IRLSOD

import Data.Graph.Inductive

data Dependence = ControlDependence | DataDependence | SummaryDependence | SpawnDependence | CallDependence | InterThreadDependence | ParameterInDependence | ParameterOutDependence deriving (Show, Eq, Enum, Ord, Bounded)

data SDGNode = CFGNode CFGNode
             | FormalIn Var
             | FormalOut Var
             | ActualIn Var Node  -- var, callSite
             | ActualOut Var Node -- car, callSite
             | Dummy
  deriving (Show, Eq, Ord)
