module Data.Graph.Inductive.Query.Dependence where

import IRLSOD

data Dependence = ControlDependence | DataDependence | SpawnDependence | InterThreadDependence | ParameterInDependence | ParameterOutDependence deriving (Show, Eq, Enum, Ord, Bounded)

data SDGNode = CFGNode CFGNode
             | FormalIn Var
             | FormalOut Var
             | ActualIn Var
             | ActualOut Var
             | Dummy
  deriving (Show, Eq, Ord)
