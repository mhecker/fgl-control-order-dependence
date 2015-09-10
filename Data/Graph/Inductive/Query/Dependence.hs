module Data.Graph.Inductive.Query.Dependence where

data Dependence = ControlDependence | DataDependence deriving (Show, Eq, Enum, Ord, Bounded)
