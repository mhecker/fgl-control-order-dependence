module Data.Graph.Inductive.Query.Dependence where

data Dependence = ControlDependence | DataDependence | SpawnDependence | InterThreadDependence deriving (Show, Eq, Enum, Ord, Bounded)
