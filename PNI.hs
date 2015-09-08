module PNI where


import IRLSOD
import Unicode

-- import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph

-- import Data.Map ( Map, (!) )
-- import qualified Data.Map as Map
-- import Data.Set (Set)
-- import qualified Data.Set as Set
-- import Data.Set.Unicode



-- [(Configuration, (Node,Event), Configuration)]
prob :: Graph gr => gr CFGNode CFGEdge -> ExecutionTrace -> Rational
prob gr [] = 1
prob gr (((control,σ,i), o, (control',σ',i')) : trace)
    | length successors /= length control = error "nicht genau ein nachfolgezustand pro thread"
    | otherwise                           = ( toRational (length $ filter (== (o,(control',σ'))) successors) /
                                              toRational (length successors) )
                                            * prob gr trace
  where successors = [(o,(control,σ)) | (o,(control,σ,i)) <- eventStep gr (control,σ,i)]
