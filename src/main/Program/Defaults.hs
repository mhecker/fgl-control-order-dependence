module Program.Defaults where

import IRLSOD

import Data.Map ( Map, (!) )
import qualified Data.Map as Map

import Unicode

import Data.Graph.Inductive

defaultInput :: Map String [Val]
defaultInput  = Map.fromList [ (stdIn, cycle [ 2, 1]), (lowIn1, cycle [1,2,3,4]), (lowIn2, cycle [4,3,2,1]) ]

defaultInput' :: Map String [Val]
defaultInput' = Map.fromList [ (stdIn, cycle [-1, 0]), (lowIn1, cycle [1,2,3,4]), (lowIn2, cycle [4,3,2,1]) ]


defaultChannelObservability channel
 | channel == stdIn     = High
 | channel == stdIn2    = High
 | channel == lowIn1 = Low
 | channel == lowIn2 = Low
 | channel == stdOut = Low
 | channel == highOut1 = High
 | channel == highOut2 = High
 | otherwise = error $ "unknown channel: " ++ channel


defaultObservabilityMap :: Graph gr => gr CFGNode CFGEdge -> ObservationalSpecification
defaultObservabilityMap gr = \n -> Map.lookup n obsmap where
 obsmap = Map.fromList $ [ (n, l) | n <- nodes gr, Just l <- [defaultObservability gr n] ]
 defaultObservability gr n
   | levels == [] = Nothing
   | otherwise    = Just $ (∐) levels
  where levels = [ level | (_,e) <- lsuc gr n, Just level <- [obs e]]
        obs (Print _ channel) = Just $ defaultChannelObservability channel
        obs (Read  _ channel) = Just $ defaultChannelObservability channel
        obs _                 = Nothing

