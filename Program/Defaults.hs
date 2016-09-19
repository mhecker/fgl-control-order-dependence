module Program.Defaults where

import IRLSOD

import Data.Map ( Map, (!) )
import qualified Data.Map as Map

import Unicode

import Data.Graph.Inductive


defaultInput  = Map.fromList [ (stdIn, cycle [ 2, 4, 6, 8]), (lowIn1, cycle [1,2,3,4]), (lowIn2, cycle [4,3,2,1]) ]
defaultInput' = Map.fromList [ (stdIn, cycle [-8,-6,-4,-2]), (lowIn1, cycle [1,2,3,4]), (lowIn2, cycle [4,3,2,1]) ]


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
defaultObservabilityMap gr = \n -> obsmap ! n where
 obsmap = Map.fromList $ [ (n, defaultObservability gr n) | n <- nodes gr ]
 defaultObservability gr n
   | levels == [] = Nothing
   | otherwise    = Just $ (∐) levels
  where levels = [ level | (n',e) <- lsuc gr n, Just level <- [obs (n',e)]]
        obs (n',Print _ channel) = Just $ defaultChannelObservability channel
        obs (n',Read  _ channel) = Just $ defaultChannelObservability channel
        obs _                    = Nothing

