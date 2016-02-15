module Util where

import Data.List (find)
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Unicode

the p = fromJust . find p 



chooseOneEach :: [(a,[b])] -> [[(a,b)]]
chooseOneEach choices = fmap (zip as) $ sequence bss
  where as  = fmap fst choices
        bss = fmap snd choices

restrict σ vars = Map.filterWithKey (\var _ -> var ∈ vars) σ
