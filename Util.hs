module Util where

import Data.List (find)
import Data.Maybe (fromJust)

the p = fromJust . find p 


