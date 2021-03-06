{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.Slices.GraphTransformations where


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Graph.Inductive


import Unicode
import Util(fromSet, invert'')

import Data.Graph.Inductive.Util (withUniqueEndNodeAndEscapeNodes)
import Data.Graph.Inductive.Query.Util.GraphTransformations (choiceAtRepresentativesGraphOf, splitRepresentativesGraphOf, splitRepresentativesGraphNoTrivialOf)
import Data.Graph.Inductive.Query.NTICD.Util (combinedBackwardSlice)
import Data.Graph.Inductive.Query.NTICD (nticdViaSinkDom, ntscdViaMDom)


nticdNTIODSliceViaEscapeNodes :: (DynGraph gr) => gr () () ->  Set Node -> Set Node
nticdNTIODSliceViaEscapeNodes g = \ms -> combinedBackwardSlice nticd' empty ms ∖ (Set.fromList (end:escape))
  where (end, escape, g') = withUniqueEndNodeAndEscapeNodes () () () () g
        nticd' = invert'' $ nticdViaSinkDom g'
        empty = Map.empty


nticdNTIODSliceViaChoiceAtRepresentatives :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODSliceViaChoiceAtRepresentatives g = \ms -> combinedBackwardSlice (nticd'') empty ms
  where -- g'  = foldr (flip delSuccessorEdges) g (Map.keys representants)
        g'' = choiceAtRepresentativesGraphOf g
        nticd'' = invert'' $ nticdViaSinkDom g''
        empty = Map.empty



nticdNTIODSliceViaCutAtRepresentatives :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODSliceViaCutAtRepresentatives g = \ms -> combinedBackwardSlice (nticd ⊔ nticd'') empty ms
  where -- g'  = foldr (flip delSuccessorEdges) g (Map.keys representants)
        g'' = splitRepresentativesGraphOf g
        nticd   = invert'' $ nticdViaSinkDom g
        nticd'' = invert'' $ nticdViaSinkDom g''
        empty = Map.empty

nticdNTIODSliceViaCutAtRepresentativesNoTrivial :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
nticdNTIODSliceViaCutAtRepresentativesNoTrivial g = \ms -> combinedBackwardSlice (nticd ⊔ nticd'') empty ms
  where -- g'  = foldr (flip delSuccessorEdges) g (Map.keys representants)
        g'' = splitRepresentativesGraphNoTrivialOf g
        nticd   = invert'' $ nticdViaSinkDom g
        nticd'' = invert'' $ nticdViaSinkDom g''
        empty = Map.empty


ntscdNTSODSliceViaCutAtRepresentatives :: forall gr a b . (DynGraph gr) => gr a b ->  Set Node -> Set Node
ntscdNTSODSliceViaCutAtRepresentatives g = \ms -> combinedBackwardSlice (ntscd ⊔ ntscd'') empty ms
  where g'' = splitRepresentativesGraphOf g
        ntscd   = invert'' $ ntscdViaMDom g
        ntscd'' = invert'' $ ntscdViaMDom g''
        empty = Map.empty
