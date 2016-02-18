{-# LANGUAGE ScopedTypeVariables #-}
module Program.Properties.TransitionSystems where

import Algebra.Lattice
import Unicode

import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Test.QuickCheck (quickCheck)

import Data.List
import Data.Ord
import qualified Data.Set as Set
import qualified Data.Map as Map

import Data.Graph.Inductive.PatriciaTree (Gr)

import Program.For
import IRLSOD (lowIn1, stdIn, stdOut, VarFunction(..))

import Program (Program, vars)
import Program.Properties.Analysis
import Program.Examples (testsuite, ijisLSODistkaputt)
import Program.Analysis
import Program.Generator (toProgram, toProgramSimple, SimpleProgram(..), GeneratedProgram(..), Generated(..))
import Program.TransitionSystem

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [properties]

properties :: TestTree
properties = testGroup "Properties" [ secureProps]

secureProps = testGroup "(concerning equivalence of security properties in terms of transition systems)" [
    testProperty  "timingClassificationDomPaths == timingClassification"
                  timingDDomPathsIsTiming,
    testProperty  "timingClassificationDomPaths is at least as precise as timingClassificationSimple"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureTimingClassificationSimple,
    testProperty  "timingClassificationDomPaths is at least as precise as minimalClassification"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` isSecureMinimalClassification,
    testProperty  "timingClassificationDomPaths is at least as precise as giffhornLSOD"
                $ isSecureTimingClassificationDomPaths `isAtLeastAsPreciseAs` giffhornLSOD
  ]




secureTwoValueIsSecureSymbolic :: SimpleProgram -> Bool
secureTwoValueIsSecureSymbolic simple =
       secureSymbolic       low p
    ↔ secureTwoValueDefUse low p
  where p        = toProgramSimple simple :: Program Gr
        low = Set.fromList ["x", "y", "z"] ∩ vars p


secureTwoValueIsSecureOneValue :: SimpleProgram -> Bool
secureTwoValueIsSecureOneValue simple =
       secureTwoValueDefUse low p
    ↔ secureOneValueDefUse low p
  where p        = toProgramSimple simple :: Program Gr
        low = Set.fromList ["x", "y", "z"] ∩ vars p


securePDGIsSecureOneValue :: SimpleProgram -> Bool
securePDGIsSecureOneValue simple =
       isSecureTimingClassificationDomPaths p'
    ↔ secureOneValueDefUse low p
  where p        = toProgramSimple simple  :: Program Gr
        p'       = toProgram       simple' :: Program Gr
        low = Set.fromList ["x", "y", "z"] ∩ vars p

        simple' = let (SimpleProgram threads) = simple
                      (Generated for _ _)     = (Map.!) threads 1
                      prefix  = foldl Seq Skip $ [ReadFromChannel var       lowIn1 | var <- Set.toList $ low ] ++
                                                 [ReadFromChannel var       stdIn  | var <- Set.toList $ vars p ∖ low]
                      postfix = foldr Seq Skip   [PrintToChannel  (Var var) stdOut | var <- Set.toList $ low ]
                      for'    = prefix `Seq` for `Seq` postfix
                  in  (GeneratedProgram (Map.fromList [(1, Generated for' undefined undefined)]))
