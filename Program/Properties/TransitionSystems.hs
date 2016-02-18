{-# LANGUAGE ScopedTypeVariables #-}
module Program.Properties.TransitionSystems where

import Algebra.Lattice
import Unicode

import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Test.QuickCheck (quickCheck, verboseCheck)

import Data.List
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Data.Graph.Inductive.PatriciaTree (Gr)

--import Program.For
import IRLSOD (lowIn1, stdIn, stdOut, VarFunction(..), Var)

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

secureProps = testGroup "(concerning equivalence of security properties for single-threaded programs in terms of transition systems)" [
    testProperty  "securePDG == secureSymbolic"
                  securePDGIsSecureSymbolic
  ]




secureTwoValueIsSecureSymbolic :: SimpleProgram -> Bool
secureTwoValueIsSecureSymbolic simple =
       secureSymbolic       low high p
    ↔ secureTwoValueDefUse low p
  where p        = toProgramSimple simple :: Program Gr
        low  = Set.fromList ["x", "y", "z"] ∩ vars p
        high = Set.fromList ["a", "b", "c"] ∩ vars p


secureTwoValueIsSecureOneValue :: SimpleProgram -> Bool
secureTwoValueIsSecureOneValue simple =
       secureTwoValueDefUse low p
    ↔ secureOneValueDefUse low p
  where p        = toProgramSimple simple :: Program Gr
        low = Set.fromList ["x", "y", "z"] ∩ vars p



securePDGIsSecureOneValue :: SimpleProgram -> Bool
securePDGIsSecureOneValue simple =
       securePDG (vars p) low high simple
    ↔ secureOneValueDefUse low p
  where p        = toProgramSimple simple  :: Program Gr
        low      = Set.fromList ["x", "y", "z"] ∩ vars p
        high     = Set.fromList ["a", "b", "c"] ∩ vars p


securePDGIsSecureSymbolic :: SimpleProgram -> Bool
securePDGIsSecureSymbolic simple =
       securePDG (vars p) low high simple
    ↔ secureSymbolic low high p
  where p        = toProgramSimple simple  :: Program Gr
        low      = Set.fromList ["x", "y", "z"] ∩ vars p
        high     = Set.fromList ["a", "b", "c"] ∩ vars p
