-- Initial irlsod.cabal generated by cabal init.  For further 
-- documentation, see http://haskell.org/cabal/users-guide/

-- The name of the package.
name:                fgl-control-order-dependence

-- The package version.  See the Haskell package versioning policy (PVP) 
-- for standards guiding when and how versions should be incremented.
-- https://wiki.haskell.org/Package_versioning_policy
-- PVP summary:      +-+------- breaking API changes
--                   | | +----- non-breaking API additions
--                   | | | +--- code changes with no API change
version:             0.1.0.0

-- A short (one-line) description of the package.
synopsis:            Algrithms for Control- and Order-Dependence

-- A longer description of the package.
-- description:         

-- URL for the project homepage or repository.
homepage:            https://pp.ipd.kit.edu/projects/joana/

-- The license under which the package is released.
license:             LGPL-3

-- The file containing the license text.
license-file:        LICENSE

-- The package author(s).
author:              Martin Hecker

-- An email address to which users can send suggestions, bug reports, and 
-- patches.
maintainer:          martin.hecker@kit.edu

-- A copyright notice.
-- copyright:           

category:            Development

build-type:          Simple

-- Extra files to be distributed with the package, such as examples or a 
-- README.
extra-source-files:  ChangeLog.md

-- Constraint on the version of Cabal needed to build this package.
cabal-version:       >=1.10

define(COMMON_EXTENSIONS, `RankNTypes, CPP, ScopedTypeVariables, FlexibleInstances, NamedFieldPuns, GeneralizedNewtypeDeriving')dnl
define(COMMON_GHC_FLAGS, `-O2 -rtsopts -threaded')dnl

define(COMMON_DEPENDENCIES, `process >= 1.2.3 && < 1.4, base >=4.8 && <4.10, deepseq, base-unicode-symbols >=0.2 && <0.3, containers >=0.5 && <0.6, fgl >=5.5 && <5.6, fgl-arbitrary == 0.2.0.3, fgl-visualize >= 0.1.0.1 && < 0.2, QuickCheck >=2.8 && <2.9, logict >=0.6 && <0.7, random >=1.1 && <1.2, MonadRandom == 0.5.1, containers-unicode-symbols == 0.3.1.1, lattices == 1.5.0, dequeue == 0.1.12, bitwise == 0.1.1.1')dnl
define(MAIN_DEPENDENCIES, `mtl >= 2.2, template-haskell >= 2.10, array >= 0.5, data-default-instances-containers >= 0.0.1 && < 0.2, monad-gen == 0.3.0.1, pqueue >= 1.3.2 && < 1.5, time >= 1.5 && < 1.6, statistics, vector, safe')dnl
define(TEST_DEPENDENCIES, `fgl-control-order-dependence, tasty >=0.11 && <0.12, tasty-quickcheck >=0.8 && <0.9, tasty-hunit >=0.9 && <0.10, tasty-ant-xml >= 1.0.5 && < 1.2')dnl

library
  hs-source-dirs: src/main/
  exposed-modules:
    IRLSOD
    Unicode
    NNGraph
    Statistics
    Program.Examples
    Program.Analysis
    Program.DynamicAnalysis
    Program.Generator
    -- Program.Tests
    Program.MultiThread
    Program.Properties.Analysis
    -- Program.Properties.TimingDependence
    -- Program.Properties.TransitionSystems
    Program.Properties.NameOfFunction
    -- Program.Properties.Properties
    Program.Properties.CDom
    Program.Typing.ResumptionBasedSecurity
    Program.Typing.FlexibleSchedulerIndependentChannels
    -- Program.Typing.ImprovedTypingsSmith
    -- Program.Typing.FlexibleSchedulerIndependent
    Program.CDom
    Program.MHP
    Program.TransitionSystem
    Program.Defaults
    Program.For
    Execution
    PNI
    Program
    ListUnicode
    ExecutionTree
    Util
    Data.Graph.Inductive.Arbitrary.Reducible
    Data.Graph.Inductive.FA
    Data.Graph.Inductive.Query.DataDependence
    Data.Graph.Inductive.Query.InterThreadDependence
    Data.Graph.Inductive.Query.TSCD
    -- Data.Graph.Inductive.Query.ControlDependenceTests
    Data.Graph.Inductive.Query.OrderDependence.Unused
    Data.Graph.Inductive.Query.InfiniteDelay
    Data.Graph.Inductive.Query.PureTimingDependence
    Data.Graph.Inductive.Query.TimingDependence
    Data.Graph.Inductive.Query.ControlDependence
    Data.Graph.Inductive.Query.LCA
    Data.Graph.Inductive.Query.OrderDependence
    Data.Graph.Inductive.Query.NTIODSlice
    Data.Graph.Inductive.Query.PathsBetween
    Data.Graph.Inductive.Query.PostDominanceFrontiers
    Data.Graph.Inductive.Query.BalancedSCC
    Data.Graph.Inductive.Query.DataConflict
    Data.Graph.Inductive.Query.NTICD
    Data.Graph.Inductive.Query.ProgramDependence
    Data.Graph.Inductive.Query.Dependence
    Data.Graph.Inductive.Query.Dataflow
    Data.Graph.Inductive.Query.Util.GraphTransformations
    Data.Graph.Inductive.Query.FCACD
    Data.Graph.Inductive.Query.NTICDUnused
    Data.Graph.Inductive.Query.PostDominance.GraphTransformations
    Data.Graph.Inductive.Query.PostDominance.Numbered
    Data.Graph.Inductive.Query.Slices.GraphTransformations
    Data.Graph.Inductive.Query.Slices.OrderDependence
    Data.Graph.Inductive.Query.Slices.CEdges
    Data.Graph.Inductive.Query.Slices.PostDominanceFrontiers
    Data.Graph.Inductive.Query.Slices.NTICD
    Data.Graph.Inductive.Query.Slices.PostDominance
    Data.Graph.Inductive.Query.PostDominance
    Data.Graph.Inductive.Query.PostDominanceFrontiers.CEdges
    Data.Graph.Inductive.Query.PostDominanceFrontiers.Numbered
    Data.Graph.Inductive.Query.NTICD.SNM
    Data.Graph.Inductive.Query.NTICD.GraphTransformations
    Data.Graph.Inductive.Query.NTICD.Program
    Data.Graph.Inductive.Query.NTICD.Util
    Data.Graph.Inductive.Util
    Data.Dequeue.SimpleDequeue
    Data.Util
  
  build-depends:       COMMON_DEPENDENCIES, MAIN_DEPENDENCIES
  
  ghc-options:         COMMON_GHC_FLAGS
  
  default-language:    Haskell2010


executable tests.bin
  hs-source-dirs: src/test/
  main-is:             Program/Tests.hs
  ghc-options:         COMMON_GHC_FLAGS -main-is Program.Tests.main
  build-depends:       COMMON_DEPENDENCIES, MAIN_DEPENDENCIES, TEST_DEPENDENCIES
  other-extensions:    COMMON_EXTENSIONS
  default-language:    Haskell2010


executable sas-props.bin
  hs-source-dirs: src/test/
  main-is:             Program/Properties/SASProperties.hs
  ghc-options:         COMMON_GHC_FLAGS -main-is Program.Properties.SASProperties.props
  build-depends:       COMMON_DEPENDENCIES, TEST_DEPENDENCIES
  other-extensions:    COMMON_EXTENSIONS
  default-language:    Haskell2010
  
executable sas-tests.bin
  hs-source-dirs: src/test/
  main-is:             Program/Properties/SASProperties.hs
  ghc-options:         COMMON_GHC_FLAGS -main-is Program.Properties.SASProperties.tests
  build-depends:       COMMON_DEPENDENCIES, TEST_DEPENDENCIES
  other-extensions:    COMMON_EXTENSIONS
  default-language:    Haskell2010
  

define(VALID,`
executable $1.valid.bin
  hs-source-dirs: src/test/
  main-is:             Program/Properties/ValidProperties.hs
  ghc-options:         COMMON_GHC_FLAGS -main-is Program.Properties.ValidProperties.$1
  build-depends:       COMMON_DEPENDENCIES, TEST_DEPENDENCIES
  other-extensions:    COMMON_EXTENSIONS
  default-language:    Haskell2010

executable $1.valid.xml.bin
  hs-source-dirs: src/test/
  main-is:             Program/Properties/ValidProperties.hs
  ghc-options:         COMMON_GHC_FLAGS -main-is Program.Properties.ValidProperties.$1X
  build-depends:       COMMON_DEPENDENCIES, TEST_DEPENDENCIES
  other-extensions:    COMMON_EXTENSIONS
  default-language:    Haskell2010
')dnl

VALID(all)
VALID(cdom)
VALID(balanced)
VALID(timing)
VALID(timingDep)
VALID(simon)
VALID(giffhorn)
VALID(soundness)
VALID(preccex)
VALID(nticd)
VALID(ntscd)
VALID(newcd)
VALID(dod)
VALID(wod)
VALID(color)
VALID(reducible)
VALID(indeps)
VALID(delay)
VALID(insensitiveDom)
VALID(sensitiveDom)
VALID(misc)

define(EXPECTED_FAILURE_DEPENDENCY, `tasty-expected-failure >= 0.11 && < 0.12')

define(INVALID,`
executable $1.invalid.bin
  hs-source-dirs: src/test/
  main-is:             Program/Properties/InvalidProperties.hs
  ghc-options:         COMMON_GHC_FLAGS -main-is Program.Properties.InvalidProperties.$1
  build-depends:       COMMON_DEPENDENCIES, TEST_DEPENDENCIES, EXPECTED_FAILURE_DEPENDENCY
  other-extensions:    COMMON_EXTENSIONS
  default-language:    Haskell2010

executable $1.invalid.xml.bin
  hs-source-dirs: src/test/
  main-is:             Program/Properties/InvalidProperties.hs
  ghc-options:         COMMON_GHC_FLAGS -main-is Program.Properties.InvalidProperties.$1X
  build-depends:       COMMON_DEPENDENCIES, TEST_DEPENDENCIES, EXPECTED_FAILURE_DEPENDENCY
  other-extensions:    COMMON_EXTENSIONS
  default-language:    Haskell2010
')dnl

INVALID(all)
INVALID(cdom)
INVALID(balanced)
INVALID(timing)
INVALID(timingDep)
INVALID(giffhorn)
INVALID(soundness)
INVALID(preccex)
INVALID(nticd)
INVALID(ntscd)
INVALID(newcd)
INVALID(dod)
INVALID(wod)
INVALID(insensitiveDom)
INVALID(sensitiveDom)
INVALID(misc)
INVALID(long)