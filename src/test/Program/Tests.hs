{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Program.Tests where

import System.Process

import Data.Graph.Inductive.Dot

import Data.Word

import Data.List

import Data.Maybe (fromJust)

import qualified Data.Map.Ordered as OMap
import Data.Foldable (toList)

import qualified Data.Dequeue as Dequeue
import Data.Dequeue (pushBack, popFront)
import Data.Dequeue.SimpleDequeue (SimpleDequeue)

import System.IO.Unsafe(unsafePerformIO)
import GHC.IO.Handle.Types (Handle)
import Control.Monad.Random
import Control.Monad(forM_, when, forever, forM)

import Test.QuickCheck
import Test.QuickCheck.Random (mkQCGen)
import Test.QuickCheck.Gen (Gen(MkGen))


import Program.Typing.FlexibleSchedulerIndependentChannels
import qualified Program.Typing.ResumptionBasedSecurity as Res

import Program.For
import Program
import Program.Defaults
import Program.Examples
import Program.ExamplesCrypto
import ReferenceCrypto

import Program.MultiThread
import Program.MHP
import Program.CDom
import Program.Analysis
import Program.DynamicAnalysis (isSecureEmpirically, isSecureEmpiricallyCombinedTest, isLSODEmpirically)
import Program.Generator (GeneratedProgram(..), toCode, toProgram,
                          IntraGeneratedProgram(..), toCodeIntra, toProgramIntra,
                          SimpleProgram(..), toCodeSimple, toProgramSimple,
                          SimpleWithArraysProgram(..), toProgramSimpleWithArrays, toCodeSimpleWithArrays,
                          SimpleCFG(..),
                          Generated(..))
import Program.TransitionSystem

import Program.Properties.CDom


import IRLSOD
import MicroArchitecturalDependence
import CacheExecution
import qualified CacheStateDependence as Precise
import qualified CacheStateDependenceImprecise as Imprecise
import qualified CacheStateDependenceAgeSets as AgeSets
import CacheSlice
import Execution
import ExecutionTree
import PNI
import Unicode
import Util
import NNGraph

import Algebra.Lattice

import qualified Data.Graph.Inductive.FA as FA
import Data.Graph.Inductive.Util
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.Dataflow
import Data.Graph.Inductive.Query.Dependence
import Data.Graph.Inductive.Query.ProgramDependence
import Data.Graph.Inductive.Query.ControlDependence
import Data.Graph.Inductive.Query.LCA
import Data.Graph.Inductive.Query.PostDominance
import Data.Graph.Inductive.Query.PostDominance.Numbered
import Data.Graph.Inductive.Query.NTICD
import Data.Graph.Inductive.Query.OrderDependence
import Data.Graph.Inductive.Query.NTIODSlice
import Data.Graph.Inductive.Query.InfiniteDelay
import qualified Data.Graph.Inductive.Query.FCACD as FCACD
import Data.Graph.Inductive.Query.TimingDependence
import Data.Graph.Inductive.Query.DataDependence
import Data.Graph.Inductive.Query.DataConflict
import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.BalancedSCC
import Data.Graph.Inductive.Arbitrary
import Data.Graph.Inductive.Query.TSCD
import Data.Graph.Inductive.Query.PureTimingDependence
import Data.Graph.Inductive.Query.Util.GraphTransformations (sinkShrinkedGraph)

import Data.Tree

import Data.Graph.Inductive.Query.Dominators
import Data.Graph.Inductive.Arbitrary.Reducible

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set



data Aes = Aes {
    cacheSize :: CacheSize,
    forMain :: For,
    encryptStateInputNode0 :: Node,
    keyInputNode :: Node
  }

aes_main = Aes {
    cacheSize = 4,
    forMain = br_aes_small_cbcenc_main mainInput Skip,
    encryptStateInputNode0 = 274,
    keyInputNode = 291
  }

aes_main_ct = Aes {
    cacheSize = 4,
    forMain = br_aes_small_cbcenc_main_ct mainInput Skip,
    encryptStateInputNode0 = 17,
    keyInputNode = 34
  }

aes_main_ct_precache = Aes {
    cacheSize = 12,
    forMain = br_aes_small_cbcenc_main_ct_precache mainInput Skip,
    encryptStateInputNode0 = 274,
    keyInputNode = 291
  }


initACS = AgeSets.initialAbstractCacheState
csg     = AgeSets.cacheStateGraph
ccdg    = AgeSets.cacheCostDecisionGraph
-- csdOf   = AgeSets.csdMergeDirectOf
csdOf   = AgeSets.csdFromDataDep

main = let {
         aes@(Aes { cacheSize, forMain, encryptStateInputNode0, keyInputNode }) = aes_main_ct_precache ;
         debugNs = [encryptStateInputNode0, keyInputNode] ;
         pr = for2Program $ forMain :: Program Gr ;
         graph = tcfg pr ;
         n0 = entryOf pr $ procedureOf pr $ mainThread pr ;
         nx = exitOf  pr $ procedureOf pr $ mainThread pr ;
         csGraph =  csg cacheSize graph initACS n0 ;
         (ccg, cost) = ccdg cacheSize graph n0
       } in
  do
    putStrLn  $ show $ length $ nodes $ graph
    putStrLn  $ show $ (n0,nx)
    showGraphWith simpleShow simpleShow $ withNodes $ graph

    putStrLn  $ show $ length $ nodes $ ccg
    showGraphWith simpleShow simpleShow $ withNodes $ ccg

    putStrLn  $ show $ cacheTimingSliceFor cacheSize csdOf ccdg graph debugNs n0 (Set.fromList [nx])

    
    -- putStrLn  $ show $ length $ nodes $ csGraph
    -- showGraphWith simpleShow simpleShow $ withNodes $ csGraph

showCdomChef p = [ ((n,n'),c) | ((n,n'),c) <- Map.toList $ idomChef p, (n,n') ∈ mhp]
  where mhp = mhpSetFor p

showGraph :: (Graph gr, Show a, Show b)  => gr a b -> IO (GHC.IO.Handle.Types.Handle, GHC.IO.Handle.Types.Handle, GHC.IO.Handle.Types.Handle, ProcessHandle)
showGraph = showGraphWith show show
-- IO (Handle, Handle, Handle, ProcessHandle)
showGraphWith :: Graph gr => (a -> String) -> (b -> String) -> (gr a b) -> IO (GHC.IO.Handle.Types.Handle, GHC.IO.Handle.Types.Handle, GHC.IO.Handle.Types.Handle, ProcessHandle)
showGraphWith showN showE g = do
  let dot = showDot (fglToDotGeneric g showN showE id)
  randomInt <- getStdRandom (randomR (1,65536)) :: IO Int
  let file = "file" ++ (show randomInt) ++ ".dot"
  writeFile file dot
  runInteractiveCommand $ "xdot " ++ file

showPDG p = showGraph $ programDependenceGraphP p
showcPDG p = showGraph $ concurrentProgramDependenceGraphP p mhp
  where mhp = mhpSetFor p
showCFG p = showGraph $ tcfg p
-- showSDGSimp sdg = showGraph $ efilter f sdg
--   where f (_,_, SummaryDependence) = True
--         f (_,_, ParameterInDependence)   = True
--         f (_,_, ParameterOutDependence)  = True
--         f (_,_, CallDependence)          = True
--         f (_,_, ControlDependence)       = True
--         f _                              = False
showTDG p = showGraph $ timingDependenceGraphP p
showConflicts p = showGraph $ dataConflictGraphP p
showInterIDomGraph gr s = showGraph $ withNodes $ trrAcyclic $ ( fromPredMap (interDom gr s) :: Gr () ())
showInterIDomGraphGeneral gr s = showGraph $ withNodes $ trrAcyclic $ ( fromPredMap (interDomGeneral summary gr s) :: Gr () ())
  where summary = sameLevelSummaryGraph'WithBs gr

investigate s gr = do
  showGraph $ withNodes $ gr
  showInterIDomGraph gr s
  putStrLn $ show $ chopsInterIDomAreChopsCounterExamples (InterCFG s gr)
  


showDomTree cdomComputation p = showGraph idom

  where
    cdom = cdomComputation p
    idom = insEdge (entry,entry,()) $ idomToTree cdom
    entry = entryOf p $ procedureOf p $ mainThread p

  
testSinkPaths = do
  (CG _ generatedGraph) <- (generate $ resize 40 arbitrary :: IO ((Connected Gr () ())))
  --(NME generatedGraph) <- (generate $ resize 30 arbitrary :: IO ((NoMultipleEdges Gr () ())))
  showGraph $ withNodes $ withoutMultipeEdges generatedGraph
  let n = head $ nodes generatedGraph
  forM ((sinkPathsFor generatedGraph) ! n) (\p -> putStrLn $ show (n,p))
mainEquiv p = do
  putStrLn $ show $ length $ allFinishedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquiv p defaultInput defaultInput'

mainEquivAnnotated p = do
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquivAnnotated p defaultInput defaultInput'

mainEquivAnnotatedSampled p = do
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput
  putStrLn $ show $ length $ allFinishedAnnotatedExecutionTraces p defaultInput'
  showCounterExamplesPniForEquivAnnotatedSampled p defaultInput defaultInput'

mainEquivAnnotatedSome p = do
  showCounterExamplesPniForEquivAnnotatedSome 7500 p defaultInput defaultInput'


withoutMultipeEdges :: (Eq b ,DynGraph gr) => gr a b -> gr a b
withoutMultipeEdges g =
  mkGraph (labNodes g) [ (n,m,e) | (n,m,e) <- nub $ labEdges g]

mainFindMorePrecise = forever $ showMorePrecise isSecureTimingClassification isSecureTimingCombinedTimingClassification
mainFindUnsound     = forever $ showMorePrecise isSecureTimingClassification isSecureEmpirically

showMorePrecise :: (Program Gr -> Bool) -> (Program Gr -> Bool) -> IO ()
showMorePrecise a1 a2 = do
    generated <- sample' (arbitrary :: Gen GeneratedProgram)
    forM_ generated (\gen -> do
       let p :: Program Gr = toProgram gen
       let sec1 = a1  p
       let sec2 = a2 p

       putStrLn $ show $ toCode gen

       putStr "a1: "
       putStrLn $ show $ sec1

       putStr "a2: "
       putStrLn $ show $ sec2

       when (sec1 ∧ ((¬) sec2)) $ do
--       when (sec1 /= sec2) $ do
         showCFG p
         return ()

       putStrLn ""
     )
