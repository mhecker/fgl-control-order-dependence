module Program.For where

import IRLSOD
import Program

import Control.Monad.Gen
import Control.Monad


import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.List (find)
import Data.Maybe (fromJust)


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util


data For = If   BoolFunction For For
         | Ass  Var VarFunction
         | ForC Val For
         | ForV Var For
         | Seq For For
         | Skip
         | ReadFromChannel Var InputChannel
         | PrintToChannel Var OutputChannel
         | SpawnThread StaticThread


compile :: DynGraph gr => Map StaticThread Node -> Node -> For -> Gen Node (gr CFGNode CFGEdge, Node, [Node])
compile entryOf nStart (If b sTrue sFalse) = do
  nTrue <- gen
  nFalse <- gen
  (gTrue, nTrue', nodesInTrue)  <- compile entryOf nTrue sTrue
  (gFalse,nFalse',nodesInFalse) <- compile entryOf nFalse sFalse
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nTrue, nFalse, nTrue', nFalse', nJoin] ]
                   [(nStart, nTrue,  Guard True  b),
                    (nStart, nFalse, Guard False b),
                    (nTrue', nJoin, nop),
                    (nFalse', nJoin, nop)
                   ]
            `mergeTwoGraphs` gTrue
            `mergeTwoGraphs` gFalse,
            nJoin,
            [nStart, nJoin] ++ nodesInTrue ++ nodesInFalse
           )

compile entryOf nStart (Ass var f) = do
  nEnd <- gen
  let nodesInThread = [nStart, nEnd]
  return $ (mkGraph [(n,n) | n <- nodesInThread ]
                    [(nStart, nEnd, Assign var f)],
            nEnd,
            nodesInThread
           )

compile entryOf nStart (ForC val s) = do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop',nodesInLoop)  <- compile entryOf nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nInit,nLoop,nLoop',nJoin]]
                    [(nStart, nInit, Assign loopvar (Val val)),
                     (nInit,  nLoop, Guard True  (Leq (Val 0) (Var loopvar) )),
                     (nInit,  nJoin, Guard False (Leq (Val 0) (Var loopvar) )),
                     (nLoop', nInit, Assign loopvar ((Var loopvar) `Plus` (Val (-1))))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin,
            [nStart, nJoin, nInit] ++ nodesInLoop
           )
    where loopvar = "_loopVar" ++ (show nStart)

compile entryOf nStart (ForV var s) = do
  nLoop <- gen
  (gLoop,nLoop', nodesInLoop)  <- compile entryOf nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nJoin, nLoop, nLoop'] ]
                    [(nStart,  nLoop, Guard True  (Leq (Val 0) (Var var))),
                     (nStart,  nJoin, Guard False (Leq (Val 0) (Var var))),
                     (nLoop',  nStart, Assign var ((Var var) `Plus` (Val (-1))))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin,
            [nStart, nJoin] ++ nodesInLoop
           )

compile entryOf nStart (Seq s1 s2) = do
  (g1,nMid, nodesInS1) <- compile entryOf nStart s1
  (g2,nEnd, nodesInS2) <- compile entryOf nMid   s2
  return $ (g1 `mergeTwoGraphs` g2, nEnd, [nStart] ++ nodesInS1 ++ nodesInS2 )

compile entryOf nStart Skip = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, nop)],
            nEnd,
            [nStart, nEnd]
           )

compile entryOf nStart (ReadFromChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Read var ch)],
            nEnd,
            [nStart, nEnd]
           )

compile entryOf nStart (PrintToChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Print var ch)],
            nEnd,
            [nStart, nEnd]
           )

compile entryOf nStart (SpawnThread threadId) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd, nThread]]
                    [(nStart, nEnd, nop),
                     (nStart, nThread, Spawn)],
            nEnd,
            [nStart, nEnd]
           )
    where nThread = entryOf ! threadId


compileAll :: DynGraph gr => Map StaticThread For -> Gen Node (Map StaticThread (Node,gr CFGNode CFGEdge,Node,[Node]))
compileAll threads = do
  nodes <- forM (Map.toList threads) $ (\(t,program) -> do
     entryNode <- gen
     return (t,entryNode,program)
   )
  let entryOf = (Map.fromList $ fmap (\(t,entryNode,program) -> (t,entryNode)) nodes)
  graphs <- forM nodes $ (\(t,entryNode,program) -> do
     (graph,exitNode,nodes) <- compile entryOf
                                       entryNode
                                       program
     return $ (t, (entryNode,graph,exitNode,nodes))
   )
  return $ Map.fromList graphs



compileAllToProgram :: DynGraph gr => Map StaticThread For -> Program gr
compileAllToProgram code = Program {
    tcfg = tcfg,
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList $ staticThreads,
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    clInit = error "clInit noch nicht definiert"
   }
  where staticThreadOf n = fromJust $
          find (\t -> let (_,_,_,nodes) = compiledCode ! t in n `elem` nodes)
               staticThreads
        staticThreads = Map.keys code
        entryOf = (!) (fmap (\(entryNode,_  ,_       ,_) -> entryNode) compiledCode)
        exitOf  = (!) (fmap (\(_        ,_  ,exitNode,_) -> exitNode ) compiledCode)
        tcfg    = foldr1
                   mergeTwoGraphs
                   [ cfg | (_,(_        ,cfg,_       ,_)) <- Map.toList $ compiledCode ]

        compiledCode = runGenFrom 1 $ compileAll code
