module Program.For where

import IRLSOD
import Program

import Control.Monad.Gen
import Control.Monad


import Data.Map ( Map, (!) )
import qualified Data.Map as Map


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


compile :: DynGraph gr => Map StaticThread Node -> Node -> For -> Gen Node (gr CFGNode CFGEdge, Node)
compile entryOf nStart (If b sTrue sFalse) = do
  nTrue <- gen
  nFalse <- gen
  (gTrue, nTrue')  <- compile entryOf nTrue sTrue
  (gFalse,nFalse') <- compile entryOf nFalse sFalse
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nTrue, nFalse, nTrue', nFalse', nJoin]]
                   [(nStart, nTrue,  Guard True  b),
                    (nStart, nFalse, Guard False b),
                    (nTrue', nJoin, nop),
                    (nFalse', nJoin, nop)
                   ]
            `mergeTwoGraphs` gTrue
            `mergeTwoGraphs` gFalse,
            nJoin
           )

compile entryOf nStart (Ass var f) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Assign var f)],
            nEnd
           )

compile entryOf nStart (ForC val s) = do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop')  <- compile entryOf nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nInit,nLoop,nLoop',nJoin]]
                    [(nStart, nInit, Assign loopvar (Val val)),
                     (nInit,  nLoop, Guard True  (Leq (Val 0) (Var loopvar) )),
                     (nInit,  nJoin, Guard False (Leq (Val 0) (Var loopvar) )),
                     (nLoop', nInit, Assign loopvar ((Var loopvar) `Plus` (Val (-1))))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin
           )
    where loopvar = "_loopVar" ++ (show nStart)

compile entryOf nStart (ForV var s) = do
  nLoop <- gen
  (gLoop,nLoop')  <- compile entryOf nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nJoin, nLoop, nLoop']]
                    [(nStart,  nLoop, Guard True  (Leq (Val 0) (Var var))),
                     (nStart,  nJoin, Guard False (Leq (Val 0) (Var var))),
                     (nLoop',  nStart, Assign var ((Var var) `Plus` (Val (-1))))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin
           )

compile entryOf nStart (Seq s1 s2) = do
  (g1,nMid) <- compile entryOf nStart s1
  (g2,nEnd) <- compile entryOf nMid   s2
  return $ (g1 `mergeTwoGraphs` g2, nEnd)

compile entryOf nStart Skip = do
  nNext <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nNext]]
                    [(nStart, nNext, nop)],
            nNext
           )

compile entryOf nStart (ReadFromChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Read var ch)],
            nEnd
           )

compile entryOf nStart (PrintToChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Print var ch)],
            nEnd
           )

compile entryOf nStart (SpawnThread threadId) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd, nThread]]
                    [(nStart, nEnd, nop),
                     (nStart, nThread, Spawn)],
            nEnd
           )
    where nThread = entryOf ! threadId


compileAll :: DynGraph gr => Map StaticThread For -> Gen Node (Map StaticThread (Node,gr CFGNode CFGEdge,Node))
compileAll threads = do
  nodes <- forM (Map.toList threads) $ (\(t,program) -> do
     entryNode <- gen
     return (t,entryNode,program)
   )
  let entryOf = (Map.fromList $ fmap (\(t,entryNode,program) -> (t,entryNode)) nodes)
  graphs <- forM nodes $ (\(t,entryNode,program) -> do
     (graph,exitNode) <- compile entryOf
                         entryNode
                         program
     return $ (t, (entryNode,graph,exitNode))
   )
  return $ Map.fromList graphs
