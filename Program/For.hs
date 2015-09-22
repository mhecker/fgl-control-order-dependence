module Program.For where

import IRLSOD
import Program

import Control.Monad.Gen


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
         | SpawnThread Node


compile :: DynGraph gr => Node -> For -> Gen Node (gr CFGNode CFGEdge, Node)
compile nStart (If b sTrue sFalse) = do
  nTrue <- gen
  nFalse <- gen
  (gTrue,nTrue')  <- compile nTrue sTrue
  (gFalse,nFalse') <- compile nFalse sFalse
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

compile nStart (Ass var f) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Assign var f)],
            nEnd
           )

compile nStart (ForC val s) = do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop')  <- compile nLoop s
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

compile nStart (ForV var s) = do
  nLoop <- gen
  (gLoop,nLoop')  <- compile nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nJoin, nLoop, nLoop']]
                    [(nStart,  nLoop, Guard True  (Leq (Val 0) (Var var))),
                     (nStart,  nJoin, Guard False (Leq (Val 0) (Var var))),
                     (nLoop',  nStart, Assign var ((Var var) `Plus` (Val (-1))))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin
           )

compile nStart (Seq s1 s2) = do
  (g1,nMid) <- compile nStart s1
  (g2,nEnd) <- compile nMid   s2
  return $ (g1 `mergeTwoGraphs` g2, nEnd)

compile nStart Skip = do
  nNext <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nNext]]
                    [(nStart, nNext, nop)],
            nNext
           )

compile nStart (ReadFromChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Read var ch)],
            nEnd
           )

compile nStart (PrintToChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Print var ch)],
            nEnd
           )

compile nStart (SpawnThread nThread) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd, nThread]]
                    [(nStart, nEnd, nop),
                     (nStart, nThread, Spawn)],
            nEnd
           )
