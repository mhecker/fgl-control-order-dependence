module Program.For where

import IRLSOD
import Program

import Control.Monad.Gen
import Control.Monad

import Unicode((∊))

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set


import Data.List (find)
import Data.Maybe (fromJust)

import Debug.Trace

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util

data For = If   BoolFunction For For
         | Ass  Var VarFunction
         | AssArr Array VarFunction VarFunction
         | ForC Val For
         | ForFromToStepUsing Val Val Val Var For
         | ForV Var For
         | Seq For For
         | Skip
         | ReadFromChannel Var         InputChannel
         | PrintToChannel  VarFunction OutputChannel
         | SpawnThread StaticThread
         | CallProcedure StaticProcedure
  deriving (Show, Eq)


subCommands :: For -> [For]
subCommands c@(If _ c1 c2) = c:(subCommands c1 ++ subCommands c2)
subCommands c@(ForC _ c1) = c:(subCommands c1)
subCommands c@(ForFromToStepUsing _ _ _ _ c1) = c:(subCommands c1)
subCommands c@(ForV _ c1) = c:(subCommands c1)
subCommands c@(Seq c1 c2) = c:(subCommands c1++ subCommands c2)
subCommands c = [c]



toChannelJava ::
  String ->
  [InputChannel]  ->
  [OutputChannel] ->
  (InputChannel  -> SecurityLattice) ->
  (OutputChannel -> SecurityLattice) -> String
toChannelJava package inputs outputs obsIn obsOut = unlines $  [
    "package example;",
    "import static edu.kit.joana.ui.annotations.Level.*;",
    "import edu.kit.joana.ui.annotations.Level;",
    "import edu.kit.joana.ui.annotations.Sink;",
    "import edu.kit.joana.ui.annotations.Source;",
    "public class Channels {"
   ] ++ concat [ [
    "    @Source(level=" ++ (fromLevel $ obsIn channel) ++ ")",
    "    public int readFromChannel() {",
    "        return 0;",
    "    }" ] | channel <- inputs
   ] ++ concat [ [
    "    @Source(level=" ++ (fromLevel $ obsOut channel) ++ ")",
    "    public vouid printToChannel(int x) {",
    "    }" ] | channel <- outputs
   ]

 where fromLevel Low  = "LOW"
       fromLevel High = "HIGH"



compile :: DynGraph gr => Map StaticThread StaticProcedure -> Map StaticProcedure Node -> Map StaticProcedure Node -> Node -> For -> Gen Node (gr CFGNode CFGEdge, Node, [Node])
compile procedureOf entryOfProcedure exitOfProcedure nStart (If b sTrue sFalse) = do
  nTrue <- gen
  nFalse <- gen
  (gTrue, nTrue', nodesInTrue)  <- compile procedureOf entryOfProcedure exitOfProcedure  nTrue sTrue
  (gFalse,nFalse',nodesInFalse) <- compile procedureOf entryOfProcedure exitOfProcedure  nFalse sFalse
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

compile procedureOf entryOfProcedure exitOfProcedure  nStart (Ass var f) = do
  nEnd <- gen
  let nodesInThread = [nStart, nEnd]
  return $ (mkGraph [(n,n) | n <- nodesInThread ]
                    [(nStart, nEnd, Assign var f)],
            nEnd,
            nodesInThread
           )

compile procedureOf entryOfProcedure exitOfProcedure  nStart (AssArr arr i f) = do
  nEnd <- gen
  let nodesInThread = [nStart, nEnd]
  return $ (mkGraph [(n,n) | n <- nodesInThread ]
                    [(nStart, nEnd, AssignArray arr i f)],
            nEnd,
            nodesInThread
           )


compile procedureOf entryOfProcedure exitOfProcedure  nStart (ForC val s) = do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop',nodesInLoop)  <- compile procedureOf entryOfProcedure exitOfProcedure  nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nInit,nLoop,nLoop',nJoin]]
                    [(nStart, nInit, Assign loopvar (Val val)),
                     (nInit,  nLoop, Guard True  (Leq (Val 1) (Var loopvar) )),
                     (nInit,  nJoin, Guard False (Leq (Val 1) (Var loopvar) )),
                     (nLoop', nInit, Assign loopvar ((Var loopvar) `Minus` (Val 1)))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin,
            [nStart, nJoin, nInit] ++ nodesInLoop
           )
    where loopvar = ThreadLocal $ "_loopVar" ++ (show nStart)

compile procedureOf entryOfProcedure exitOfProcedure  nStart (ForFromToStepUsing from to step loopvar s) =
 if to < from then error $ show from ++ " <  " ++ show to else
 if step <= 0 then error $ show step ++ " <= 0" else do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop',nodesInLoop)  <- compile procedureOf entryOfProcedure exitOfProcedure  nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nInit,nLoop,nLoop',nJoin]]
                    [(nStart, nLoop, Assign loopvar (Val from)),
                     (nLoop',  nInit, Guard True  ((Var loopvar) `Leq` (Val $ to - 1 ))),
                     (nLoop',  nJoin, Guard False ((Var loopvar) `Leq` (Val $ to - 1 ))),
                     (nInit, nLoop, Assign loopvar ((Var loopvar) `Plus` (Val step)))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin,
            [nStart, nJoin, nInit] ++ nodesInLoop
           )

compile procedureOf entryOfProcedure exitOfProcedure  nStart (ForV var s) = do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop', nodesInLoop)  <- compile procedureOf entryOfProcedure exitOfProcedure  nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nInit, nJoin, nLoop, nLoop'] ]
                    [(nStart,  nInit, Assign loopvar (Var var)),
                     (nInit,   nLoop, Guard True  (Leq (Val 1) (Var loopvar))),
                     (nInit,   nJoin, Guard False (Leq (Val 1) (Var loopvar))),
                     (nLoop',  nInit, Assign loopvar ((Var loopvar) `Minus` (Val 1)))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin,
            [nStart, nJoin, nInit] ++ nodesInLoop
           )
    where loopvar = ThreadLocal $ "_loopVar" ++ (show nStart)

compile procedureOf entryOfProcedure exitOfProcedure  nStart (Seq s1 s2) = do
  (g1,nMid, nodesInS1) <- compile procedureOf entryOfProcedure exitOfProcedure  nStart s1
  (g2,nEnd, nodesInS2) <- compile procedureOf entryOfProcedure exitOfProcedure  nMid   s2
  return $ (g1 `mergeTwoGraphs` g2, nEnd, [nStart] ++ nodesInS1 ++ nodesInS2 )

compile procedureOf entryOfProcedure exitOfProcedure  nStart Skip = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, nop)],
            nEnd,
            [nStart, nEnd]
           )

compile procedureOf entryOfProcedure exitOfProcedure  nStart (ReadFromChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Read var ch)],
            nEnd,
            [nStart, nEnd]
           )

compile procedureOf entryOfProcedure exitOfProcedure  nStart (PrintToChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Print var ch)],
            nEnd,
            [nStart, nEnd]
           )

compile procedureOf entryOfProcedure exitOfProcedure  nStart (SpawnThread threadId) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd, nThread]]
                    [(nStart, nEnd, nop),
                     (nStart, nThread, Spawn)],
            nEnd,
            [nStart, nEnd]
           )
    where nThread = entryOfProcedure ! (procedureOf ! threadId)


compile procedureOf entryOfProcedure exitOfProcedure  nStart (CallProcedure procId) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd, nProc, nProcExit]]
                    [(nStart, nEnd, CallSummary),
                     (nStart, nProc, Call),
                     (nProcExit, nEnd, Return)
                    ],
            nEnd,
            [nStart, nEnd]
           )
    where nProc = entryOfProcedure ! procId
          nProcExit = exitOfProcedure ! procId


compileAll :: DynGraph gr => Map StaticThread StaticProcedure -> Map StaticProcedure For -> Gen Node (Map StaticProcedure (Node,gr CFGNode CFGEdge,Node,[Node]))
compileAll procedureOf procedures = do
  procedureEntryNodes <- forM (Map.toList procedures) $ (\(p,program) -> do
     entryNode <- gen
     return (p,entryNode,program)
   )
  procedureExitNodes <- forM (Map.toList procedures) $ (\(p,program) -> do
     exitNode <- gen
     return (p,exitNode,program)
   )
  let entryOfProcedures = (Map.fromList $ fmap (\(p,entryNode,program) -> (p,entryNode)) procedureEntryNodes)
  let exitOfProcedures = (Map.fromList $ fmap (\(p,exitNode,program) -> (p,exitNode)) procedureExitNodes)
  procedureGraphs <- forM procedureEntryNodes $ (\(p,entryNode,program) -> do
     (graph,exitNode,nodes) <- compile procedureOf
                                       entryOfProcedures
                                       exitOfProcedures
                                       entryNode
                                       (Skip `Seq` program) -- prevent the first edge in any thread from being a (possibly high)
                                                            -- Read instruction, which would make the first node, on which all
                                                            -- others control-depend by default, high
                                                            -- TODO: better cope with this in the analysis!?!?
     return $ (p, (entryNode,
                   insEdge (exitNode, exitOfProcedures ! p, NoOp) $ insNodeIfNecessary (exitOfProcedures ! p, exitOfProcedures ! p) $ graph,
                   (exitOfProcedures ! p),
                   (exitOfProcedures ! p):nodes
                  )
              )
   )
  return $ Map.fromList procedureGraphs



compileAllToProgram :: DynGraph gr => Map StaticThread StaticProcedure -> Map StaticProcedure For -> Program gr
compileAllToProgram threadCode procedureCode = Program {
    tcfg = tcfg,
    procedureOf = procedureOf,
    staticThreads  = Set.fromList $ staticThreads,
    staticProcedureOf = staticProcedureOf,
    staticProcedures  = Set.fromList $ staticProcedures,
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = error "observability noch nicht definiert"
   }
  where procedureOf t = threadCode ! t
        staticThreads = Map.keys threadCode
        staticProcedureOf n = fromJust $
          find (\t -> let (_,_,_,nodes) = compiledProcedureCode ! t in n ∊ nodes)
               staticProcedures
        staticProcedures = Map.keys procedureCode
        entryOf = (!) (fmap (\(entryNode,_  ,_       ,_) -> entryNode) compiledProcedureCode)
        exitOf  = (!) (fmap (\(_        ,_  ,exitNode,_) -> exitNode ) compiledProcedureCode)
        tcfg    = foldr1
                   mergeTwoGraphs
                   [ cfg | (_,(_        ,cfg,_       ,_)) <- Map.toList $ compiledProcedureCode ]

        compiledProcedureCode = runGenFrom 1 $ compileAll threadCode procedureCode



printIndent :: For -> [String]
printIndent c = print 0 c
  where indent i = concat $ take i $ repeat "\t"
        indentTo i = fmap (indent i ++)

        print i (Seq c1 c2) =
           let c1s   = print 0 c1
               c2s   = print 0 c2
               cs    = c1s ++ c2s
           in indentTo i cs
        print i (Ass x vf)   =
           let cs = [ simpleShow x ++ " := " ++ simpleShow vf ]
           in indentTo i cs 
        print i (AssArr (Array a) ix vf) =
           let cs = [ a ++ "[" ++ simpleShow ix ++ "] := " ++ simpleShow vf ]
           in indentTo i cs 
        print i (If b c1 c2) =
           let csIf   = [ "if " ++ simpleShow b ++ " then " ]
               c1s    = print 1 c1
               csEl   = [ "else" ]
               c2s    = print 1 c2
               csEn   = [ "end" ]
               cs = csIf ++ c1s ++ csEl ++ c2s ++ csEn
           in indentTo i cs
        print i (ForC x c) =
           let csFor  = [ "for _ : [1.." ++ show x ++ "]"]
               c1s    = print 1 c
               csEn   = [ "end" ]
               cs = csFor ++ c1s ++ csEn
           in indentTo i cs
        print i (ForFromToStepUsing from to step ix c) =
           let csFor  = [ "for " ++ simpleShow ix ++ " : [" ++ show from  ++ ", " ++ show (from + step) ++ " .. " ++ show to ++ "]"]
               c1s    = print 1 c
               csEn   = [ "end" ]
               cs = csFor ++ c1s ++ csEn
           in indentTo i cs
        print i (ForV x c) =
           let csFor  = [ "for " ++ show x]
               c1s    = print 1 c
               csEn   = [ "end" ]
               cs = csFor ++ c1s ++ csEn
           in indentTo i cs
        print i Skip =
           let cs = [ "skip" ]
           in indentTo i cs 
        print i (ReadFromChannel x ch) =
           let cs = [ simpleShow x ++ " := " ++  "read_" ++ ch ]
           in indentTo i cs 
        print i (PrintToChannel  vf ch) =
           let cs = [ "print_" ++ ch ++ "(" ++ simpleShow vf  ++ ")"]
           in indentTo i cs 
        print i (SpawnThread t) =
           let cs = [ "fork " ++ show t]
           in indentTo i cs 
        print i (CallProcedure p) =
           let cs = [ "call " ++ show p]
           in indentTo i cs 

putStrIndent c = forM_ (printIndent c) (\s -> do
    putStrLn s
  )

