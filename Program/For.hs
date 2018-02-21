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


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Util

data For = If   BoolFunction For For
         | Ass  Var VarFunction
         | ForC Val For
         | ForV Var For
         | Seq For For
         | Skip
         | ReadFromChannel Var         InputChannel
         | PrintToChannel  VarFunction OutputChannel
         | SpawnThread StaticThread
         | CallProcedure StaticProcedure
  deriving Show


subCommands :: For -> [For]
subCommands c@(If _ c1 c2) = c:(subCommands c1 ++ subCommands c2)
subCommands c@(ForC _ c1) = c:(subCommands c1)
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



compile :: DynGraph gr => Map StaticThread Node -> Map StaticProcedure Node -> Node -> For -> Gen Node (gr CFGNode CFGEdge, Node, [Node])
compile entryOf entryOfProcedure nStart (If b sTrue sFalse) = do
  nTrue <- gen
  nFalse <- gen
  (gTrue, nTrue', nodesInTrue)  <- compile entryOf entryOfProcedure nTrue sTrue
  (gFalse,nFalse',nodesInFalse) <- compile entryOf entryOfProcedure nFalse sFalse
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

compile entryOf entryOfProcedure nStart (Ass var f) = do
  nEnd <- gen
  let nodesInThread = [nStart, nEnd]
  return $ (mkGraph [(n,n) | n <- nodesInThread ]
                    [(nStart, nEnd, Assign var f)],
            nEnd,
            nodesInThread
           )

compile entryOf entryOfProcedure nStart (ForC val s) = do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop',nodesInLoop)  <- compile entryOf entryOfProcedure nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nInit,nLoop,nLoop',nJoin]]
                    [(nStart, nInit, Assign loopvar (Val val)),
                     (nInit,  nLoop, Guard True  (Leq (Val 1) (Var loopvar) )),
                     (nInit,  nJoin, Guard False (Leq (Val 1) (Var loopvar) )),
                     (nLoop', nInit, Assign loopvar ((Var loopvar) `Plus` (Val (-1))))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin,
            [nStart, nJoin, nInit] ++ nodesInLoop
           )
    where loopvar = ThreadLocal $ "_loopVar" ++ (show nStart)

compile entryOf entryOfProcedure nStart (ForV var s) = do
  nInit <- gen
  nLoop <- gen
  (gLoop,nLoop', nodesInLoop)  <- compile entryOf entryOfProcedure nLoop s
  nJoin <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nInit, nJoin, nLoop, nLoop'] ]
                    [(nStart,  nInit, Assign loopvar (Var var)),
                     (nInit,   nLoop, Guard True  (Leq (Val 1) (Var loopvar))),
                     (nInit,   nJoin, Guard False (Leq (Val 1) (Var loopvar))),
                     (nLoop',  nInit, Assign loopvar ((Var loopvar) `Plus` (Val (-1))))
                   ]
            `mergeTwoGraphs` gLoop,
            nJoin,
            [nStart, nJoin, nInit] ++ nodesInLoop
           )
    where loopvar = ThreadLocal $ "_loopVar" ++ (show nStart)

compile entryOf entryOfProcedure nStart (Seq s1 s2) = do
  (g1,nMid, nodesInS1) <- compile entryOf entryOfProcedure nStart s1
  (g2,nEnd, nodesInS2) <- compile entryOf entryOfProcedure nMid   s2
  return $ (g1 `mergeTwoGraphs` g2, nEnd, [nStart] ++ nodesInS1 ++ nodesInS2 )

compile entryOf entryOfProcedure nStart Skip = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, nop)],
            nEnd,
            [nStart, nEnd]
           )

compile entryOf entryOfProcedure nStart (ReadFromChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Read var ch)],
            nEnd,
            [nStart, nEnd]
           )

compile entryOf entryOfProcedure nStart (PrintToChannel var ch) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd]]
                    [(nStart, nEnd, Print var ch)],
            nEnd,
            [nStart, nEnd]
           )

compile entryOf entryOfProcedure nStart (SpawnThread threadId) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd, nThread]]
                    [(nStart, nEnd, nop),
                     (nStart, nThread, Spawn)],
            nEnd,
            [nStart, nEnd]
           )
    where nThread = entryOf ! threadId


compile entryOf entryOfProcedure nStart (CallProcedure procId) = do
  nEnd <- gen
  return $ (mkGraph [(n,n) | n <- [nStart, nEnd, nProc]]
                    [(nStart, nEnd, CallSummary),
                     (nStart, nProc, Call),
                     (nProc, nStart, Return)
                    ],
            nEnd,
            [nStart, nEnd]
           )
    where nProc = entryOfProcedure ! procId


compileAll :: DynGraph gr => Map StaticThread For -> Map StaticProcedure For -> Gen Node (Map StaticThread (Node,gr CFGNode CFGEdge,Node,[Node]), Map StaticProcedure (Node,gr CFGNode CFGEdge,Node,[Node]))
compileAll threads procedures = do
  threadEntryNodes <- forM (Map.toList threads) $ (\(t,program) -> do
     entryNode <- gen
     return (t,entryNode,program)
   )
  procedureEntryNodes <- forM (Map.toList procedures) $ (\(p,program) -> do
     entryNode <- gen
     return (p,entryNode,program)
   )
  let entryOf           = (Map.fromList $ fmap (\(t,entryNode,program) -> (t,entryNode)) threadEntryNodes)
  let entryOfProcedures = (Map.fromList $ fmap (\(p,entryNode,program) -> (p,entryNode)) procedureEntryNodes)
  threadGraphs <- forM threadEntryNodes $ (\(t,entryNode,program) -> do
     (graph,exitNode,nodes) <- compile entryOf
                                       entryOfProcedures
                                       entryNode
                                       (Skip `Seq` program) -- prevent the first edge in any thread from being a (possibly high)
                                                            -- Read instruction, which would make the first node, on which all
                                                            -- others control-depend by default, high
                                                            -- TODO: better cope with this in the analysis!?!?
     return $ (t, (entryNode,graph,exitNode,nodes))
   )
  procedureGraphs <- forM procedureEntryNodes $ (\(p,entryNode,program) -> do
     (graph,exitNode,nodes) <- compile entryOf
                                       entryOfProcedures
                                       entryNode
                                       (Skip `Seq` program) -- prevent the first edge in any thread from being a (possibly high)
                                                            -- Read instruction, which would make the first node, on which all
                                                            -- others control-depend by default, high
                                                            -- TODO: better cope with this in the analysis!?!?
     return $ (p, (entryNode,graph,exitNode,nodes))
   )
  return $ (Map.fromList threadGraphs, Map.fromList procedureGraphs)



compileAllToProgram :: DynGraph gr => Map StaticThread For -> Map StaticProcedure For -> Program gr
compileAllToProgram threadCode procedureCode = Program {
    tcfg = tcfg,
    staticThreadOf = staticThreadOf,
    staticThreads  = Set.fromList $ staticThreads,
    staticProcedureOf = staticProcedureOf,
    staticProcedures  = Set.fromList $ staticProcedures,
    mainThread = 1,
    entryOf = entryOf,
    exitOf = exitOf,
    observability = error "observability noch nicht definiert"
   }
  where staticThreadOf n = fromJust $
          find (\t -> let (_,_,_,nodes) = compiledThreadCode ! t in n ∊ nodes)
               staticThreads
        staticThreads = Map.keys threadCode
        staticProcedureOf n = fromJust $
          find (\t -> let (_,_,_,nodes) = compiledProcedureCode ! t in n ∊ nodes)
               staticProcedures
        staticProcedures = Map.keys procedureCode
        entryOf = (!) (fmap (\(entryNode,_  ,_       ,_) -> entryNode) compiledThreadCode)
        exitOf  = (!) (fmap (\(_        ,_  ,exitNode,_) -> exitNode ) compiledThreadCode)
        tcfg    = foldr1
                   mergeTwoGraphs
                   [ cfg | (_,(_        ,cfg,_       ,_)) <- Map.toList $ compiledThreadCode ]

        (compiledThreadCode, compiledProcedureCode) = runGenFrom 1 $ compileAll threadCode procedureCode
