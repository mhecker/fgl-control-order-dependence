module Program.For where

import IRLSOD
import Program

import Control.Monad.Gen
import Control.Monad

import Control.Exception.Base (assert)

import Unicode((∊), (∪))

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



twoAddressCode :: For -> For
twoAddressCode c = twoAddressCodeFrom r0 c
  where r0 = maximum ( 0 : [ r | c <- cs, r <- regsIn c ]) + 1000
        cs = subCommands c

        regsIn (If bf _ _)            =  [ r | VarName (Register r) <- Set.toList $ useB bf ]
        regsIn (ForC _ _)             =  []
        regsIn (ForV x _ )            =  [ r |         (Register r) <- [x] ]
        regsIn (Ass x vf)             =  [ r | VarName (Register r) <- Set.toList $ useV vf ]
                                      ++ [ r |         (Register r) <- [x] ]
        regsIn (AssArr a ix vf)       =  [ r | VarName (Register r) <- Set.toList $ useV ix ∪ useV vf ]
        regsIn (ReadFromChannel x _)  =  [ r |         (Register r) <- [x] ]
        regsIn (PrintToChannel  vf _) =  [ r | VarName (Register r) <- Set.toList $ useV vf ]
        regsIn (Skip)                 =  []
        regsIn (CallProcedure _)      =  []
        regsIn (SpawnThread _)        =  []
        regsIn (Seq _ _)              =  []


twoAddressCodeFrom :: Int -> For -> For
twoAddressCodeFrom r0 (If bf c1 c2) =
  let (loads, bf', _) = twoAddressCodeB r0 bf in case loads of
    Nothing ->          (If bf' (twoAddressCode c1) (twoAddressCode c2))
    Just ls -> ls `Seq` (If bf' (twoAddressCode c1) (twoAddressCode c2))
twoAddressCodeFrom r0  (Ass var vf)  =
  let (loads, vf', _) = twoAddressCodeV r0 vf in case loads of
    Nothing ->          (Ass var vf')
    Just ls -> ls `Seq` (Ass var vf')
twoAddressCodeFrom r0  (AssArr arr ix vf)  =
  let (loadsVf, vf', r) = twoAddressCodeV r0 vf
      (loadsIx, ix', _) = twoAddressCodeV r ix
      loads = loadsVf `sseq` loadsIx
  in case loads of
       Nothing ->          (AssArr arr ix' vf')
       Just ls -> ls `Seq` (AssArr arr ix' vf')
twoAddressCodeFrom r0  (ForC val c) = ForC val (twoAddressCodeFrom r0 c)
twoAddressCodeFrom r0  (ForV var c) = ForV var (twoAddressCodeFrom r0 c)
twoAddressCodeFrom r0  (Seq c1 c2 ) = Seq (twoAddressCodeFrom r0 c1) (twoAddressCodeFrom r0 c2)
twoAddressCodeFrom r0  c = c


twoAddressCodeB :: Int -> BoolFunction -> (Maybe For, BoolFunction, Int)
twoAddressCodeB r bf@CTrue =  (Nothing, bf, r)
twoAddressCodeB r bf@CFalse = (Nothing, bf, r)
twoAddressCodeB r bf@(Leq x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Leq x' y', r'')
twoAddressCodeB r bf@(Eeq x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Eeq x' y', r'')
twoAddressCodeB r bf@(And x y) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
        (loadsY, y', r'') = twoAddressCodeB r' y
    in (loadsX `sseq` loadsY, And x' y', r'')
twoAddressCodeB r bf@(Or x y) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
        (loadsY, y', r'') = twoAddressCodeB r' y
    in (loadsX `sseq` loadsY, And x' y', r'')
twoAddressCodeB r bf@(Not x) =
    let (loadsX, x', r' ) = twoAddressCodeB r  x
    in (loadsX, Not x', r')


sseq Nothing r = r
sseq l Nothing = l
sseq (Just l) (Just r) = Just (l `Seq` r)


twoAddressCodeV :: Int -> VarFunction -> (Maybe For, VarFunction, Int)
twoAddressCodeV r vf@(Val _) = (Nothing, vf, r)
twoAddressCodeV r vf@(Var (Register rr)) = assert (rr < r) $ (Nothing, vf, r)
twoAddressCodeV r (ArrayRead x ix) =
    let (loadsIx, ix', r' ) = twoAddressCodeV r ix
    in (loadsIx `sseq` (Just $ Ass (Register r') (ArrayRead x ix')), Var (Register r'), r' + 1)
twoAddressCodeV r vf@(Var x) = (Just $ Ass (Register r) vf, Var (Register r), r + 1)
twoAddressCodeV r vf@(Plus x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Plus x' y', r'')
twoAddressCodeV r vf@(Minus x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Minus x' y', r'')
twoAddressCodeV r vf@(Times x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Times x' y', r'')
twoAddressCodeV r vf@(Div x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Div x' y', r'')
twoAddressCodeV r vf@(Mod x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Mod x' y', r'')
twoAddressCodeV r vf@(Shl x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Shl x' y', r'')
twoAddressCodeV r vf@(Shr x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Shr x' y', r'')
twoAddressCodeV r vf@(Xor x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, Xor x' y', r'')
twoAddressCodeV r vf@(BAnd x y) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
        (loadsY, y', r'') = twoAddressCodeV r' y
    in (loadsX `sseq` loadsY, BAnd x' y', r'')
twoAddressCodeV r bf@(Neg x) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
    in (loadsX, Neg x', r')
twoAddressCodeV r bf@(BNot x) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
    in (loadsX, BNot x', r')
twoAddressCodeV r vf@(AssertRange min max x) =
    let (loadsX, x', r' ) = twoAddressCodeV r  x
    in (loadsX, (AssertRange min max x'), r')



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


vfMapB :: (VarFunction -> VarFunction) -> BoolFunction -> BoolFunction
vfMapB f (Leq vf1 vf2) = Leq vf1' vf2'
  where vf1' = f vf1
        vf2' = f vf2
vfMapB f (Eeq vf1 vf2) = Eeq vf1' vf2'
  where vf1' = f vf1
        vf2' = f vf2
vfMapB f (And bf1 bf2) = And bf1' bf2'
  where bf1' = vfMapB f bf1
        bf2' = vfMapB f bf2
vfMapB f (Or bf1 bf2) = Or bf1' bf2'
  where bf1' = vfMapB f bf1
        bf2' = vfMapB f bf2
vfMapB f (Not bf) = Not bf'
  where bf' = vfMapB f bf

vfMapF :: (VarFunction -> VarFunction) -> For -> For
vfMapF f (If bf c1 c2) = If bf' c1' c2'
  where bf' = vfMapB f bf
        c1' = vfMapF f c1
        c2' = vfMapF f c2
vfMapF f (Ass x vf) = Ass x vf'
  where vf' = f vf
vfMapF f (AssArr a ix vf) = AssArr a ix' vf'
  where vf' = f vf
        ix' = f ix
vfMapF f (ForC i c) = ForC i c' 
  where c' = vfMapF f c
vfMapF f (ForFromToStepUsing from to step ix c) = (ForFromToStepUsing from to step ix c)
  where c' = vfMapF f c
vfMapF f (ForV x c) = ForV x c' 
  where c' = vfMapF f c
vfMapF f (Seq c1 c2) = Seq c1' c2'
  where c1' = vfMapF f c1
        c2' = vfMapF f c2
vfMapF f (PrintToChannel vf ch) = PrintToChannel vf' ch
  where vf' = f vf
vfMapF f for@(ReadFromChannel _ _) = for
vfMapF f for@(SpawnThread _)       = for
vfMapF f for@(CallProcedure _)     = for
vfMapF f for@(Skip)                = for
