{-# LANGUAGE OverloadedStrings, CPP, TypeFamilies, NamedFieldPuns, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Main (main) where

#define DEBUG 0

import Compiler.Hoopl as H

import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict

import Data.Array
import qualified Data.ByteString.Char8 as C
import Data.Char
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe

import Network.Socket

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
#if DEBUG
import System.IO.Unsafe
#endif

import Text.Regex.TDFA hiding (match)

import AST
import Bus
import Parser
import IR (toIR)
import qualified IR
import Optimize

newtype Mailbox a = Mailbox (MVar a)
-- Just to make SedState Showable
instance Show (Mailbox a) where
    show _ = "Mailbox {}"
data IPCState = IPCState
  { box :: Mailbox (Either (Maybe S) S)
  , bus :: Bus S
  , passenger :: Passenger S }
  deriving (Show)

data File
  = NormalFile { fileIsEOF :: IO Bool, fileMaybeGetLine :: IO (Maybe S), filePutStrLn :: S -> IO () }
  | SocketFile Socket

instance Show File where
  show (NormalFile _ _ _) = "NormalFile{}"
  show (SocketFile s) = "SocketFile " ++ show s

handleFile h = NormalFile (hIsEOF h) (hMaybeGetLine h) (C.hPutStrLn h)
inputListFile :: [FilePath] -> IO File
inputListFile [] = return (NormalFile (hIsEOF stdin) (hMaybeGetLine stdin) C.putStrLn)
inputListFile inputs = do
    current :: MVar Handle <- newEmptyMVar
    inputs <- newMVar inputs

    let nextFile :: IO a -> a -> IO a
        nextFile cont eof = do
            fs <- takeMVar inputs
            case fs of
              [] -> putMVar inputs [] >> return eof
              (f:fs) -> do
                putMVar inputs fs
                putMVar current =<< openFile f ReadMode
                cont

        isEOF :: IO Bool
        isEOF = do
            h <- takeMVar current
            eof <- hIsEOF h
            if eof
              then nextFile isEOF True
              else putMVar current h >> return False

        maybeGetLine :: IO (Maybe S)
        maybeGetLine = do
            h <- takeMVar current
            line <- hMaybeGetLine h
            case line of
                Nothing -> nextFile maybeGetLine Nothing
                Just line -> putMVar current h >> return (Just line)

    nextFile (return ()) ()
    return (NormalFile isEOF maybeGetLine C.putStrLn)

data SedState program = SedState
  { program :: program
  , files :: Map Int File
  , lineNumber :: Int
  , pattern :: Maybe S
  , hold :: Map S S
  , lastRegex :: Maybe RE
  , predicates :: Set Int

  , ipcState :: Maybe IPCState

  -- Pending output? Other tricky stuff?
}
  deriving (Show)

debug :: MonadIO m => String -> m ()
#if DEBUG
debug s = liftIO $ withMVar putstrlock $ \() -> do
    t <- myThreadId
    System.IO.putStrLn (show t ++ ": " ++ s)
putstrlock = unsafePerformIO (newMVar ())
#else
debug _ = return ()
#endif

fatal msg = error ("ERROR: " ++ msg)

-- The wheels on the bus go round and round...
busRider p b = forever $ putMVar b . Right =<< ride p

newIPCState = do
  bus <- newBus
  passenger <- board bus
  box <- newEmptyMVar
  _ <- forkIO (busRider passenger box)
  return IPCState { box = Mailbox box, bus = bus, passenger = passenger }

forkIPCState Nothing = return Nothing
forkIPCState (Just state) = do
  passenger <- board (bus state)
  box <- newEmptyMVar
  _ <- forkIO (busRider passenger box)
  return $ Just state { passenger = passenger, box = Mailbox box }

initialState ipc pgm file0 = do
  ipcState <- if ipc then Just <$> newIPCState else return Nothing
  return SedState {
    program = pgm
  , files = M.singleton 0 file0
  , lineNumber = 0
  , pattern = Nothing
  , hold = M.empty
  , lastRegex = Nothing
  , predicates = S.empty
  , ipcState = ipcState
  }
forkState pgm = get >>= \state -> liftIO $ do
  ipcState' <- forkIPCState (ipcState state)
  return state {
    program = pgm
  , pattern = Nothing
  , lineNumber = 0
  , predicates = S.empty
  , ipcState = ipcState'
 }

setPred (IR.Pred n) b = modify $ \s -> s { predicates = f (predicates s) }
  where
    f | b = S.insert n
      | otherwise = S.delete n
getPred (IR.Pred n) = S.member n . predicates <$> get

runIRLabel :: H.Label -> SedM ()
runIRLabel entry = do
  GMany _ blocks _ <- program <$> get
  block <- case mapLookup entry blocks of
    Nothing -> error ("Entry " ++ show entry ++ " not found in graph?")
    Just block -> return block
  runIRBlock block
runIRBlock block = do
  let lift f n z = z >> f n
  foldBlockNodesF (lift runIR_debug) block (return ())

runIR_debug :: IR.Insn e x -> SedM ()
runIR_debug i@(IR.Comment _) = runIR i
runIR_debug i = do
  debug (show i)
  runIR i

runIR :: IR.Insn e x -> SedM ()
runIR (IR.Label _) = return ()
runIR (IR.Branch l) = runIRLabel l
runIR (IR.Set p cond) = setPred p =<< case cond of
  IR.Bool b -> return b
  IR.Line l -> gets ((l ==) . lineNumber)
  IR.EndLine l -> gets ((l <) . lineNumber)
  IR.Match re -> checkRE re
  IR.MatchLastRE -> checkRE . fromJust =<< gets lastRegex
  IR.AtEOF -> liftIO . fileIsEOF =<< gets (fromJust . M.lookup 0 . files)
runIR (IR.If p t f) = do
  b <- getPred p
  runIRLabel (if b then t else f)
runIR (IR.Listen i maybeHost port) = doListen i maybeHost port
runIR (IR.Accept s c) = doAccept s c
runIR (IR.Fork entry next) = do
    pgm <- program <$> get
    state <- forkState pgm
    forkIO_ $ do
        debug ("start of fork")
        put state
        runIRLabel entry
        debug ("end of fork")
    debug ("parent is after fork")
    runIRLabel next
runIR (IR.Redirect i j) = redirectFile i j
runIR (IR.CloseFile i) = closeFile i

runIR (IR.SetLastRE re) = setLastRegex re

runIR (IR.Subst sub stype) = do
  state <- get
  case pattern state of
    Just p
      | Just (RE _ pat) <- lastRegex state
      , matches@(_:_) <- match stype pat p -> do
          let newp = subst p sub matches
          debug ("Subst: " ++ show p ++ " => " ++ show newp)
          modify $ \state -> state { pattern = Just newp }
    _ -> fatal "Subst: no match when substituting?"

runIR (IR.Message Nothing) = doMessage . fromJust =<< gets pattern
runIR (IR.Message (Just s)) = doMessage s

runIR (IR.PrintS i s) = printTo i s
runIR (IR.Print i) = get >>= \state ->
    case pattern state of
        Just p -> printTo i p
        _ -> return ()
runIR (IR.Clear) = modify $ \state -> state { pattern = Just "" }
runIR (IR.Hold reg) = doHold reg
runIR (IR.Get reg) = doGet reg
runIR (IR.GetA reg) = doGetAppend reg
runIR (IR.Cycle i intr cont eof) = do
    res <- getLineOrEvent i
    let (pat,l,k) = case res of
          Left Nothing -> (Nothing, 0, eof)
          Left (Just s) -> (Just s, 1, cont)
          Right s -> (Just s, 0, intr)
    modify $ \state -> state { pattern = pat, lineNumber = lineNumber state + l }
    runIRLabel k
runIR (IR.Quit code) = liftIO (exitWith code)
runIR (IR.Comment s) = debug ("*** " ++ s)
runIR (IR.Read i) = do
  l <- maybeGetLine i
  case l of
   Just _ -> modify $ \state -> state { pattern = l }
   Nothing -> liftIO exitSuccess
runIR (IR.ReadAppend i) = do
  l <- maybeGetLine i
  case l of
   Just s -> patternAppend s
   Nothing -> liftIO exitSuccess

runIR cmd = fatal ("runIR: Unhandled instruction " ++ show cmd)

setLastRegex re = modify $ \state -> state { lastRegex = Just re }

checkRE (RE _ re) = do
  p <- pattern <$> get
  case p of
    Just p -> return (matchTest re p)
    _ -> return False

type SedPM p a = StateT (SedState p) IO a
type Program = Graph IR.Insn C C
type SedM a = SedPM Program a

doListen i maybeHost port = do
    let hints = defaultHints { addrFlags = [AI_PASSIVE], addrSocketType = Stream }
    let maybeHost' = fmap C.unpack maybeHost
    s <- liftIO $ do
        addr:_ <- getAddrInfo (Just hints) maybeHost' (Just (show port))
        s <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
        setSocketOption s ReuseAddr 1
        bind s (addrAddress addr)
        listen s 7
        return s
    debug ("now listening on " ++ show i)
    replaceFile i (SocketFile s)

doAccept i j = do
    Just (SocketFile s) <- getFile i
    debug ("accepting from " ++ show i ++ " to " ++ show j)
    (c,addr) <- liftIO $ accept s
    debug ("accepted: " ++ show addr)
    h <- liftIO $ socketToHandle c ReadWriteMode
    replaceFile j (handleFile h)

doMessage m = gets ipcState >>= f
  where
    f Nothing = return ()
    f (Just ipcState) =
      do
        debug ("Messaging " ++ show m)
        liftIO (drive (bus ipcState) m)

doHold reg = do
  pat <- fromMaybe "" . pattern <$> get
  debug ("Hold: holding " ++ show pat ++ " in " ++ show reg)
  modify $ \s -> s { hold = M.insert (fromMaybe "" reg) pat (hold s) }
doGet reg =
  modify $ \s -> s { pattern = Just (fromMaybe "" (M.lookup (fromMaybe "" reg) (hold s))) }

doGetAppend reg =
  patternAppend =<< gets (fromMaybe "" . M.lookup (fromMaybe "" reg) . hold)

patternAppend s = do
  p <- gets (fromMaybe "" . pattern)
  debug ("appending " ++ show s ++ " to " ++ show p)
  modify $ \state -> state { pattern = Just (p <> "\n" <> s) }

-- This could be preprocessed a bit better, e.g. having the parser parse the
-- replacement into a list of (Literal|Ref Int).
subst :: S -> S -> [MatchArray] -> S
subst p rep matches = go "" 0 matches
  where
    go acc lastmatch (m:ms)
        | matchstart >= lastmatch = go acc' matchend ms
        | otherwise = go acc lastmatch ms
        where
            (matchstart,matchlen) = m ! 0
            matchend = matchstart + matchlen
            acc' = acc <> substr lastmatch (matchstart - lastmatch)
                       <> replace rep m
    go acc lastmatch [] = acc <> C.drop lastmatch p

    substr s l = C.take l (C.drop s p)
    replace rep match = go "" 0
      where
        go acc i | i == C.length rep = acc
        go acc i = case C.index rep i of
          '\\' -> go (acc <> matchN (digitToInt (C.index rep (i + 1)))) (i + 2)
          '&' -> go (acc <> matchN 0) (i + 1)
          c -> go (C.snoc acc c) (i + 1)
        matchN n = (uncurry substr) (match ! n)

match SubstFirst re p = take 1 (matchAll re p)
match SubstAll re p = matchAll re p
-- TODO Handle not finding enough matches for match i. Should be handled the
-- same as a nonmatch.
match (SubstNth i) re p = [matchAll re p !! i]

closeFile i = do
    f <- getFile i
    debug ("Closing " ++ show i ++ ": " ++ show f)
    {- The underlying socket/files may be used by other threads, so don't
    -- actually close them. Let them be garbage collected instead.
    case M.lookup i (files state) of
        Just (SocketFile s) -> sClose s
        Just (HandleFile h) -> hClose h
        _ -> return ()
    -}
    delFile i
replaceFile i f = do
    closeFile i
    setFile i f
redirectFile i j = do
    f <- getFile j
    case f of
       Just f -> replaceFile i f >> delFile j
       Nothing -> closeFile i

getFile i = gets (M.lookup i . files)
setFile i f = modify $ \state -> state { files = M.insert i f (files state) }
delFile i = modify $ \state -> state { files = M.delete i (files state) }

printTo i s = do
  Just f <- getFile i
  liftIO (filePutStrLn f s)

maybeGetLine i = liftIO . fileMaybeGetLine =<< fromJust <$> getFile i

hMaybeGetLine :: Handle -> IO (Maybe S)
hMaybeGetLine h = do
    eof <- hIsEOF h
    if eof then pure Nothing
           else Just <$> C.hGetLine h

forkIO_ :: StateT s IO () -> StateT s IO ()
forkIO_ m = unliftIO forkIO m >> return ()

unliftIO :: (IO b -> IO a) -> StateT s IO b -> StateT s IO a
unliftIO f m = do
  state <- get
  liftIO (f (evalStateT m state))

getLineOrEvent :: Int -> StateT (SedState p) IO (Either (Maybe S) S)
getLineOrEvent i = do
    state <- gets ipcState
    case state of
      Just state -> do
        let Mailbox v = box state
        forkIO_ (liftIO . putMVar v . Left =<< maybeGetLine i)
        liftIO $ takeMVar v
      Nothing -> do
        Left <$> maybeGetLine i

data Options = Options
  { extendedRegexps :: Bool
  , autoprint :: Bool
  , enableIPC :: Bool
  , scripts :: [Either S FilePath]
  , dumpParse :: Bool
  , dumpOptimizedIR :: Bool
  , dumpOriginalIR :: Bool
  , fuel :: Int
  } deriving (Show, Eq)
defaultOptions = Options
    { extendedRegexps = True
    , autoprint = True
    , enableIPC = True
    , scripts = []
    , dumpParse = False
    , dumpOptimizedIR = False
    , dumpOriginalIR = False
    , fuel = 1000000 }
addScript s o = o { scripts = Left (C.pack s) : scripts o }
addScriptFile f o = o { scripts = Right f : scripts o }
setFuel f o = o { fuel = f }

sedOptions =
  [ Option ['r', 'E'] ["regexp-extended"] (NoArg $ \o -> o { extendedRegexps = True }) "Use extended regexps (default, always enabled, only parsed for sed compatibility"
  , Option ['n'] ["quiet", "silent"] (NoArg $ \o -> o { autoprint = False }) "suppress automatic printing of pattern space"
  , Option ['e'] ["expression"] (ReqArg addScript "SCRIPT") "add the script to the commands to be executed"
  , Option ['f'] ["file"] (ReqArg addScriptFile "SCRIPT_FILE") "add the contents of script-file ot the commands to be executed"
  , Option ['I'] ["no-ipc"] (NoArg $ \o -> o { enableIPC = False}) "disable IPC"
  , Option [] ["dump-parse"] (NoArg $ \o -> o { dumpParse = True }) "don't run script, just parse and print the parsed program"
  , Option [] ["dump-ir"] (NoArg $ \o -> o { dumpOptimizedIR = True }) "don't run script, just compile and print post-optimization IR"
  , Option [] ["dump-ir-pre"] (NoArg $ \o -> o { dumpOriginalIR = True }) "don't run script, just compile and print pre-optimization IR"
  , Option ['O'] ["opt-fuel"] (ReqArg (setFuel . read) "FUEL") "override amount of optimization fuel for optimizations. -O0 to disable optimizations."
  -- Not implemented!
  -- , Option ['s'] ["sandbox"] (NoArg Sandbox) "Disable unsafe commands (WAR"
  ]

-- TODO Include source file/line info here, thread through to the parser...
flagScript :: Options -> IO [S]
flagScript Options { scripts = ss } = concat <$> mapM f ss
  where
    f (Left e) = return [e]
    f (Right f) = C.lines <$> C.readFile f

getScript :: Options -> [S] -> IO ([S], [S])
getScript options inputs = case scripts options of
  [] -> return ([head inputs], tail inputs)
  _ -> do
    ss <- flagScript options
    return (ss, inputs)

runProgram :: Bool -> (H.Label, Program) -> File -> IO ()
runProgram ipc (label, program) file0 = do
    state <- initialState ipc program file0
    evalStateT (runIRLabel label) state

do_main args = do
  let (optFuns,nonOpts,errors) = getOpt Permute sedOptions args
  let usage = usageInfo "Usage: sed [OPTION]... [SCRIPT] [INPUT]..." sedOptions
  when (not (null errors)) $ do
    mapM_ putStrLn (errors ++ [usage])
    exitFailure
  let opts@Options {..} = foldl (.) id optFuns defaultOptions

  (scriptLines,inputs) <- getScript opts (map C.pack nonOpts)
  let seds = parseString (C.unlines scriptLines)
  when dumpParse $ do
    mapM_ (hPrint stderr) seds
    exitSuccess
  let program = toIR autoprint seds
  when (dumpOriginalIR) $
      hPutStrLn stderr ("\n\n*** ORIGINAL: \n" ++ show program)
  let (program', remainingFuel) = optimize fuel program
  when (dumpOptimizedIR) $ do
      hPutStr stderr "\n\n*** OPTIMIZED: \n"
      hPutStrLn stderr (show program')
      hPutStrLn stderr ("Remaining fuel: " ++ show remainingFuel)
      hPutStrLn stderr ("Used fuel: " ++ show (fuel - remainingFuel))
  when (dumpOptimizedIR || dumpOriginalIR) exitSuccess

  file0 <- inputListFile (map C.unpack inputs)
  runProgram enableIPC (fst program,program') file0

main = do_main =<< getArgs
