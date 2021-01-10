{-# LANGUAGE OverloadedStrings, CPP, TypeFamilies, NamedFieldPuns, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Sed (main) where

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
import System.Random

import Text.Printf (printf)
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
  = NormalFile { fileIsEOF :: IO Bool, fileMaybeGetLine :: IO (Maybe S), filePutStr :: S -> IO () }
  | SocketFile Socket

instance Show File where
  show (NormalFile _ _ _) = "NormalFile{}"
  show (SocketFile s) = "SocketFile " ++ show s

handleFile h = NormalFile (hIsEOF h) (hMaybeGetLine h) (C.hPutStr h)
inputListFile :: [FilePath] -> IO File
inputListFile [] = return (NormalFile (hIsEOF stdin) (hMaybeGetLine stdin) C.putStr)
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
    return (NormalFile isEOF maybeGetLine C.putStr)

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

runIR (IR.Trans from to) = do
  state <- get
  case pattern state of
    Just p -> modify $ \state -> state { pattern = Just (trans from to p) }
    _ -> fatal "Trans: no pattern when substituting?"

runIR (IR.Message Nothing) = doMessage . fromJust =<< gets pattern
runIR (IR.Message (Just s)) = doMessage s

runIR (IR.PrintS i s) = printTo i s
runIR (IR.Print i) = get >>= \state ->
    case pattern state of
        Just p -> printTo i p
        _ -> return ()
runIR (IR.PrintLiteral w i) = get >>= \state ->
    case pattern state of
        Just p -> putStrTo i (formatLiteral w p)
        _ -> return ()
runIR (IR.PrintLineNumber i) = do
    l <- gets lineNumber
    printTo i (C.pack (show l))
runIR (IR.Change s) = modify $ \state -> state { pattern = Just s }
runIR (IR.Hold reg) = doHold reg
runIR (IR.HoldA reg) = doHoldAppend reg
runIR (IR.Get reg) = doGet reg
runIR (IR.GetA reg) = doGetAppend reg
runIR (IR.Exchange reg) = doExchange reg
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
  setRegValue reg pat
doGet (Just "yhjulwwiefzojcbxybbruweejw") = patternSet =<< liftIO randomString
doGet reg = patternSet =<< getRegValue reg

doGetAppend = patternAppend <=< getRegValue
doHoldAppend reg = do
  pat <- fromMaybe "" . pattern <$> get
  prev <- gets (M.lookup (fromMaybe "" reg) . hold)
  setRegValue reg $ case prev of
    Nothing -> pat
    Just value -> C.concat [value, "\n", pat]

doExchange reg = do
  pat <- fromMaybe "" . pattern <$> get
  held <- getRegValue reg
  setRegValue reg pat
  patternSet held

setRegValue reg value =
  modify $ \s -> s { hold = M.insert (fromMaybe "" reg) value (hold s) }
getRegValue reg = gets (fromMaybe "" . M.lookup (fromMaybe "" reg) . hold)
-- TODO We ought to provide secure random numbers
randomString = C.pack <$> replicateM 32 (randomRIO ('A','Z'))

patternAppend s = do
  p <- gets (fromMaybe "" . pattern)
  debug ("appending " ++ show s ++ " to " ++ show p)
  patternSet (p <> "\n" <> s)

patternSet :: S -> SedM ()
patternSet p = modify $ \s -> s { pattern = Just p }

subst :: S -> Replacement -> [MatchArray] -> S
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
    replace rep match = C.concat (map replace1 rep)
      where
        replace1 (Literal s) = s
        replace1 WholeMatch  = group 0
        replace1 (BackReference i) = group i
        group n = (uncurry substr) (match ! n)

match SubstFirst re p = take 1 (matchAll re p)
match SubstAll re p = matchAll re p
match (SubstNth i) re p = take 1 . drop (i - 1) $ matchAll re p

trans :: S -> S -> S -> S
trans from to p = C.map f p
  where
    f c | Just i <- C.elemIndex c from = C.index to i
        | otherwise = c

formatLiteral :: Int -> S -> S
formatLiteral width s = lineWrap width (C.lines (C.append (escape s) "\n"))
  where
    escape = C.concatMap escapeChar
    escapeChar '\\' = "\\\\"
    escapeChar c | isPrint c = C.singleton c
                 | otherwise = C.pack (printf "\\%03o" (ord c))

    lineWrap 0 ss = C.concat (map (flip C.append eol) ss)
    lineWrap width ss = C.concat (concatMap (wrap width) ss)

    eol = "$\n"
    cont = "\\\n"
    wrap width s | C.null s2 = [s1, eol]
                 | otherwise = s1 : cont : wrap width s2
      where
        (s1,s2) = C.splitAt (width - 1) s

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

printTo i s = putStrTo i (C.append s "\n")

putStrTo i s = do
  Just f <- getFile i
  liftIO (filePutStr f s)

incrementLineNumber =
    modify $ \state -> state { lineNumber = lineNumber state + 1 }

maybeGetLine :: Int -> StateT (SedState p) IO (Maybe S)
maybeGetLine i = do
    maybeLine <- liftIO . fileMaybeGetLine =<< fromJust <$> getFile i
    case maybeLine of
     Just l | 0 <- i -> incrementLineNumber >> return (Just l)
     _ -> return maybeLine

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
  [ Option ['r', 'E'] ["regexp-extended"] (NoArg $ \o -> o { extendedRegexps = True }) "Use extended regexps (default, always enabled, only parsed for sed compatibility)"
  , Option ['n'] ["quiet", "silent"] (NoArg $ \o -> o { autoprint = False }) "suppress automatic printing of pattern space"
  , Option ['e'] ["expression"] (ReqArg addScript "SCRIPT") "add the script to the commands to be executed"
  , Option ['f'] ["file"] (ReqArg addScriptFile "SCRIPT_FILE") "add the contents of script-file to the commands to be executed"
  , Option ['I'] ["no-ipc"] (NoArg $ \o -> o { enableIPC = False}) "disable IPC"
  , Option [] ["dump-parse"] (NoArg $ \o -> o { dumpParse = True }) "don't run script, just parse and print the parsed program"
  , Option [] ["dump-ir"] (NoArg $ \o -> o { dumpOptimizedIR = True }) "don't run script, just compile and print post-optimization IR"
  , Option [] ["dump-ir-pre"] (NoArg $ \o -> o { dumpOriginalIR = True }) "don't run script, just compile and print pre-optimization IR"
  , Option ['O'] ["opt-fuel"] (ReqArg (setFuel . read) "FUEL") "override amount of optimization fuel for optimizations. -O0 to disable optimizations."
  , Option ['s'] ["separate"] (NoArg id) "Unimplemented GNU feature: treat files as separate rather than a single continuous stream"
  -- Not implemented!
  -- , Option [] ["sandbox"] (NoArg Sandbox) "operate in sandbox mode (unimplemented GNU sed feature)"
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
  let (entryLabel, program) = toIR autoprint seds
  when (dumpOriginalIR) $
      hPutStrLn stderr ("\n\n*** ORIGINAL: (entry point " ++ show entryLabel ++ ")\n" ++ show program)
  let (program', remainingFuel) = optimize fuel (entryLabel, program)
  when (dumpOptimizedIR) $ do
      hPutStr stderr ("\n\n*** OPTIMIZED: (entry point " ++ show entryLabel ++ ")\n")
      hPutStrLn stderr (show program')
      hPutStrLn stderr ("Remaining fuel: " ++ show remainingFuel)
      hPutStrLn stderr ("Used fuel: " ++ show (fuel - remainingFuel))
  when (dumpOptimizedIR || dumpOriginalIR) exitSuccess

  file0 <- inputListFile (map C.unpack inputs)
  runProgram enableIPC (entryLabel,program') file0

main = do_main =<< getArgs
