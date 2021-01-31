{-# LANGUAGE OverloadedStrings, CPP, TypeFamilies, NamedFieldPuns, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Sed (main) where

#define DEBUG 0

import Compiler.Hoopl as H hiding ((<*>))

import Control.Concurrent
import Control.Exception
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
import Data.Time

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
  = NormalFile {
    -- Check if file is at EOF. May require reading one more character and may
    -- thus block, but doesn't have to read the whole line.
    fileIsEOF :: IO Bool,
    -- Get a line or return Nothing if at EOF.
    fileMaybeGetLine :: IO (Maybe S),
    -- Read a fulle line like fileMaybeGetLine but don't consume the line
    -- returned until another call to fileMaybeGetLine.
    filePeekLine :: IO (Maybe S),
    -- Output a string (without newline at the end)
    filePutStr :: S -> IO ()
  }
  | SocketFile Socket

instance Show File where
  show (NormalFile {}) = "NormalFile{}"
  show (SocketFile s) = "SocketFile " ++ show s

rawHandleFile :: Handle -> Handle -> File
rawHandleFile inh outh = NormalFile (hIsEOF inh) (hMaybeGetLine inh) (error "filePeekLine in rawHandleFile") (C.hPutStr outh)
handleFile :: Handle -> Handle -> IO File
handleFile inh outh = threadedFile (rawHandleFile inh outh)

threadedFile :: File -> IO File
threadedFile file@NormalFile{} = do
    nextLine :: MVar (Maybe S) <- newEmptyMVar

    let readThread :: IO ()
        readThread = do
            line <- fileMaybeGetLine file
            putMVar nextLine line
            -- Stop reading on EOF
            when (isJust line) readThread

        maybeGetLine :: IO (Maybe S)
        maybeGetLine = takeMVar nextLine

        peekLine :: IO (Maybe S)
        peekLine = readMVar nextLine

        isEOF :: IO Bool
        isEOF = isNothing <$> readMVar nextLine

    _ <- forkIO readThread
    return (NormalFile isEOF maybeGetLine peekLine (filePutStr file))
threadedFile (SocketFile _) = error "Can't wrap a server socket in a threaded file"

inputListFile :: [FilePath] -> IO File
inputListFile [] = handleFile stdin stdout
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
    threadedFile (NormalFile isEOF maybeGetLine (error "filePeekLine in inputListFile") C.putStr)

hMaybeGetLine :: Handle -> IO (Maybe S)
hMaybeGetLine h = do
    eof <- hIsEOF h
    if eof then pure Nothing
           else Just <$> C.hGetLine h

data SedState program = SedState
  { program :: program
  , files :: Map Int File
  , lineNumber :: Int
  , lastRegex :: Maybe RE
  , extendedRegex :: Bool
  , predicates :: Set Int
  , strings :: Map Int S

  , ipcState :: Maybe IPCState
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

initialState ipc ere pgm file0 = do
  ipcState <- if ipc then Just <$> newIPCState else return Nothing
  return SedState {
    program = pgm
  , files = M.singleton 0 file0
  , lineNumber = 0
  , strings = M.empty
  , lastRegex = Nothing
  , predicates = S.empty
  , ipcState = ipcState
  , extendedRegex = ere
  }
forkState pgm = get >>= \state -> liftIO $ do
  ipcState' <- forkIPCState (ipcState state)
  return state {
    program = pgm
  , lineNumber = 0
  , predicates = S.empty
  , ipcState = ipcState'
 }

setPred (IR.Pred n) b = modify $ \s -> s { predicates = f (predicates s) }
  where
    f | b = S.insert n
      | otherwise = S.delete n
getPred (IR.Pred n) = S.member n . predicates <$> get

setString (IR.SVar n) value =
    modify $ \s -> s { strings = M.insert n value (strings s) }
getString (IR.SVar n) = gets (fromMaybe "" . M.lookup n . strings)

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
runIR (IR.SetP p cond) = setPred p =<< case cond of
  IR.Bool b -> return b
  IR.Line l -> gets ((l ==) . lineNumber)
  IR.EndLine l -> gets ((l <) . lineNumber)
  IR.Match svar re -> checkRE svar re
  IR.MatchLastRE svar -> checkRE svar =<< getLastRegex
  IR.AtEOF fd -> liftIO . fileIsEOF =<< gets (fromJust . M.lookup fd . files)
  IR.PendingIPC -> hasPendingIPC =<< gets ipcState
runIR (IR.SetS s expr) = setString s =<< evalStringExpr expr
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
runIR (IR.Message s) = doMessage =<< getString s

runIR (IR.PrintConstS i s) = printTo i s
runIR (IR.Print i s) = printTo i =<< getString s
runIR (IR.PrintLiteral w i s) = do
    p <- getString s
    putStrTo i (formatLiteral w p)
runIR (IR.PrintLineNumber i) = do
    l <- gets lineNumber
    printTo i (C.pack (show l))
runIR (IR.Quit code) = liftIO (exitWith code)
runIR (IR.Comment s) = debug ("*** " ++ s)

runIR (IR.Wait i) = waitLineOrEvent i
runIR (IR.Read svar i) = do
  l <- maybeGetLine i
  case l of
   Just s -> setString svar s
   Nothing -> liftIO exitSuccess -- TODO EOF should be visible to the program rather than exiting directly.
runIR (IR.GetMessage svar) = do
    state <- gets (fromJust . ipcState)
    let Mailbox v = box state
    Right message <- liftIO (takeMVar v)
    setString svar message

-- Not quite right - all referenced files should be created/truncated before
-- the first written line, then all subsequent references continue writing
-- without reopening the file.
-- Probably the IR step should assign a file descriptor for each used output
-- file, generate code to open them on startup and then this should be done
-- through (Print fd) instead.
runIR (IR.WriteFile path svar) = do
  s <- getString svar
  liftIO $ C.appendFile (C.unpack path) (C.append s "\n")

runIR (IR.ShellExec svar) = do
    cmd <- getString svar
    fatal ("ShellExec not allowed (would run " ++ show cmd ++ ")")

--runIR cmd = fatal ("runIR: Unhandled instruction " ++ show cmd)

setLastRegex re = modify $ \state -> state { lastRegex = Just re }
getLastRegex :: StateT (SedState p) IO RE
getLastRegex = gets $ \SedState { lastRegex = last } -> case last of
    Just re -> re
    Nothing -> fatal "no previous regular expression"

checkRE svar (RE _ bre ere) = do
  p <- getString svar
  re <- gets (selectRegex bre ere . extendedRegex)
  return (matchTest re p)

selectRegex _ ere True = ere
selectRegex bre _ False = bre

evalStringExpr (IR.SConst s) = return s
evalStringExpr (IR.SVarRef svar) = getString svar
evalStringExpr (IR.SRandomString) = liftIO randomString
evalStringExpr (IR.SSubst svar sub stype) = substitute sub stype =<< getString svar
evalStringExpr (IR.STrans from to str) =
    trans from to <$> getString str
-- TODO Should this do something special if 'a' is empty?
evalStringExpr (IR.SAppendNL a b) = do
    a <- getString a
    b <- getString b
    return (C.concat [a, "\n", b])

-- TODO We ought to provide secure random numbers
randomString = C.pack <$> replicateM 32 (randomRIO ('A','Z'))

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
    replaceFile j =<< liftIO (handleFile h h)

doMessage m = gets ipcState >>= f
  where
    f Nothing = return ()
    f (Just ipcState) =
      do
        debug ("Messaging " ++ show m)
        liftIO (drive (bus ipcState) m)

substitute sub stype p = do
  (RE _ bre ere) <- getLastRegex
  useExtRE <- gets extendedRegex
  let pat = selectRegex bre ere useExtRE
  let matches@(_:_) = match stype pat p
  let newp = subst p sub matches
  debug ("Subst: " ++ show p ++ " => " ++ show newp)
  return newp

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

peekLine :: Int -> StateT (SedState p) IO (Maybe S)
peekLine i = do
    liftIO . filePeekLine =<< fromJust <$> getFile i

forkIO_ :: StateT s IO () -> StateT s IO ()
forkIO_ m = unliftIO forkIO m >> return ()

unliftIO :: (IO b -> IO a) -> StateT s IO b -> StateT s IO a
unliftIO f m = do
  state <- get
  liftIO (f (evalStateT m state))

waitLineOrEvent :: Int -> StateT (SedState p) IO ()
waitLineOrEvent i = do
    state <- gets ipcState
    case state of
      Just state -> do
        let Mailbox v = box state
        forkIO_ (liftIO . putMVar v . Left =<< peekLine i)
        liftIO (() <$ takeMVar v)
      Nothing -> () <$ peekLine i

hasPendingIPC (Just (IPCState { box = Mailbox mvar })) = do
    val <- liftIO (tryTakeMVar mvar)
    case val of
      Just (Right _) -> return True
      _ -> return False
hasPendingIPC _ = return False

data Options = Options
  { extendedRegexps :: Bool
  , autoprint :: Bool
  , enableIPC :: Bool
  , scripts :: [Either S FilePath]
  , dumpParse :: Bool
  , dumpOptimizedIR :: Bool
  , dumpOriginalIR :: Bool
  , timeIt :: Bool
  , fuel :: Int
  } deriving (Show, Eq)
defaultOptions = Options
    { extendedRegexps = False
    , autoprint = True
    , enableIPC = True
    , scripts = []
    , dumpParse = False
    , dumpOptimizedIR = False
    , dumpOriginalIR = False
    , timeIt = False
    , fuel = 1000000 }
addScript s o = o { scripts = Left (C.pack s) : scripts o }
addScriptFile f o = o { scripts = Right f : scripts o }
setFuel f o = o { fuel = f }

sedOptions =
  [ Option ['r', 'E'] ["regexp-extended"] (NoArg $ \o -> o { extendedRegexps = True }) "Use extended regexps"
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
  , Option ['t'] ["time"] (NoArg $ \o -> o { timeIt = True }) "Time optimization and execution of the program"
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

runProgram :: Bool -> Bool -> (H.Label, Program) -> File -> IO ExitCode
runProgram ipc ere (label, program) file0 = do
    state <- initialState ipc ere program file0
    evalStateT (runIRLabel label) state
    return ExitSuccess

timestamp :: IO UTCTime
timestamp = getCurrentTime

reportTime :: String -> UTCTime -> UTCTime -> IO ()
reportTime label start end = do
    hPutStrLn stderr (printf "%32s %.3fs" label (realToFrac (diffUTCTime end start) :: Double))

do_main args = do
  let (optFuns,nonOpts,errors) = getOpt Permute sedOptions args
  let usage = usageInfo "Usage: sed [OPTION]... [SCRIPT] [INPUT]..." sedOptions
  when (not (null errors)) $ do
    mapM_ putStrLn (errors ++ [usage])
    exitFailure
  let opts@Options {..} = foldl (.) id optFuns defaultOptions

  (scriptLines,inputs) <- getScript opts (map C.pack nonOpts)

  tStartParse <- timestamp
  let seds = parseString (C.unlines scriptLines)
  tEndParse <- seds `seq` timestamp

  when dumpParse $ do
    mapM_ (hPrint stderr) seds
    exitSuccess

  tStartGenerateIR <- timestamp
  let (entryLabel, program) = toIR autoprint seds
  tEndGenerateIR <- program `seq` timestamp

  when (dumpOriginalIR) $
      hPutStrLn stderr ("\n\n*** ORIGINAL: (entry point " ++ show entryLabel ++ ")\n" ++ show program)

  tStartOpt <- timestamp
  let (program', remainingFuel)
          | fuel > 0  = optimize fuel (entryLabel, program)
          | otherwise = (program, fuel)
  tEndOpt <- program' `seq` timestamp

  when (dumpOptimizedIR) $ do
      hPutStr stderr ("\n\n*** OPTIMIZED: (entry point " ++ show entryLabel ++ ")\n")
      hPutStrLn stderr (show program')
      hPutStrLn stderr ("Remaining fuel: " ++ show remainingFuel)
      hPutStrLn stderr ("Used fuel: " ++ show (fuel - remainingFuel))
  when (dumpOptimizedIR || dumpOriginalIR) exitSuccess

  when timeIt $ do
    reportTime "Parsing" tStartParse tEndParse
    reportTime "Generate IR" tStartGenerateIR tEndGenerateIR
    reportTime "Optimize" tStartOpt tEndOpt

  tProgStart <- timestamp
  file0 <- inputListFile (map C.unpack inputs)
  status <- catch
    (runProgram enableIPC extendedRegexps (entryLabel,program') file0)
    return
  tProgEnd <- timestamp

  when timeIt $ do
    reportTime "Running" tProgStart tProgEnd

  exitWith status

main = do_main =<< getArgs
