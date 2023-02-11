{-# LANGUAGE OverloadedStrings, CPP, TypeFamilies, NamedFieldPuns, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Interpret (runProgram, inputListFile) where

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

import Network.Socket

import System.Exit
import System.IO
#if DEBUG
import System.IO.Unsafe
#endif
import System.Random

import Text.Printf (printf)
import Text.Regex.Posix hiding (match)

import AST
import Bus
import IR (Program)
import qualified IR

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

nullFile = NormalFile (pure True) (pure Nothing) (pure Nothing) (\_ -> pure ())

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

outputHandleFile h = nullFile { filePutStr = putstr }
  where
    putstr s = do
     C.hPutStr h s
     hFlush h -- TODO Close files on exit so their buffers get flushed. Probably requires adding some shutdown code?
inputHandleFile h = (rawHandleFile h h) { filePutStr = \_ -> return () }

outputFile path = outputHandleFile <$> openFile path WriteMode
inputFile path = inputHandleFile <$> openFile path ReadMode

fileFile write path = catch (f path) errorHandler
  where
    f | write     = outputFile
      | otherwise = inputFile
    errorHandler :: IOException -> IO File
    errorHandler _ = return nullFile

hMaybeGetLine :: Handle -> IO (Maybe S)
hMaybeGetLine h = do
    eof <- hIsEOF h
    if eof then pure Nothing
           else Just <$> C.hGetLine h

data RE = RE S Regex

instance Show RE where
  show (RE s _) = show s
instance Eq RE where
  RE s _ == RE t _ = s == t
instance Ord RE where
  compare (RE s _) (RE t _) = compare s t

type Match = [MatchArray]

data SedState program = SedState
  { program :: program
  , files :: Map Int File
  , lineNumber :: Int
  , lastRegex :: Maybe Int
  , predicates :: Set Int
  , strings :: Map Int S
  , matches :: Map Int Match
  , regexps :: Map Int RE

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

initialState ipc pgm file0 = do
  ipcState <- if ipc then Just <$> newIPCState else return Nothing
  return SedState {
    program = pgm
  , files = M.singleton 0 file0
  , lineNumber = 0
  , strings = M.empty
  , matches = M.empty
  , regexps = M.empty
  , lastRegex = Nothing
  , predicates = S.empty
  , ipcState = ipcState
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

setString :: IR.SVar -> S -> SedM ()
setString (IR.SVar n) value =
    modify $ \s -> s { strings = M.insert n value (strings s) }
-- TODO Figure out why synsedizer triggers a fromJust error here... we
-- shouldn't be reading unset strings...
getString (IR.SVar n) = gets (fromMaybe "" . M.lookup n . strings)

setMatch :: IR.MVar -> Match -> SedM ()
setMatch (IR.MVar n) value =
    modify $ \s -> s { matches = M.insert n value (matches s) }
getMatch (IR.MVar n) = gets (fromJust . M.lookup n . matches)

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
runIR (IR.SetP p cond) = setPred p =<< evalCond cond
runIR (IR.SetS s expr) = setString s =<< evalStringExpr expr
runIR (IR.SetM m expr) = setMatch m =<< case expr of
  IR.Match svar re -> checkRE svar =<< getRegex re
  IR.MatchLastRE svar -> checkRE svar =<< getLastRegex
  IR.NextMatch m2 _ -> tail <$> getMatch m2
  IR.MVarRef m2 -> getMatch m2
runIR (IR.AppendS s s2) = do
  a <- getString s
  b <- getString s2
  setString s (a <> b)
runIR (IR.If c t f) = do
  b <- evalCond c
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

runIR (IR.CompileRE re s ere) = setRegex re (compileRE s ere)
runIR (IR.SetLastRE re) = setLastRegex re
runIR (IR.Message s) = doMessage =<< getString s

runIR (IR.Print i s) = printTo i =<< getString s
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

runIR (IR.ReadFile svar i) = do
  setString svar =<< readWholeFile i
runIR (IR.OpenFile i write path) =
  setFile i =<< liftIO (fileFile write (C.unpack path))

runIR (IR.ShellExec svar) = do
    cmd <- getString svar
    fatal ("ShellExec not allowed (would run " ++ show cmd ++ ")")

--runIR cmd = fatal ("runIR: Unhandled instruction " ++ show cmd)

evalCond cond = case cond of
  IR.Bool b -> return b
  IR.Line l -> gets ((l ==) . lineNumber)
  IR.EndLine l -> gets ((l <) . lineNumber)
  IR.AtEOF fd -> liftIO . fileIsEOF =<< gets (fromJust . M.lookup fd . files)
  IR.PendingIPC -> hasPendingIPC =<< gets ipcState
  IR.IsMatch m -> not . null <$> getMatch m
  IR.PRef p -> getPred p

setRegex :: IR.RE -> RE -> SedM ()
setRegex (IR.RE n) re = modify $ \s -> s { regexps = f (regexps s) }
  -- TODO Map probably has one of these insert-but-don't-replace functions...
  where f rvars | Just _ <- M.lookup n rvars = rvars
                | otherwise                  = M.insert n re rvars

getRegex (IR.RE n) = gets (fromJust . M.lookup n . regexps)

setLastRegex (IR.RE n) = modify $ \state -> state { lastRegex = Just n }
getLastRegex :: SedM RE
getLastRegex = do
    last <- gets lastRegex
    case last of
      Just n  -> getRegex (IR.RE n)
      Nothing -> fatal "no previous regular expression"

compileRE :: S -> Bool -> RE
compileRE s ere = RE s (makeRegexOpts compOpt defaultExecOpt s)
  where
    compOpt | ere       = compExtended
            | otherwise = blankCompOpt

-- TODO Use matchOnce instead to avoid unnecessary work. (NextMatch handling
-- gets more tricky since it will need to know how to "continue" after a
-- previous match.)
checkRE svar (RE _ re) = matchAll re <$> getString svar

evalStringExpr :: IR.StringExpr -> SedM S
evalStringExpr (IR.SConst s) = return s
evalStringExpr (IR.SVarRef svar) = getString svar
evalStringExpr (IR.SRandomString) = liftIO randomString
evalStringExpr (IR.STrans from to str) =
    trans from to <$> getString str
-- TODO Should this do something special if 'a' is empty?
evalStringExpr (IR.SAppendNL a b) = do
    a <- getString a
    b <- getString b
    return (C.concat [a, "\n", b])
evalStringExpr (IR.SAppend a b) = do
    a <- getString a
    b <- getString b
    return (a <> b)
evalStringExpr (IR.SSubstring s start end) = do
  s <- getString s
  startix <- resolve start s
  endix <- resolve end s
  return (substring startix endix s)
  where
    substring start end = C.take (end - start) . C.drop start
    resolve IR.SIStart _ = return 0
    resolve IR.SIEnd   s = return (C.length s)
    resolve (IR.SIMatchStart m)   _ = groupStart 0 m
    resolve (IR.SIMatchEnd m)     _ = groupEnd 0 m
    resolve (IR.SIGroupStart m i) _ = groupStart i m
    resolve (IR.SIGroupEnd m i)   _ = groupEnd i m
    groupStart i m = fst . (! i) . head <$> getMatch m
    groupLen i m = snd . (! i) . head <$> getMatch m
    groupEnd i m = (+) <$> groupStart i m <*> groupLen i m
evalStringExpr (IR.SFormatLiteral w s) = formatLiteral w <$> getString s
evalStringExpr (IR.SGetLineNumber) = gets (C.pack . show . lineNumber)

-- TODO We ought to provide secure random numbers
randomString = C.pack <$> replicateM 32 (randomRIO ('A','Z'))

type SedPM p a = StateT (SedState p) IO a
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

trans :: S -> S -> S -> S
trans from to p = C.map f p
  where
    f c | Just i <- C.elemIndex c from = C.index to i
        | otherwise = c

-- C.init because Print appends a newline and this output always ends with a
-- newline. The added newline is relevant to get the correct $ at the end of
-- the formatted literal.
formatLiteral :: Int -> S -> S
formatLiteral width s = C.init (lineWrap width (C.lines (escape s <> "\n")))
  where
    escape = C.concatMap escapeChar
    escapeChar '\\' = "\\\\"
    escapeChar c | isPrint c && ord c < 128 = C.singleton c
                 | otherwise                = C.pack (printf "\\%03o" (ord c))

    lineWrap 0 ss = C.concat (map (<> eol) ss)
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

readWholeFile i = go True ""
  where
    go firstLine acc = do
      maybeLine <- maybeGetLine i
      case maybeLine of
        Just l -> go False (if firstLine then l else acc <> "\n" <> l)
        Nothing -> return acc

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

runProgram :: Bool -> (H.Label, Program) -> File -> IO ExitCode
runProgram ipc (label, program) file0 = do
    state <- initialState ipc program file0
    evalStateT (runIRLabel label) state
    return ExitSuccess
