{-# LANGUAGE OverloadedStrings, CPP, TypeFamilies #-}
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
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Data.Set (Set)

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
  = HandleFile { fileHandle :: Handle }
  | SocketFile Socket
  deriving (Show, Eq)
data SedState program = SedState
  { program :: program
  , files :: Map Int File
  , lineNumber :: Int
  , pattern :: Maybe S
  , hold :: Map S S

  , lastRegex :: Maybe RE

  , autoprint :: Bool

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

initialState autoprint ipc pgm = do
  ipcState <- if ipc then Just <$> newIPCState else return Nothing
  return SedState {
    program = pgm
  , files = M.empty
  , lineNumber = 0
  , pattern = Nothing
  , hold = M.empty
  , lastRegex = Nothing
  , autoprint = autoprint
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

runSed :: Bool -> Bool -> [Sed] -> IO ()
runSed autoprint ipc seds = do
    let program = toIR autoprint seds
    let program' = optimize program
    let body@(GMany (JustO e) _ _) = program'
    debug ("\n\n*** ORIGINAL: \n" ++ show program)
    debug ("\n\n*** OPTIMIZED: \n" ++ show program')
    state <- initialState autoprint ipc body
    evalStateT (runIRBlock e) state

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
  IR.Match re -> checkRE re
  IR.MatchLastRE -> checkRE . fromJust =<< gets lastRegex
  IR.AtEOF -> liftIH 0 hIsEOF
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

runIR cmd = fatal ("runIR: Unhandled instruction " ++ show cmd)

setLastRegex re = modify $ \state -> state { lastRegex = Just re }

checkRE (RE _ re) = do
  p <- pattern <$> get
  case p of
    Just p -> return (matchTest re p)
    _ -> return False

type SedPM p a = StateT (SedState p) IO a
type SedM a = SedPM (Graph IR.Insn O C) a

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
    replaceFile j (HandleFile h)

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

doGetAppend reg = do
  state <- get
  let p = fromMaybe "" (pattern state)
  let got = fromMaybe "" (M.lookup (fromMaybe "" reg) (hold state))
  debug ("GetA: appending " ++ show got ++ " to " ++ show p)
  modify $ \state -> state { pattern = Just (p <> "\n" <> got) }

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
    go acc _ [] = acc

    substr s l = C.take l (C.drop s p)
    replace rep match = go "" 0
      where
        go acc i | i == C.length rep = acc
        go acc i = case C.index rep i of
          '\\' -> go (acc <> matchN (digitToInt (C.index rep (i + 1)))) (i + 2)
          '&' -> go (acc <> matchN 0) (i + 1)
          c -> go (C.snoc acc c) (i + 1)
        matchN n = (uncurry substr) (match ! n)

match SubstFirst re p = case matchOnce re p of Just x -> [x]; Nothing -> []
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

getFile i = M.lookup i . files <$> get
setFile i f = modify $ \state -> state { files = M.insert i f (files state) }
delFile i = modify $ \state -> state { files = M.delete i (files state) }

ifile i state = fileHandle (M.findWithDefault (HandleFile stdin) i (files state))
ofile i state = fileHandle (M.findWithDefault (HandleFile stdout) i (files state))

liftIH i f = liftIO . f =<< ifile i <$> get
liftOH i f = liftIO . f =<< ofile i <$> get

printTo i s = liftOH i (\h -> C.hPutStrLn h s)

maybeGetLine i = liftIH i hMaybeGetLine

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

data Flag =
    -- Accepted but ignored, since this is already the default.
    ExtendedRegexps
  | Autoprint Bool
  | EnableIPC Bool
  | Script S
  | ScriptFile FilePath
  -- | Sandbox
  deriving Show

sedOptions =
  [ Option ['r', 'E'] ["regexp-extended"] (NoArg ExtendedRegexps) "Use extended regexps (default, always enabled, only parsed for sed compatibility"
  , Option ['n'] ["quiet", "silent"] (NoArg (Autoprint False)) "suppress automatic printing of pattern space"
  , Option ['e'] ["expression"] (ReqArg (Script . C.pack) "SCRIPT") "add the script to the commands to be executed"
  , Option ['f'] ["file"] (ReqArg ScriptFile "SCRIPT_FILE") "add the contents of script-file ot the commands to be executed"
  , Option ['I'] ["no-ipc"] (NoArg (EnableIPC False)) "disable IPC"
  -- Not implemented!
  -- , Option ['s'] ["sandbox"] (NoArg Sandbox) "Disable unsafe commands (WAR"
  ]

-- TODO Include source file/line info here, thread through to the parser...
flagScript :: Flag -> IO [S]
flagScript (Script e) = return [e]
flagScript (ScriptFile f) = C.lines <$> C.readFile f
flagScript _ = return []

getScript :: [Flag] -> [S] -> IO ([S], [S])
getScript flags inputs = do
  scripts <- concat <$> mapM flagScript flags
  if null scripts
    then return ([head inputs], tail inputs)
    else return (scripts, inputs)

getAutoprint [] def = def
getAutoprint (Autoprint ap:xs) _ = getAutoprint xs ap
getAutoprint (_:xs) def = getAutoprint xs def

getIPC [] def = def
getIPC (EnableIPC b:xs) _ = getIPC xs b
getIPC (_:xs) def = getIPC xs def

main = do_main =<< getArgs
do_main args = do
  let (opts,nonOpts,errors) = getOpt Permute sedOptions args
  let usage = usageInfo "Usage: sed [OPTION]... [SCRIPT] [INPUT]..." sedOptions
  when (not (null errors)) $ do
    mapM_ putStrLn (errors ++ [usage])
    exitFailure

  (scriptLines,inputs) <- getScript opts (map C.pack nonOpts)
  let pgm = parseString (C.unlines scriptLines)
  when (not (null inputs)) $ fatal "Input files not handled yet, only stdin"
  let autoprint = getAutoprint opts True
  let ipc = getIPC opts True
  runSed autoprint ipc pgm
