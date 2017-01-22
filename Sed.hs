{-# LANGUAGE OverloadedStrings, CPP #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

#define DEBUG 0
#define IPC 1

import Control.Applicative
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
import System.IO.Unsafe

import Text.Regex.TDFA hiding (match)

import AST
import Bus
import Parser

-- Just to make SedState Showable
newtype Mailbox a = Mailbox (MVar a)
instance Show (Mailbox a) where
    show _ = "Mailbox {}"

data BlockState = BlockN | BlockI | Block0 deriving (Show, Eq)
data File
  = HandleFile { fileHandle :: Handle }
  | SocketFile { fileSocket :: Socket }
  deriving (Show, Eq)
data SedState = SedState {
  program :: [Sed],
  files :: Map Int File,
  lineNumber :: Int,
  pattern :: Maybe S,
  -- hold "" is classic hold space
  hold :: Map S S,
  activeAddresses :: Set MaybeAddress,

  lastRegex :: Maybe RE,

  autoprint :: Bool,
  block :: BlockState,

#if IPC
  box :: Mailbox (Either (Maybe S) S),
  bus :: Bus S,
  passenger :: Passenger S,
#endif
  irq :: Bool

  -- Pending output? Other tricky stuff?
}
  deriving (Show)

#if DEBUG
putstrlock = unsafePerformIO (newMVar ())
debug s = withMVar putstrlock $ \() -> do
    t <- myThreadId
    System.IO.putStrLn (show t ++ ": " ++ s)
#else
debug _ = return ()
#endif
debugPrint x = debug (show x)

fatal msg = error ("ERROR: " ++ msg)

-- The wheels on the bus goes round and round...
busRider p b = forever $ putMVar b . Right =<< ride p

initialState autoprint pgm = do
  bus <- newBus
  passenger <- board bus
  box <- newEmptyMVar
  forkIO (busRider passenger box)
  return SedState {
    program = pgm,
    files = M.empty,
    lineNumber = 0,
    pattern = Nothing,
    hold = M.empty,
    activeAddresses = S.empty,
    lastRegex = Nothing,
    autoprint = autoprint,
    block = BlockN,
#if IPC
    box = Mailbox box,
    bus = bus,
    passenger = passenger,
#endif
    irq = False }
forkState pgm = get >>= \state -> liftIO $ do
#if IPC
  passenger <- board (bus state)
  box <- newEmptyMVar
  forkIO (busRider passenger box)
#endif
  return state {
    program = pgm
  , pattern = Nothing
  , activeAddresses = S.empty
  , lineNumber = 0
  , block = BlockN
#if IPC
  , passenger = passenger
  , box = Mailbox box
#endif
 }

runSed :: Bool -> [Sed] -> IO ()
runSed autoprint seds = evalStateT runProgram =<< initialState autoprint seds

addressActive addr = S.member addr . activeAddresses <$> get
modifyActiveAddresses f =
  modify $ \state -> state { activeAddresses = f (activeAddresses state) }
activateAddress addr = modifyActiveAddresses (S.insert addr)
deactivateAddress addr = modifyActiveAddresses (S.delete addr)

setLastRegex re = modify $ \state -> state { lastRegex = Just re }

check :: MaybeAddress -> SedM Bool
-- A bit of special casing here - unconditional statements should not be run
-- in the before-first or IRQ state unless they're inside a 0{} or I{} block.
-- runBlock updates and restores the BlockI/Block0 state.
-- This doesn't apply for unconditional *blocks* though - see runBlock below.
check Always = do
  state <- get
  case state of
   _ | irq state -> return (block state == BlockI)
     | 0 <- lineNumber state -> return (block state == Block0)
     -- On non-first lines, a missing pattern happens after 'd' (for example)
     -- treat these as matching too.
     | otherwise -> return True
check (At addr) = check1 addr
-- if active: check for end, deactivate, return true
-- if not active: check for start => activate, return true
-- otherwise: return false
check addr@(Between start end) = do
  active <- addressActive addr
  change <- check1 (if active then end else start)
  when change $ (if active then deactivateAddress else activateAddress) addr
  return (active || change)

-- EOF is checked lazily to avoid the start of each cycle blocking until after
-- at least one character of the next line has been read.
check1 EOF = liftIH 0 hIsEOF
check1 (Line expectedLine) = do
  state <- get
  return (lineNumber state == expectedLine && not (irq state))
check1 IRQ = irq <$> get
check1 (Match Nothing) = do
  lre <- lastRegex <$> get
  case lre of
    Just re -> checkRE re
    Nothing -> return False
check1 (Match (Just re)) = do
  setLastRegex re
  checkRE re

checkRE (RE _ re) = do
  p <- pattern <$> get
  case p of
    Just p -> return (matchTest re p)
    _ -> return False

-- Only the first one negates - series of ! don't double-negate.
-- run will traverse and ignore all NotAddr prefixes.
applyNot (NotAddr cmd) t = not t
applyNot cmd t = t

runProgram :: SedM ()
runProgram = do
  prog <- program <$> get
  runBlock prog (return ())

type SedM a = StateT SedState IO a

runBlock :: [Sed] -> SedM () -> SedM ()
runBlock [] k = newCycle 0 runProgram
-- Would be nice not to need this hack here, the rest of the conditional stuff
-- should be updated to work with this.
-- This makes it so that unconditional blocks are run even if the BlockI/0
-- state check would *not* run an unconditional statement now. The block might
-- then contain conditionals that do match.
runBlock (Sed Always (Block seds):ss) k =
    runBlock seds (runBlock ss k)
runBlock (Sed cond c:ss) k = do
    dorun <- check cond
    debug (show cond ++ " => " ++ show dorun ++ ": " ++ show c)
    -- If the address is one of these special addresses, then change the block
    -- state, then make sure to reset it to its previous value before running
    -- the next statement.
    -- Blocks run inside this block will inherit it and get the block-state
    -- popped once it gets back to the outer continuation.
    let setBlock b = modify $ \state -> state { block = b }
    oldBlock <- block <$> get
    setBlock $ case cond of
        At (Line 0) -> Block0
        At IRQ -> BlockI
        _ -> oldBlock
    let k' = setBlock oldBlock >> runBlock ss k
    if applyNot c dorun then run c k' else k'

run :: Cmd -> SedM () -> SedM ()
run c k = case c of
    Block seds -> runBlock seds k
    Fork sed -> do
        state <- forkState [sed]
        forkIO_ $ do
            debug ("start of fork")
            put state
            runProgram
            debug ("end of fork")
        debug ("parent is after fork")
        k
    NotAddr c -> run c k
    Label l -> k
    Branch Nothing -> do
        debug "branch: nothing"
        newCycle 0 runProgram
    Branch (Just l) -> runBranch l =<< program <$> get
    Next i -> newCycle i k
    Print i -> get >>= \state ->
        case pattern state of
          Just p -> printTo i p >> k
          _ -> k
    -- Delete should clear pattern space and start a new cycle (this avoids
    -- printing anything).
    Delete -> do
      modify $ \state -> state { pattern = Nothing }
      newCycle 0 runProgram
    Clear -> do
      modify $ \state -> state { pattern = Just "" }
      k

    Insert s -> do
      printTo 0 s
      k

    Listen i maybeHost port -> do
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
        k

    Accept i j -> do
        Just (SocketFile s) <- getFile i
        debug ("accepting from " ++ show i ++ " to " ++ show j)
        (c,addr) <- liftIO $ accept s
        debug ("accepted: " ++ show addr)
        h <- liftIO $ socketToHandle c ReadWriteMode
        replaceFile j (HandleFile h)
        k

    Redirect i (Just j) -> do
        f <- getFile j
        case f of
           Just f -> replaceFile i f >> delFile j
           Nothing -> closeFile i
        k
    Redirect i Nothing -> do
        f <- getFile i
        debug ("Closing " ++ show i ++ ": " ++ show f)
        closeFile i
        k

#if IPC
    Message msg -> do
        state <- get
        let m = case msg of
              Just m -> m
              Nothing -> fromJust (pattern state)
        debug ("Messaging " ++ show m)
        liftIO (drive (bus state) m)
        k
#endif

    Subst mre rep t action -> do
      state <- get
      -- Still a Maybe RE in case there was no previous regexp at all
      mre <- case mre of
           Just re -> setLastRegex re >> return (Just re)
           Nothing -> return (lastRegex state)
      case pattern state of
        -- matchAll if SubstGlobal is in flags
        Just p | Just (RE _ pat) <- mre, matches@(_:_) <- match t pat p -> do
          let newp = subst p rep matches
          debug ("Subst: " ++ show p ++ " => " ++ show newp)
          runSubAction action newp
          modify $ \state -> state { pattern = Just newp }
          k
        _ -> do
          debug ("Subst: no match in " ++ show (pattern state))
          k

    Quit print status -> do
      let exit = liftIO (exitWith status)
      if print then run (Print 0) exit else exit

    Hold reg -> do
      pat <- fromMaybe "" . pattern <$> get
      debug ("GetA: holding " ++ show pat ++ " in " ++ show reg)
      modify $ \state -> state { hold = M.insert (fromMaybe "" reg) pat (hold state) }
      k
    Get reg -> do
      modify $ \state -> state { pattern = Just (fromMaybe "" (M.lookup (fromMaybe "" reg) (hold state))) }
      k
    GetA reg -> do
      state <- get
      let p = fromMaybe "" (pattern state)
      let got = fromMaybe "" (M.lookup (fromMaybe "" reg) (hold state))
      debug ("GetA: appending " ++ show got ++ " to " ++ show p)
      modify $ \state -> state { pattern = Just (p <> "\n" <> got) }
      k

    _ -> liftIO (System.IO.putStrLn ("Unhandled command: " ++ show c) >> exitFailure)

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

runSubAction SActionNone _ = return ()
runSubAction SActionExec s = do
    debug ("TODO: Actually execute " ++ show s)
    return ()
runSubAction (SActionPrint i) s = printTo i s

match SubstFirst re p = case matchOnce re p of Just x -> [x]; Nothing -> []
match SubstAll re p = matchAll re p
-- TODO Handle not finding enough matches for match i. Should be handled the
-- same as a nonmatch.
match (SubstNth i) re p = [matchAll re p !! i]

getFile i = M.lookup i . files <$> get
closeFile i = do
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

forkIO_ :: SedM () -> SedM ()
forkIO_ m = unliftIO forkIO m >> return ()

unliftIO :: (IO b -> IO a) -> SedM b -> SedM a
unliftIO f m = do
  state <- get
  liftIO (f (evalStateT m state))

-- Read a new input line, then run k if input was available or return ()
-- directly if we've reached EOF.
-- For 'n' (read input and continue execution), k is the next-command
-- continuation. For the end-of-cycle or 'b' (t/T) without target, k is instead
-- runProgram so that it restarts the whole program.
newCycle i k = do
    get >>= \state -> debug ("new cycle: -- state = " ++ show state)
    next i $ do
        get >>= \state -> debug ("new cycle: => state = " ++ show state)
        k
    debug ("new cycle: exiting")

next i k = do
    state <- get
    case pattern state of
        Just t | autoprint state && not (irq state) ->
            printTo 0 t
        _ -> return ()
#if IPC
    -- if we successfully got an IRQ for last cycle, that means we're already
    -- running an asynchronous getLine and shouldn't start another.
    let Mailbox v = box state
    when (not (irq state)) $
      forkIO_ (liftIO . putMVar v . Left =<< maybeGetLine i)
    lineOrEvent <- liftIO $ takeMVar v
#else
    lineOrEvent <- Left <$> maybeGetLine i
#endif
    debug ("next: " ++ show lineOrEvent)
    case lineOrEvent of
      Left Nothing -> return ()
      Left (Just l) -> do
            modify $ \state -> state { pattern = Just l, lineNumber = 1 + lineNumber state,
                        irq = False }
            k
      Right l -> do
            modify $ \state -> state { pattern = Just l, irq = True }
            k

runBranch l ss = go ss failed
  where
    go (s:ss) fail = case s of
      Sed _ (Label m) | l == m -> runBlock ss (return ())
      Sed _ (Block ss') -> go ss' (go ss fail)
      _ -> go ss fail
    go [] fail = fail
    failed = fatal ("Label " ++ show l ++ " not found")

runSedString autoprint = runSed autoprint . parseString

runSedFile autoprint f = do
    pgm <- parseString <$> C.readFile f
    debugPrint pgm
    runSed autoprint pgm

data Flag =
    -- Accepted but ignored, since this is already the default.
    ExtendedRegexps
  | Autoprint Bool
  | Script S
  | ScriptFile FilePath
  -- | Sandbox
  deriving Show

sedOptions =
  [ Option ['r', 'E'] ["regexp-extended"] (NoArg ExtendedRegexps) "Use extended regexps (default, always enabled, only parsed for sed compatibility"
  , Option ['n'] ["quiet", "silent"] (NoArg (Autoprint False)) "suppress automatic printing of pattern space"
  , Option ['e'] ["expression"] (ReqArg (Script . C.pack) "SCRIPT") "add the script to the commands to be executed"
  , Option ['f'] ["file"] (ReqArg ScriptFile "SCRIPT_FILE") "add the contents of script-file ot the commands to be executed"
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

main = do
  args <- getArgs
  let (opts,nonOpts,errors) = getOpt Permute sedOptions args
  let usage = usageInfo "Usage: sed [OPTION]... [SCRIPT] [INPUT]..." sedOptions
  when (not (null errors)) $ do
    mapM_ putStrLn (errors ++ [usage])
    exitFailure

  (scriptLines,inputs) <- getScript opts (map C.pack nonOpts)
  let pgm = parseString (C.unlines scriptLines)
  when (not (null inputs)) $ fatal "Input files not handled yet, only stdin"
  let autoprint = getAutoprint opts True
  runSed autoprint pgm
