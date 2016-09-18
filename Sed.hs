{-# LANGUAGE OverloadedStrings, CPP #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

import Control.Applicative
import Control.Concurrent
import Control.Monad

import Data.ByteString.Char8 as C
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe

import Network.Socket

import System.IO
import System.IO.Unsafe

import AST
import Parser

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
  -- Probably the wrong model for these.
  -- Consider one /foo/,/bar/ address and one /foo/,/baz/ address - pretty much
  -- each line should have its own state for whether it's still triggered.
  activeAddresses :: [Address],
  autoprint :: Bool

  -- Pending output? Other tricky stuff?
}
  deriving (Show)

#define DEBUG 0
#if DEBUG
putstrlock = unsafePerformIO (newMVar ())
debug s = withMVar putstrlock $ \() -> do
    t <- myThreadId
    System.IO.putStrLn (show t ++ ": " ++ s)
#else
debug _ = return ()
#endif

fatal msg = error ("ERROR: " ++ msg)

initialState pgm = SedState pgm M.empty 0 Nothing M.empty [] True
forkState state pgm = state { program = pgm, pattern = Nothing, lineNumber = 0 }

runSed :: [Sed] -> IO ()
runSed seds = runProgram (initialState seds)

-- TODO Should not run anything on line 0 (before-first) unless it matches it
-- explicitly. Also should not run normal code in interrupt context.
-- Note though that we *should* run this code if it's contained inside a matching
-- 0{ or I{ block!
check Always _ = return True
check (At (Line expectedLine)) (SedState { lineNumber = actualLine })
    = return (expectedLine == actualLine)
check (At EOF) state = hIsEOF (ifile 0 state)

-- Only the first one negates - series of ! don't double-negate.
-- run will traverse and ignore all NotAddr prefixes.
applyNot (NotAddr cmd) t = not t
applyNot cmd t = t

runProgram :: SedState -> IO ()
runProgram state = runBlock (program state) state (const (return ()))

-- Read a new input line, then run k if input was available or return ()
-- directly if we've reached EOF.
-- For 'n' (read input and continue execution), k is the next-command
-- continuation. For the end-of-cycle or 'b' (t/T) without target, k is instead
-- runProgram so that it restarts the whole program.
newCycle state k = do
    debug ("new cycle: -- state = " ++ show state)
    res <- next 0 state
    debug ("new cycle: => state = " ++ show res)
    case res of
        Just state -> k state
        Nothing -> debug ("new cycle: exiting")

runBlock :: [Sed] -> SedState -> (SedState -> IO ()) -> IO ()
runBlock [] state k = newCycle state runProgram
runBlock (Sed cond c:ss) state k = do
    dorun <- check cond state
    debug (show cond ++ " => " ++ show dorun ++ ": " ++ show c)
    let k' state = runBlock ss state k
    if applyNot c dorun then run c state k' else k' state

run :: Cmd -> SedState -> (SedState -> IO ()) -> IO ()
run c state k = case c of
    Block seds -> runBlock seds state k
    Fork sed -> do
        forkIO $ do
            debug ("start of fork")
            runProgram (forkState state [sed])
            debug ("end of fork")
        debug ("parent is after fork")
        k state
    NotAddr c -> run c state k
    Label l -> k state
    Branch Nothing -> do
        debug "branch: nothing"
        newCycle state runProgram
    Branch (Just l) -> runBranch l (program state) state
    Next i -> newCycle state k
    -- TODO Does this restart? Clear the pattern space after printing? Restart?
    Print i -> do
        C.hPutStrLn (ofile i state) (fromJust (pattern state))
        k state
    Delete -> k state { pattern = Nothing }
    Listen i maybeHost port -> do
        let hints = defaultHints { addrFlags = [AI_PASSIVE], addrSocketType = Stream }
        let maybeHost' = fmap C.unpack maybeHost
        addr:_ <- getAddrInfo (Just hints) maybeHost' (Just (show port))
        s <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
        setSocketOption s ReuseAddr 1
        bind s (addrAddress addr)
        listen s 7
        debug ("now listening on " ++ show i)
        k =<< replaceFile i (SocketFile s) state
    Accept i j -> do
        let Just (SocketFile s) = getFile i state
        debug ("accepting from " ++ show i ++ " to " ++ show j)
        (c,addr) <- accept s
        debug ("accepted: " ++ show addr)
        h <- socketToHandle c ReadWriteMode
        k =<< replaceFile j (HandleFile h) state
    Redirect i (Just j) -> do
        state <- case getFile j state of
            Just f -> delFile j =<< replaceFile i f state
            Nothing -> closeFile i state
        k state
    Redirect i Nothing -> do
        debug ("Closing " ++ show i ++ ": " ++ show (getFile i state))
        k =<< closeFile i state

getFile i state = M.lookup i (files state)
closeFile i state = do
    {- The underlying socket/files may be used by other threads, so don't
    -- actually close them. Let them be garbage collected instead.
    case M.lookup i (files state) of
        --Just (SocketFile s) -> sClose s
        --Just (HandleFile h) -> hClose h
        _ -> return ()
    -}
    delFile i state
replaceFile i f state = do
    state <- closeFile i state
    setFile i f state
setFile i f state = return state { files = M.insert i f (files state) }
delFile i state = return state { files = M.delete i (files state) }
ifile i state = fileHandle (M.findWithDefault (HandleFile stdin) i (files state))
ofile i state = fileHandle (M.findWithDefault (HandleFile stdout) i (files state))

next i state = do
    case pattern state of
        Just t | autoprint state -> C.hPutStrLn (ofile 0 state) t
        _ -> return ()
    let h = ifile i state
    eof <- hIsEOF h
    debug ("next: eof=" ++ show eof)
    case eof of
        True -> return Nothing
        False -> do
            l <- Just <$> C.hGetLine h
            return $ Just state { pattern = l, lineNumber = 1 + lineNumber state }

runBranch l (s:ss) state = case s of
    Sed _ (Label m) | l == m -> runBlock ss state (const (return ()))
    _ -> runBranch l ss state
runBranch l [] state = fatal ("Label " ++ show l ++ " not found")

-- TODO This single-threaded acceptor probably doesn't scale. What I would like
-- is to fork one thread per capability, all running accept. A special fork
-- command for forking "to each cpu"?
echoServer = C.unlines $
  [ "0 L1:2007"
  , ":loop"
  , "A1 2"
  , "f 0 < 0 2"
  , "< 2"
  , "bloop" ]

cat = ""

runSedString = runSed . parseString

runSedFile f = do
    pgm <- parseString <$> C.readFile f
    print pgm
    runSed pgm

--main = runSedString echoServer
main = runSedFile "examples/chatroulette.xed"
