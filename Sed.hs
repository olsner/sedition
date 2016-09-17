{-# LANGUAGE OverloadedStrings #-}

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

putstrlock = unsafePerformIO (newMVar ())
debug s = return () -- withMVar putstrlock (\() -> System.IO.putStrLn s)

fatal msg = error ("ERROR: " ++ msg)

initialState pgm = SedState pgm M.empty 0 Nothing M.empty [] True
forkState state pgm = state { program = pgm, pattern = Nothing, lineNumber = 0 }

runSed :: [Sed] -> IO ()
runSed seds = runProgram (initialState seds) >> return ()

check Always _ = return True
check (At (Line expectedLine)) (SedState { lineNumber = actualLine })
    = return (expectedLine == actualLine)
check (At EOF) state = hIsEOF (ifile 0 state)

-- Only the first one negates - series of ! don't double-negate.
-- run will traverse and ignore all NotAddr prefixes.
applyNot (NotAddr cmd) t = not t
applyNot cmd t = t

runProgram state = runBlock (program state) state
runBlock (Sed cond s:ss) state = do
    dorun <- check cond state
    state <- if applyNot s dorun then run s state else return state
    runBlock ss state
runBlock [] state = do
    res <- next 0 state
    debug ("looped: state = " ++ show res)
    case res of
        Just state -> runProgram state
        Nothing -> return state
run :: Cmd -> SedState -> IO SedState
run c state = case c of
    Block seds -> runBlock seds state
    Fork sed -> do
        forkIO (runProgram (forkState state [sed]) >> return ())
        debug ("parent is after fork")
        return state
    NotAddr c -> run c state
    Label l -> return state
    Branch l -> runBranch l (program state) state
    -- TODO 'n' autoprints if not disabled, *then* reads a new input line
    Next i -> do
        res <- next i state
        case res of
            Just state -> return state
            Nothing -> return state
    Listen i maybeHost port -> do
        let hints = defaultHints { addrFlags = [AI_PASSIVE], addrSocketType = Stream }
        let maybeHost' = fmap C.unpack maybeHost
        addr:_ <- getAddrInfo (Just hints) maybeHost' (Just (show port))
        s <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
        setSocketOption s ReuseAddr 1
        bind s (addrAddress addr)
        listen s 7
        debug ("now listening on " ++ show i)
        replaceFile i (SocketFile s) state
    Accept i j -> do
        let Just (SocketFile s) = getFile i state
        debug ("accepting from " ++ show i ++ " to " ++ show j)
        (c,addr) <- accept s
        debug ("accepted: " ++ show addr)
        h <- socketToHandle c ReadWriteMode
        replaceFile j (HandleFile h) state
    Redirect i (Just j) -> do
        case getFile j state of
            Just f -> delFile j =<< replaceFile i f state
            Nothing -> closeFile i state
    Redirect i Nothing -> do
        debug ("Closing " ++ show i ++ ": " ++ show (getFile i state))
        closeFile i state

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
    eof2 <- isEOF
    debug ("next: eof=" ++ show eof ++ " stdin eof=" ++ show eof2)
    case eof of
        True -> return Nothing
        False -> do
            l <- Just <$> C.hGetLine h
            return $ Just state { pattern = l, lineNumber = 1 + lineNumber state }

runBranch Nothing  ss     state = runBlock ss state
runBranch (Just l) (s:ss) state = case s of
    Sed _ (Label m) | l == m -> runBlock ss state
    _ -> runBranch (Just l) ss state
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
