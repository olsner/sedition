
import Control.Concurrent

import Data.Map (Map)
import qualified Data.Map as M

import Network.Socket

import System.IO

-- Compiled regexp
type RE = String
type Label = String

data Event = Accept Int Int
    deriving (Ord, Eq)
data Address = Line Int | Match RE | Event Event
    deriving (Ord, Eq)
data MaybeAddress = Always | At Address | Between Address Address | NotAt Address | NotBetween Address Address
    deriving (Ord, Eq)
data Sed = Sed MaybeAddress Cmd
data Cmd
  = Block [Sed]
  | Fork Sed
  | Target Label
  | Branch Label
  -- | BranchIf Label
  -- | BranchIfNot Label
  | Next Int
  -- nextappend
  | Print Int
  -- printfirstline
  -- fork flags are parsed separately to an event address with fork
  | Listen Int (Maybe String) Int
  | Redirect Int (Maybe Int)
  | Subst RE RE

data File
  = HandleFile { fileHandle :: Handle }
  | SocketFile { fileSocket :: Socket }
data SedState = SedState {
  program :: [Sed],
  files :: Map Int File,
  lineNumber :: Int,
  pattern :: Maybe String,
  event :: Maybe Event,
  -- hold "" is classic hold space
  hold :: Map String String,
  -- Probably the wrong model for these.
  -- Consider one /foo/,/bar/ address and one /foo/,/baz/ address - pretty much
  -- each line should have its own state for whether it's still triggered.
  activeAddresses :: [Address],
  autoprint :: Bool

  -- Pending output? Other tricky stuff?
}

fatal msg = error ("ERROR: " ++ msg)

initialState pgm = SedState pgm M.empty 0 Nothing Nothing M.empty [] True

runSed :: [Sed] -> IO ()
runSed seds = runProgram (initialState seds) >> return ()

checkEvent e state = Just e == event state

check Always _ = True
check (At (Line expectedLine)) (SedState { lineNumber = actualLine })
    = expectedLine == actualLine
check (At (Event e)) state = checkEvent e state

runProgram state = runBlock (program state) state
runBlock (Sed cond s:ss) state = do
    if check cond state then run s state else return state
    runBlock ss state
runBlock [] state = next 0 state >>= runProgram
run c state = case c of
    Block seds -> runBlock seds state
    Fork sed -> do
        forkIO (runProgram state { program = [sed] } >> return ())
        return state
    Target l -> return state
    Branch l -> runBranch l (program state) state
    Next i -> next i state
    Listen i maybeHost port -> do
        let hints = defaultHints { addrSocketType = Stream }
        addr:_ <- getAddrInfo (Just hints) maybeHost (Just (show port))
        s <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
        bind s (addrAddress addr)
        listen s 7
        replaceFile i (SocketFile s) state
    Redirect i (Just j) -> do
        case getFile j state of
            Just f -> closeFile j =<< replaceFile i f state
            Nothing -> closeFile i state
    Redirect i Nothing -> closeFile i state

getFile i state = M.lookup i (files state)
closeFile i state = do
    {- The underlying socket/files may be used by other threads, so don't
    -- actually close them. Let them be garbage collected instead.
    case M.lookup i (files state) of
        --Just (SocketFile s) -> sClose s
        --Just (HandleFile h) -> hClose h
        _ -> return ()
    -}
    return state { files = M.delete i (files state) }
replaceFile i f state = do
    state <- closeFile i state
    return state { files = M.insert i f (files state) }
ifile i state = fileHandle (M.findWithDefault (HandleFile stdin) i (files state))
ofile i state = fileHandle (M.findWithDefault (HandleFile stdout) i (files state))

next i state = do
    case pattern state of
        Just t | autoprint state -> hPutStrLn (ofile 0 state) t
        _ -> return ()
    l <- hGetLine (ifile i state)
    return state { pattern = Just l }

runBranch l (s:ss) state = case s of
    Sed Always (Target m) | l == m -> runBlock ss state
    _ -> runBranch l ss state
runBranch l [] state = fatal ("Label " ++ show l ++ " not found")

echoServer = [
    Sed (At (Line 0)) (Listen 1 Nothing 2007),
    Sed (At (Event (Accept 1 2))) (Fork
        (Sed (At (Line 0)) (Redirect 0 (Just 2)))),
    Sed (At (Event (Accept 1 2))) (Redirect 2 Nothing)
    ]

cat = []
