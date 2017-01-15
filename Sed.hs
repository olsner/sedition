{-# LANGUAGE OverloadedStrings, CPP #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

import Control.Applicative
import Control.Concurrent
import Control.Monad

import Data.Array
import Data.ByteString.Char8 as C
import Data.Char
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid

import Network.Socket

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
  -- Probably the wrong model for these.
  -- Consider one /foo/,/bar/ address and one /foo/,/baz/ address - pretty much
  -- each line should have its own state for whether it's still triggered.
  --activeAddresses :: [Address],

  -- TODO Add last matched regexp. Requires 'check' to be able to update the
  -- state before returning.

  autoprint :: Bool,
  block :: BlockState,

  box :: Mailbox (Either (Maybe S) S),
  bus :: Bus S,
  passenger :: Passenger S,
  irq :: Bool

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
debugPrint x = debug (show x)

fatal msg = error ("ERROR: " ++ msg)

-- The wheels on the bus goes round and round...
busRider p b = forever $ putMVar b . Right =<< ride p

initialState pgm = do
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
    autoprint = True,
    block = BlockN,
    box = Mailbox box,
    bus = bus,
    passenger = passenger,
    irq = False }
forkState state pgm = do
  passenger <- board (bus state)
  box <- newEmptyMVar
  forkIO (busRider passenger box)
  return state {
    program = pgm,
    pattern = Nothing,
    lineNumber = 0,
    block = BlockN,
    passenger = passenger,
    box = Mailbox box }

runSed :: [Sed] -> IO ()
runSed seds = runProgram =<< initialState seds

-- EOF is checked lazily to avoid the start of each cycle blocking until after
-- at least one character of the next line has been read.
check (At EOF) state = hIsEOF (ifile 0 state)
-- A bit of special casing here - unconditional statements should not be run
-- in the before-first or IRQ state unless they're inside a 0{} or I{} block.
-- runBlock updates and restores the BlockI/Block0 state.
-- This doesn't apply for unconditional *blocks* though - see runBlock below.
check Always state
    | irq state = return (block state == BlockI)
    | 0 <- lineNumber state = return (block state == Block0)
    -- On non-first lines, a missing pattern happens after 'd' (for example)
    -- treat these as matching too.
    | otherwise = return True
check (At (Line expectedLine)) (SedState { lineNumber = actualLine, irq = False })
    = return (expectedLine == actualLine)
check (At (Line _)) state = return False
check (At IRQ) state = return (irq state)
check (At (Match (Just (RE _ re)))) state
    | Just p <- pattern state = return (matchTest re p)
    | otherwise = return False
check addr state = fatal ("Unhandled addr " ++ show addr ++ " in state " ++ show state)

-- Only the first one negates - series of ! don't double-negate.
-- run will traverse and ignore all NotAddr prefixes.
applyNot (NotAddr cmd) t = not t
applyNot cmd t = t

runProgram :: SedState -> IO ()
runProgram state = runBlock (program state) state (const (return ()))

runBlock :: [Sed] -> SedState -> (SedState -> IO ()) -> IO ()
runBlock [] state k = newCycle 0 state runProgram
-- Would be nice not to need this hack here, the rest of the conditional stuff
-- should be updated to work with this.
-- This makes it so that unconditional blocks are run even if the BlockI/0
-- state check would *not* run an unconditional statement now. The block might
-- then contain conditionals that do match.
runBlock (Sed Always (Block seds):ss) state k =
    runBlock seds state (\state -> runBlock ss state k)
runBlock (Sed cond c:ss) state k = do
    dorun <- check cond state
    debug (show cond ++ " => " ++ show dorun ++ ": " ++ show c)
    -- If the address is one of these special addresses, then change the block
    -- state, then make sure to reset it to its previous value before running
    -- the next statement.
    -- Blocks run inside this block will inherit it and get the block-state
    -- popped once it gets back to the outer continuation.
    let state' = case cond of
            At (Line 0) -> state { block = Block0 }
            At IRQ -> state { block = BlockI }
            _ -> state
    let k' state'' = runBlock ss (state'' { block = block state }) k
    if applyNot c dorun then run c state' k' else k' state

run :: Cmd -> SedState -> (SedState -> IO ()) -> IO ()
run c state k = case c of
    Block seds -> runBlock seds state k
    Fork sed -> do
        forkIO $ do
            debug ("start of fork")
            runProgram =<< forkState state [sed]
            debug ("end of fork")
        debug ("parent is after fork")
        k state
    NotAddr c -> run c state k
    Label l -> k state
    Branch Nothing -> do
        debug "branch: nothing"
        newCycle 0 state runProgram
    Branch (Just l) -> runBranch l (program state) state
    -- err, this is wrong... n should not restart?
    -- it should just replace pattern space - and should *not* accept an IRQ.
    Next i -> newCycle i state k
    Print i | Just p <- pattern state -> do
                C.hPutStrLn (ofile i state) p
                k state
            | otherwise -> k state
    Delete -> k state { pattern = Nothing }

    Insert s -> C.hPutStrLn (ofile 0 state) s >> k state

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

    Message Nothing -> do
        let Just m = pattern state
        debug ("Messaging " ++ show m)
        drive (bus state) m
        k state
    Message (Just m) -> do
        debug ("Messaging " ++ show m)
        drive (bus state) m
        k state

    Subst (Just (RE _ pat)) rep t action
      | Just p <- pattern state,
        -- matchAll if SubstGlobal is in flags
        matches@(_:_) <- match t pat p -> do
          let newp = subst p rep matches
          runSubAction action newp state
          k state { pattern = Just newp }
      | otherwise -> k state

    Quit True status -> run (Print 0) state (const (exitWith status))
    Quit False status -> exitWith status

    _ -> System.IO.putStrLn ("Unhandled command: " ++ show c) >> exitFailure

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

runSubAction SActionNone _ _ = return ()
runSubAction SActionExec s _ = do
    debug ("TODO: Actually execute " ++ show s)
    return ()
runSubAction (SActionPrint i) s state = C.hPutStrLn (ofile i state) s

match SubstFirst re p = case matchOnce re p of Just x -> [x]; Nothing -> []
match SubstAll re p = matchAll re p
-- TODO Handle not finding enough matches for match i. Should be handled the
-- same as a nonmatch.
match (SubstNth i) re p = [matchAll re p !! i]

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

hMaybeGetLine :: Handle -> IO (Maybe S)
hMaybeGetLine h = do
    eof <- hIsEOF h
    if eof then pure Nothing
           else Just <$> C.hGetLine h

forkIO_ f = forkIO f >> return ()

-- Read a new input line, then run k if input was available or return ()
-- directly if we've reached EOF.
-- For 'n' (read input and continue execution), k is the next-command
-- continuation. For the end-of-cycle or 'b' (t/T) without target, k is instead
-- runProgram so that it restarts the whole program.
newCycle i state k = do
    debug ("new cycle: -- state = " ++ show state)
    next i state $ \state -> do
        debug ("new cycle: => state = " ++ show state)
        k state
    debug ("new cycle: exiting")

next i state k = do
    case pattern state of
        Just t | autoprint state && not (irq state) ->
            C.hPutStrLn (ofile 0 state) t
        _ -> return ()
    -- if we successfully got an IRQ for last cycle, that means we're already
    -- running an asynchronous getLine and shouldn't start another.
    let Mailbox v = box state
    when (not (irq state)) $
      forkIO_ (putMVar v . Left =<< hMaybeGetLine (ifile i state))
    lineOrEvent <- takeMVar v
    debug ("next: " ++ show lineOrEvent)
    case lineOrEvent of
      Left Nothing -> return ()
      Left (Just l) -> do
            k $ state { pattern = Just l, lineNumber = 1 + lineNumber state,
                        irq = False }
      Right l -> do
            k $ state { pattern = Just l, irq = True }

runBranch l (s:ss) state = case s of
    Sed _ (Label m) | l == m -> runBlock ss state (const (return ()))
    _ -> runBranch l ss state
runBranch l [] state = fatal ("Label " ++ show l ++ " not found")

runSedString = runSed . parseString

runSedFile f = do
    pgm <- parseString <$> C.readFile f
    debugPrint pgm
    runSed pgm

main = runSedFile "examples/http_server.xed"
