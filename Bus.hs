module Bus (
    Bus(..), newBus, Passenger(..), board, drive, ride, wait, tryride
    ) where

import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad

import Data.Either
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe

import System.IO.Unsafe
import System.Mem.Weak

newtype Bus a = Bus (MVar (Int, Map Int (Weak (MVar a))))
newtype Passenger a = Passenger (MVar a)

instance Show (Passenger a) where
  show _ = "Passenger{}"
instance Show (Bus a) where
  show _ = "Bus{}"

-- | Create a new empty bus.
newBus :: IO (Bus a)
newBus = Bus <$> newMVar (0, M.empty)

-- | Create a new passenger boarded onto the given bus.
board :: Bus a -> IO (Passenger a)
board (Bus bus) = modifyMVar bus $ \(next,pid) -> do
  pidvar <- newEmptyMVar
  weak <- mkWeakMVar pidvar (passengerLeft bus next)
  let pid' = M.insert next weak pid
  return ((next + 1, pid'), Passenger pidvar)

passengerLeft bus id = modifyMVar_ bus $ \(next,pid) -> do
  t <- myThreadId
  lockedPutStrLn (show t ++ ": passenger " ++ show id ++ " left the bus")
  return (next, M.delete id pid)

-- Actually we rely on the weak vars stuff to get rid of passenger corpses.
unboard :: Bus a -> Passenger a -> IO ()
unboard bus passenger = return ()

activePassengers :: Bus a -> IO [MVar a]
activePassengers (Bus bus) = do
    (next,map) <- takeMVar bus
    lost <- forM (M.toList map) $ \(k,w) -> do
        mv <- deRefWeak w
        case mv of
          Just v -> return (Left v)
          Nothing -> return (Right k)
    let (lefts,rights) = partitionEithers lost
    let map' = foldr M.delete map rights
    putMVar bus (next,map')
    lockedPutStrLn ("drive: lost " ++ show (length rights) ++ " passengers")
    return lefts

-- | Drive the bus with a value, sending it to each travelling passenger.
-- | This will block until every passenger has gotten the message.
drive :: Bus a -> a -> IO ()
drive bus value = do
    active <- activePassengers bus
    forM_ active $ \v -> putMVar v value

-- | Ride the bus: block until there's a value to receive, then make ourselves
-- | available to receive again.
ride :: Passenger a -> IO a
ride (Passenger v) = takeMVar v

-- | Wait for the bus to arrive, but don't ride it.
wait :: Passenger a -> IO ()
wait (Passenger v) = readMVar v >> return ()

-- | Check if the bus is here yet.
tryride :: Passenger a -> IO (Maybe a)
tryride (Passenger v) = tryTakeMVar v

putstrlock = unsafePerformIO (newMVar ())
lockedPutStrLn s = withMVar putstrlock $ \() -> do
    putStrLn s

testBus j n = do
    bus <- newBus
    passengers <- replicateM n (board bus)
    let traveller p = do
            t <- myThreadId
            msg <- ride p
            lockedPutStrLn (show t ++ ": travelled to " ++ show msg)
            if msg == j then return () else traveller p
    mapM_ (forkIO . traveller) passengers
    forM_ [1..j] $ \j -> do
        lockedPutStrLn ("MAIN: driving bus to " ++ show j)
        drive bus j

    lockedPutStrLn ("MAIN: threads should be dead, driving bus to " ++ show (j + 1))
    drive bus (j + 1)
