{-# LANGUAGE OverloadedStrings, CPP, TypeFamilies, NamedFieldPuns, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Sed (main) where

#define DEBUG 0

import Compiler.Hoopl as H hiding ((<*>))

import Control.Exception
import Control.Monad

import qualified Data.ByteString.Char8 as C
import Data.Time

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
#if DEBUG
import System.IO.Unsafe
#endif
import System.Process (rawSystem)

import Text.Printf (printf)

import AST
import Compile
import Interpret (runProgram, inputListFile)
import Parser
import IR (toIR, Program)
import Optimize

data Options = Options
  { extendedRegexps :: Bool
  , autoprint :: Bool
  , enableIPC :: Bool
  , scripts :: [Either S FilePath]
  , cOutputFile :: FilePath
  , exeOutputFile :: FilePath
  , dumpParse :: Bool
  , dumpOptimizedIR :: Bool
  , dumpOriginalIR :: Bool
  , timeIt :: Bool
  , runIt :: Bool
  , compileIt :: Bool
  , fuel :: Int
  } deriving (Show, Eq)
defaultOptions = Options
    { extendedRegexps = False
    , autoprint = True
    , enableIPC = True
    , scripts = []
    , cOutputFile = "out.c"
    , exeOutputFile = "a.out"
    , dumpParse = False
    , dumpOptimizedIR = False
    , dumpOriginalIR = False
    , timeIt = False
    , runIt = True
    , compileIt = False
    , fuel = 1000000 }
addScript s o = o { scripts = Left (C.pack s) : scripts o }
addScriptFile f o = o { scripts = Right f : scripts o }
setCOutputFile f o = o { cOutputFile = f }
setExeOutputFile f o = o { exeOutputFile = f }
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
  , Option ['c'] ["compile"] (NoArg $ \o -> o { runIt = False, compileIt = True }) "Don't run the program, compile it to C code instead."
  , Option [] ["run"] (NoArg $ \o -> o { runIt = True }) "Compile and run."
  , Option ['o'] ["c-output"] (ReqArg setCOutputFile "C_FILE") "Path to compiled C output file."
  , Option [] ["exe"] (ReqArg setExeOutputFile "EXEC_FILE") "Path to compiled executable."
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

compileProgram :: Bool -> (H.Label, Program) -> FilePath -> IO ()
compileProgram ipc (label, program) ofile = do
    let compiled = compileIR ipc label program
    C.writeFile ofile compiled

compileC cFile exeFile = rawSystem "cc" ["-g", "-Og", cFile, "-o", exeFile]

-- TODO Use some realPath function instead of ./, in case a full path is used.
runExecutable exe inputs = rawSystem ("./" ++ exe) (map C.unpack inputs)

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
  let (entryLabel, program) = toIR autoprint extendedRegexps seds
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

  flip catch exitWith $ do
    when compileIt $ do
      tCompileStart <- timestamp
      compileProgram enableIPC (entryLabel, program') cOutputFile
      tCompileEnd <- timestamp

      when timeIt $ do
        reportTime "Compile (Sed)" tCompileStart tCompileEnd

    -- Dabburu kanpairu!
    -- TODO or pipe the compiled C code directly into gcc so we can do it in
    -- one pass without an extra file inbetween.
    when (compileIt && runIt) $ do
      tCompileStart <- timestamp
      status <- compileC cOutputFile exeOutputFile
      tCompileEnd <- timestamp

      when timeIt $ do
        reportTime "Compile (C)" tCompileStart tCompileEnd

      when (status /= ExitSuccess) $ exitWith status

    when runIt $ do
      tProgStart <- timestamp
      status <- if compileIt
        then runExecutable exeOutputFile inputs
        else do
          file0 <- inputListFile (map C.unpack inputs)
          runProgram enableIPC (entryLabel,program') file0
      tProgEnd <- timestamp

      when timeIt $ do
        reportTime "Running" tProgStart tProgEnd

      when (status /= ExitSuccess) $ exitWith status

  return ExitSuccess


main = do_main =<< getArgs
