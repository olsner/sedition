{-# LANGUAGE OverloadedStrings, CPP, TypeFamilies, NamedFieldPuns, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Main (main) where

#define DEBUG 0

import Compiler.Hoopl as H hiding ((<*>))

import Control.Exception
import Control.Monad

import qualified Data.ByteString.Char8 as C
import Data.Time

import System.Console.GetOpt
import System.Directory (removeFile)
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
import qualified EmitAsm
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
  , sOutputFile :: FilePath
  , exeOutputFile :: FilePath
  , dumpParse :: Bool
  , dumpOptimizedIR :: Bool
  , dumpOriginalIR :: Bool
  , timeIt :: Bool
  , runIt :: Bool
  , compileIt :: Bool
  , assembleIt :: Bool
  , linkIt :: Bool
  , fuel :: Int
  , defines :: [String]
  } deriving (Show, Eq)
defaultOptions = Options
    { extendedRegexps = False
    , autoprint = True
    , enableIPC = True
    , scripts = []
    , cOutputFile = "out.c"
    , sOutputFile = "out.asm"
    , exeOutputFile = "a.out"
    , dumpParse = False
    , dumpOptimizedIR = False
    , dumpOriginalIR = False
    , timeIt = False
    , runIt = True
    , compileIt = False
    , assembleIt = False
    , linkIt = False
    , fuel = 1000000
    , defines = [] }
addScript s o = o { scripts = Left (C.pack s) : scripts o }
addScriptFile f o = o { scripts = Right f : scripts o }
setCOutputFile f o = o { cOutputFile = f, sOutputFile = f }
setExeOutputFile f o = o { exeOutputFile = f, linkIt = True }
setFuel f o = o { fuel = f }
addDefine f o = o { defines = f : defines o }

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
  , Option ['S'] ["assemble"] (NoArg $ \o -> o { runIt = False, assembleIt = True }) "Don't run the program, compile it to assembly instead."
  , Option [] ["run"] (NoArg $ \o -> o { runIt = True }) "Compile and run."
  , Option ['o'] ["c-output"] (ReqArg setCOutputFile "C_FILE") "Path to compiled C output file."
  , Option [] ["exe"] (ReqArg setExeOutputFile "EXEC_FILE") "Path to compiled executable."
  , Option ['D'] [] (ReqArg addDefine "MACRO") "Add macro to C compilation"
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
    let compiled = compileIR ofile ipc label program
    C.writeFile ofile compiled

system :: String -> [String] -> IO ()
system cmd args = do
  res <- rawSystem cmd args
  case res of
    ExitSuccess -> return ()
    _ -> throw res

-- TODO Add flags to control gcc optimization/debug settings.
compileC cFile exeFile defines =
    rawSystem "cc" (["-O2", cFile, "-o", exeFile] ++ map ("-D"++) defines)

compileToAsm :: Bool -> (H.Label, Program) -> FilePath -> IO ()
compileToAsm ipc (label, program) sfile =
    C.writeFile sfile (EmitAsm.compileIR ipc label program)

withTempFile ext work = do
  (path,h) <- openTempFile "/tmp" ("sedition" ++ ext)
  hClose h
  finally (work path) (removeFile path)

assemble sFile exeFile defines =
    withTempFile ".s" $ \stdSFile ->
    withTempFile ".o" $ \oFile ->
    withTempFile ".o" $ \stdOFile -> do
      -- TODO Could do the mangling/compilation of sedition.h here instead of
      -- compiling to assembly in the Makefile.
      C.writeFile stdSFile EmitAsm.seditionRuntime
      system "cc" ["-c", stdSFile, "-o", stdOFile]
      let yasmFlags = ["-gdwarf2", "-felf64"] ++ map ("-D"++) defines
      system "yasm" (yasmFlags ++ ["-o", oFile, sFile])
      system "cc" [oFile, stdOFile, "-o", exeFile]

-- TODO Use some realPath function instead of ./, in case a full path is used.
runExecutable exe inputs = rawSystem ("./" ++ exe) (map C.unpack inputs)

timestamp :: IO UTCTime
timestamp = getCurrentTime

reportTime :: String -> UTCTime -> UTCTime -> IO ()
reportTime label start end = do
    hPutStrLn stderr (printf "%32s %.3fs" label (realToFrac (diffUTCTime end start) :: Double))

timedOperation name work = do
  tStart <- timestamp
  finally work $ do
    tEnd <- timestamp
    reportTime name tStart tEnd

do_main args = do
  let (optFuns,nonOpts,errors) = getOpt Permute sedOptions args
  let usage = usageInfo "Usage: sed [OPTION]... [SCRIPT] [INPUT]..." sedOptions
  when (not (null errors)) $ do
    mapM_ putStrLn (errors ++ [usage])
    exitFailure
  let opts@Options {..} = foldl (.) id optFuns defaultOptions

  let timed name work = if timeIt then timedOperation name work else work

  (scriptLines,inputs) <- getScript opts (map C.pack nonOpts)

  tStartParse <- timestamp
  let seds = parseString (C.unlines scriptLines)
  tEndParse <- seds `seq` timestamp

  when dumpParse $ do
    mapM_ (hPrint stderr) seds
    exitSuccess

  tStartGenerateIR <- timestamp
  let (entryLabel, program) = toIR autoprint extendedRegexps enableIPC seds
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
    when assembleIt $ do
      tCompileStart <- timestamp
      compileToAsm enableIPC (entryLabel, program') sOutputFile
      tCompileEnd <- timestamp

      when timeIt $ do
        reportTime "Compile (IR -> Asm)" tCompileStart tCompileEnd

    when (assembleIt && linkIt) $ do
      timed "Assemble" $ assemble sOutputFile exeOutputFile defines

    when compileIt $ do
      tCompileStart <- timestamp
      compileProgram enableIPC (entryLabel, program') cOutputFile
      tCompileEnd <- timestamp

      when timeIt $ do
        reportTime "Compile (IR -> C)" tCompileStart tCompileEnd

    -- Dabburu kanpairu!
    -- (https://www.youtube.com/watch?v=FHkFzRZdlV4)
    -- TODO or pipe the compiled C code directly into gcc so we can do it in
    -- one pass without an extra file inbetween.
    when (compileIt && linkIt) $ do
      tCompileStart <- timestamp
      status <- compileC cOutputFile exeOutputFile defines
      tCompileEnd <- timestamp

      when timeIt $ do
        reportTime "Compile (C)" tCompileStart tCompileEnd

      when (status /= ExitSuccess) $ exitWith status

    when runIt $ do
      tProgStart <- timestamp
      status <- if compileIt || assembleIt
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
