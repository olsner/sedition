{-# LANGUAGE RecordWildCards,OverloadedStrings,TemplateHaskell #-}

module Main where

import Control.Exception
import Control.Monad

import qualified Data.ByteString.Char8 as C
import Data.FileEmbed (embedStringFile)
import Data.String
import Data.Time

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import System.Process (rawSystem)

import Text.Printf

import SimulateTDFA
import TaggedRegex
import TNFA
import TDFA
import TDFA2C
import GenC

doSimulateTDFA tdfa s = print (runTDFA True tdfa s)

compileTDFA tdfa output = C.writeFile output . toByteString $
    programHeader output <> genC tdfa <> programFooter

-- TODO Add flags to control gcc optimization/debug settings.
compileC cFile exeFile defines =
    rawSystem "cc" (["-O2", cFile, "-o", exeFile] ++ map ("-D"++) defines)

-- TODO Use some realPath function instead of ./, in case a full path is used.
runExecutable exe inputs = rawSystem ("./" ++ exe) inputs

seditionRuntime :: IsString a => a
seditionRuntime = $(embedStringFile "sedition.h")
startingLine = length (lines seditionRuntime) + 2

programHeader :: String -> Builder
programHeader ofile = seditionRuntime <>
    "#line " <> intDec startingLine <> " " <> cstring (C.pack ofile) <> "\n" <>
    "static bool match(match_t* m, string* s, const size_t orig_offset) {\n" <>
    "bool result = false;\n" <>
    sfun "memset" ["m", "0xff", "sizeof(*m)"]
programFooter :: Builder
programFooter = "return result;\n" <>
    "}\n" <>
    "void main(int argc, const char *argv[]) {\n" <>
    "  static match_t m;\n" <>
    "  static string s;\n" <>
    "  for (int i = 1; i < argc; i++) {\n" <>
    "    set_str_const(&s, argv[i], strlen(argv[i]));\n" <>
    "    bool res = match(&m, &s, 0);\n" <>
    "    print_match(res, &m, &s);\n" <>
    "  }\n}\n"

-- TODO Some duplication with Sed.hs, extract utilities or something.
timestamp :: IO UTCTime
timestamp = getCurrentTime

reportTime :: String -> UTCTime -> UTCTime -> IO ()
reportTime label start end = do
    hPutStrLn stderr (printf "%32s %.3fs" label (realToFrac (diffUTCTime end start) :: Double))

-- TODO And option to run a match with TNFA instead of TDFA
-- (running without -c currently enables TDFA)
data Options = Options
  { extendedRegexps :: Bool
  , cOutputFile :: FilePath
  , exeOutputFile :: FilePath
  , dumpParse :: Bool
  , dumpTNFA :: Bool
  , dumpTDFA :: Bool
  , timeIt :: Bool
  , runIt :: Bool
  , compileIt :: Bool
  , defines :: [String]
  , strings :: [String]
  } deriving (Show, Eq)
defaultOptions = Options
    { extendedRegexps = False
    , cOutputFile = "out.c"
    , exeOutputFile = "a.out"
    , dumpParse = False
    , dumpTNFA = False
    , dumpTDFA = False
    , timeIt = False
    , runIt = True
    , compileIt = False
    , defines = []
    , strings = [] }
addString s o = o { strings = s : strings o }
setCOutputFile f o = o { cOutputFile = f }
setExeOutputFile f o = o { exeOutputFile = f }
addDefine f o = o { defines = f : defines o }

tdfa2cOptions =
  [ Option ['r', 'E'] ["regexp-extended"] (NoArg $ \o -> o { extendedRegexps = True }) "Use extended regexps"
  , Option ['t'] ["time"] (NoArg $ \o -> o { timeIt = True }) "Time optimization and execution of the program"
  , Option ['c'] ["compile"] (NoArg $ \o -> o { compileIt = True }) "Compile the regex to C code, compile and run it to match strings (if given)"
  , Option [] ["dump-parse"] (NoArg $ \o -> o { dumpParse = True }) "parse and print the parsed regex"
  , Option [] ["dump-tnfa"] (NoArg $ \o -> o { dumpTNFA = True }) "show the TNFA state machine"
  , Option [] ["dump-tdfa"] (NoArg $ \o -> o { dumpTDFA = True }) "show the TDFA state machine"
  , Option ['o'] ["c-output"] (ReqArg setCOutputFile "C_FILE") "Path to compiled C output file."
  , Option ['x'] ["exe"] (ReqArg setExeOutputFile "EXEC_FILE") "Path to compiled executable."
  , Option ['D'] [] (ReqArg addDefine "MACRO") "Add macro to C compilation"
  ]

do_main args = do
  let (optFuns,nonOpts,errors) = getOpt Permute tdfa2cOptions args
  let usage = usageInfo "Usage: tdfa2c [OPTION]... REGEX [STRING...]" tdfa2cOptions
  when (not (null errors) || null nonOpts) $ do
    mapM_ putStrLn (errors ++ [usage])
    exitFailure
  let Options{..} = foldl (.) id optFuns defaultOptions

  let regex:strings = nonOpts

  tStartParse <- timestamp
  let re = testTagRegex regex
  tEndParse <- re `seq` timestamp

  when dumpParse $ do
    hPrint stderr re
    when (not (dumpTDFA || dumpTNFA)) exitSuccess

  tStartTNFA <- timestamp
  let tnfa = genTNFA re
  tEndTNFA <- tnfa `seq` timestamp

  when dumpTNFA $ do
      hPutStrLn stderr (TNFA.prettyStates tnfa)
      when (not dumpTDFA) exitSuccess

  tStartTDFA <- timestamp
  let tdfa = genTDFA tnfa
  tEndTDFA <- tdfa `seq` timestamp

  when dumpTDFA $ do
      hPutStr stderr (TDFA.prettyStates tdfa)

  when timeIt $ do
    reportTime "Parsing" tStartParse tEndParse
    reportTime "TNFA" tStartTNFA tEndTNFA
    reportTime "TDFA" tStartTDFA tEndTDFA

  when (dumpTDFA || dumpTNFA) exitSuccess

  flip catch exitWith $ do
    when compileIt $ do
      tCompileStart <- timestamp
      compileTDFA tdfa cOutputFile
      tCompileEnd <- timestamp

      when timeIt $ do
        reportTime "Compile (TDFA)" tCompileStart tCompileEnd

    when (compileIt && runIt) $ do
      tCompileStart <- timestamp
      status <- compileC cOutputFile exeOutputFile defines
      tCompileEnd <- timestamp

      when timeIt $ do
        reportTime "Compile (C)" tCompileStart tCompileEnd

      when (status /= ExitSuccess) $ exitWith status

    when (not (null strings)) $ do
      tProgStart <- timestamp
      status <- if compileIt
        then runExecutable exeOutputFile strings
        else mapM_ (doSimulateTDFA tdfa) strings >> return ExitSuccess
      tProgEnd <- timestamp

      when timeIt $ do
        reportTime "Running" tProgStart tProgEnd

      when (status /= ExitSuccess) $ exitWith status

  return ExitSuccess


main = do_main =<< getArgs
