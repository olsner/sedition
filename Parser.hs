{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Applicative
import Control.Monad

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as BS

import Data.Maybe

import Text.Trifecta
import Text.Trifecta.Delta

import AST

pFile = pCommandsThen eof
pBlock = pCommandsThen (char '}')

manyMaybe p = catMaybes <$> many p
pCommandsThen :: Parser a -> Parser [Sed]
pCommandsThen p = manyMaybe (try $ wsThen lineOrComment) <* (wsThen p)
  where wsThen p = skipMany (oneOf "; \t\n\f\t\v\r") *> p

lineOrComment = Just <$> pLine <|> Nothing <$ pComment

-- TODO Special case, when the *first* line is #n autoprint is disabled.
-- Maybe should be in pFile (can be in the AST as a disable-autoprint command).
pComment = char '#' *> skipMany (notChar '\n')
pLine = Sed <$> option Always pMaybeAddress <*> wsThen pCommand

pMaybeAddress = choice $
  [ At <$> pAddress
  -- FIXME whitespace is accepted and ignored around the ,
  , Between <$> pAddress <* char ',' <*> pAddress
  ]
pAddress :: Parser Address
pAddress = choice
  [ Line <$> int
  , EOF <$ char '$'
  , IRQ <$ char 'I'
  , Match . re <$> slash True
  ]

-- not eof, blank, }, ; or #
pLabel = BS.pack <$> wsThen (some (noneOf "; \t\n\f\t\v\r#"))
pRegister = pLabel
-- Same but also delimited by : (for :port)
pHostName = BS.pack <$> wsThen (some (noneOf ":; \t\n\f\t\v\r#"))
pTextArgument = BS.pack <$> some (noneOf "\n\f\v\r#")

int :: Parser Int
int = fromInteger <$> decimal

wsThen p = blanks *> p
ws1Then p = blanks1 *> p
wsInt = wsThen int

blank = oneOf " \t"
blanks = skipMany blank
blanks1 = skipSome blank

slash :: Bool -> Parser S
slash re = (char '/' *> slashWith re '/')
    <|> (char '\\' *> anyChar >>= slashWith re)

-- Reads a "slash"-terminated (the terminator itself already parsed) argument
-- and consumes the terminator.
slashWith :: Bool -> Char -> Parser S
slashWith re term = (fmap BS.pack $
    many (noneOf [term,'\n','\\'] <|> (char '\\' >> char term))) <* char term

maybeP p = option Nothing (Just <$> p)

flags accepted = oneOf accepted
sFlag = charSwitch $
  [ ('g', SubstGlobal)
  , ('e', SubstExec)
  -- TODO p int for printing to a given file descriptor
  , ('p', SubstPrint 0)
  -- integer: substitute only the nth occurrence
  -- w file: write result to file
  -- m/M: make ^ and $ match start/end of line in a multi-line buffer
  --      (with \` and \' matching start/end of whole buffer)
  -- i/I: match case-insensitively
  -- would like to allow using m or M for messaging. Why did they use both?
  -- (GNU extension though - doesn't (necessarily) need to be supported)
  ]

pCommand = charSwitchM $
  [ ('{', Block <$> pBlock)
  , ('!', NotAddr <$> pCommand)
  , (':', Label <$> pLabel)
  , ('<', Redirect <$> wsThen int <*> maybeP (ws1Then int))
  , ('A', Accept <$> wsThen int <*> ws1Then int)
  , ('L', Listen <$> int <*> maybeP pHostName <*> (char ':' *> int))
  , ('b', Branch <$> maybeP pLabel)
  , ('d', pure Delete)
  , ('f', Fork <$> wsThen pLine)
  , ('h', Hold <$> maybeP pRegister)
  , ('n', Next <$> option 0 wsInt)
  , ('p', Print <$> option 0 wsInt)
  , ('m', Message <$> wsThen (maybeP pTextArgument))
  , ('s', anyChar >>= (\c -> Subst <$> (re <$> slashWith True c)
                                   <*> slashWith False c
                                   <*> many sFlag))
  ]

charSwitchM cps = choice [char c *> p | (c,p) <- cps]
charSwitch cps = charSwitchM [(c, pure p) | (c,p) <- cps]

parseString :: ByteString -> [Sed]
parseString input = case parseOnly pFile input of
    Success p -> p
    Failure e -> error (show e)

-- TODO: Include a parseFile here so we can get diagnostics with nice and
-- proper file/line messaages.

parseOnly p = parseByteString p (Lines 0 0 0 0)
testParseString input = print (parseOnly pFile input)
testParseFile = print . parseOnly pFile <=< BS.readFile
testParseLines = mapM_ testParseString . BS.lines <=< BS.readFile

doTest (input, result) = case parseOnly pFile input of
   Success p | p == result -> putStrLn ("pass: " ++ show input ++ " parsed to " ++ show p)
             | otherwise   -> putStrLn ("fail: " ++ show input ++ " did not parse to " ++ show result ++ " but " ++ show p)
   Failure e -> putStrLn ("fail: " ++ show input ++ " failed to parse:\n" ++ show e)

doTests = mapM_ doTest

tests =
  [ ("s/a/b/g", [Sed Always (Subst (Just (RE "a")) "b" [SubstGlobal])])
  , ("s/\\//\\//", [Sed Always (Subst (Just (RE "/")) "/" [])])
  , ("s|\\||\\||", [Sed Always (Subst (Just (RE "|")) "|" [])])
  , ("s///", [Sed Always (Subst Nothing "" [])])
  , ("//s///", [Sed (At (Match Nothing)) (Subst Nothing "" [])])
  , ("\\//s///", [Sed (At (Match Nothing)) (Subst Nothing "" [])])
  , ("\\||s|||", [Sed (At (Match Nothing)) (Subst Nothing "" [])])
  , ("\\/\\//s///", [Sed (At (Match (Just (RE "/")))) (Subst Nothing "" [])])
  , ("\\|\\||s|||", [Sed (At (Match (Just (RE "|")))) (Subst Nothing "" [])])
  ]

main = do
    doTests tests
    putStrLn ("Finished " ++ show (length tests) ++ " tests")
