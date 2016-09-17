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
  ]

-- not eof, blank, }, ; or #
pLabel = BS.pack <$> wsThen (some (noneOf "; \t\n\f\t\v\r#"))
pRegister = pLabel
-- Same but also delimited by : (for :port)
pHostName = BS.pack <$> wsThen (some (noneOf ":; \t\n\f\t\v\r#"))

int :: Parser Int
int = fromInteger <$> decimal

wsThen p = blanks *> p
ws1Then p = blanks1 *> p
wsInt = wsThen int

blank = oneOf " \t"
blanks = skipMany blank
blanks1 = skipSome blank

maybeP p = option Nothing (Just <$> p)

pCommand = charSwitch $
  [ ('{', Block <$> pBlock)
  , ('!', NotAddr <$> pCommand)
  , (':', Label <$> pLabel)
  , ('<', Redirect <$> wsThen int <*> maybeP (ws1Then int))
  , ('A', Accept <$> wsThen int <*> ws1Then int)
  , ('L', Listen <$> int <*> maybeP pHostName <*> (char ':' *> int))
  , ('b', Branch <$> maybeP pLabel)
  , ('d', pure Delete)
  , ('f', Fork <$> pLine)
  , ('h', Hold <$> maybeP pRegister)
  , ('n', Next <$> option 0 wsInt)
  , ('p', Print <$> option 0 wsInt)
  ]
  where
    charSwitch cps = choice [char c *> p | (c,p) <- cps]

parseString :: ByteString -> [Sed]
parseString input = case parseOnly pFile input of
    Success p -> p
    Failure e -> error (show e)

parseOnly p = parseByteString p (Lines 0 0 0 0)
testParseString input = print (parseOnly pFile input)
testParseFile = print . parseOnly pFile <=< BS.readFile
testParseLines = mapM_ testParseString . BS.lines <=< BS.readFile
