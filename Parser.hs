module Parser where

import Control.Applicative

import Data.Attoparsec.ByteString.Char8 as A
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as BS

import Data.Maybe

import AST

pFile = manyMaybe maybeLine <* endOfInput
pLine = whiteSpace *>
    (Sed <$> option Always pMaybeAddress <*> (whiteSpace *> pCommand)) <*
    eol

manyMaybe :: Parser (Maybe a) -> Parser [a]
manyMaybe p = catMaybes <$> many p

maybeLine = choice [Just <$> pLine, Nothing <$ pComment]
maybeP p = option Nothing (Just <$> p)

pCommand :: Parser Cmd
pCommand = choice
  [ Hold <$> (char 'h' *> maybeP pRegister)
  , Listen <$> (char 'L' *> int) <*> maybeP pHostName <*> (char ':' *> int)
  , Label <$> (char ':' *> pLabel)
  , Branch <$> (char 'b' *> maybeP pLabel)
  , Accept <$> (char 'A' *> int) <*> (whiteSpace1 *> int)
  , Redirect <$> (char '<' *> whiteSpace *> int) <*> (whiteSpace1 *> maybeP int)
  , Fork <$> (char 'f' *> pLine)
  , NotAddr <$> (char '!' *> pCommand)
  , (\c -> error ("Unrecognized command " ++ show c)) <$> anyChar <* A.takeWhile (const True)
  ]

int :: Parser Int
int = read <$> many1 digit

identifier = takeTill (inClass " \t\n#")
pLabel = whiteSpace *> identifier
pRegister = whiteSpace *> identifier
pHostName = A.takeWhile1 (\c -> c /= ':')

pMaybeAddress = choice $
  [ At <$> pAddress
  , Between <$> pAddress <* comma <*> pAddress ]
pAddress :: Parser Address
pAddress = choice
  [ Line <$> int
  , EOF <$ char '$'
  ]

comma = () <$ whiteSpace <* char ',' <* whiteSpace

pComment :: Parser ()
pComment = char '#' *> skipRestOfLine
whiteSpace = skipWhile isspace
whiteSpace1 = satisfy isspace *> whiteSpace
isspace c = c == ' ' || c == '\t'
nonWhiteSpace = takeTill isspace

eol = takeTill (inClass "\n#") <* newlineOrComment

-- TODO Escaped newlines in comments?
skipRestOfLine = () <$ takeTill (== '\n') <* A.takeWhile (== '\n')
newline = () <$ takeWhile1 (== '\n') <|> endOfInput
newlineOrComment = (newline <|> pComment) <?> "newlineOrComment"

parseString :: ByteString -> [Sed]
parseString input = case parseOnly pFile input of
    Right p -> p
    Left e -> error e

testParseString input = print (parseOnly pFile input)
