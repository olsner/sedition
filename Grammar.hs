module Grammar where

import Control.Applicative

import Data.Attoparsec.ByteString.Char8 as A
import qualified Data.ByteString.Char8 as BS

import Data.Maybe

import AST

pFile = manyMaybe maybeLine <* endOfInput
pLine = whiteSpace *>
    (Sed <$> option Always pMaybeAddress <*> (whiteSpace *> pCommand)) <*
    newline

manyMaybe :: Parser (Maybe a) -> Parser [a]
manyMaybe p = catMaybes <$> many p

maybeLine = choice [Just <$> pLine, Nothing <$ pComment]
maybeP p = option Nothing (Just <$> p)

pCommand :: Parser Cmd
pCommand = choice
  [ Hold <$> (char 'h' *> maybeP pRegister <* eol)
  , Listen <$> (char 'L' *> int) <*> maybeP pHostName <*> (char ':' *> int) <* eol
  ]

int :: Parser Int
int = read <$> many1 digit

pRegister = whiteSpace *> nonWhiteSpace
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
pComment = () <$ char '#' <* takeRestOfLine
whiteSpace = skipWhile isspace
isspace c = c == ' ' || c == '\t'
nonWhiteSpace = takeTill isspace

eol = takeTill (\c -> c == '\n' || c == '#') <* newlineOrComment

-- TODO Escaped newlines in comments?
takeRestOfLine = takeTill (== '\n') <* A.takeWhile (== '\n')
newline = () <$ takeWhile1 (== '\n') <|> endOfInput
newlineOrComment = (newline <|> pComment) <?> "newlineOrComment"

main = do
    input <- BS.getContents
    print (parseOnly pFile input)

parseString input = do
    print (parseOnly pFile (BS.pack input))
