{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}

module Parser (parseString, parseOnly, pFile) where

import Control.Applicative

import Data.Bits
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.UTF8 as UTF8
import Data.Char (digitToInt, toUpper)
import Data.Maybe

import System.Exit

import Text.Trifecta hiding (parseString)

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
pLine = Sed <$> pMaybeAddress <*> wsThen pCommand

pMaybeAddress = do
    addr <- option Always pAddressRange
    f <- option id (NotAddr <$ try (wsThen (char '!')))
    return (f addr)
-- Backtracking could be avoided here - we shouldn't need to reparse pAddress
-- after failing to find a second part of the range.
pAddressRange = choice $
  [ try (Between <$> pAddress <* wsThen (char ',') <*> wsThen pAddress)
  , At <$> pAddress
  ]
pAddress :: Parser Address
pAddress = choice
  [ Line <$> int
  , EOF <$ char '$'
  , IRQ <$ char 'I'
  , Match . re <$> slash True
  ]

unescape 'a' = '\a'
unescape 'f' = '\f'
unescape 'n' = '\n'
unescape 'r' = '\r'
unescape 't' = '\t'
unescape 'v' = '\v'
unescape c   = c

hexUnescape _ d1 d2 = toEnum (read ['0','x',d1,d2])
hexUnescape1 _ d1 = toEnum (read ['0','x',d1])
controlChar c = toEnum (fromEnum (toUpper c) `xor` 0x40)

list p1 p2 = (:) <$> p1 <*> p2

wsMaybeP p = wsThen (maybeP p)
pRequiredLabel = BS.pack <$> some (noneOf "; \t\n\f\t\v\r#{}")
pLabel = wsMaybeP pRequiredLabel
pRegister = pLabel
pFileName = wsThen pRequiredLabel
-- Same but also delimited by : (for :port)
pHostName = BS.pack <$> some (noneOf ":; \t\n\f\t\v\r#{}")
-- Accept both single-line and multiple-line arguments to [aicm]
-- initial whitespace is ignored (but only on the very first line after the
-- command), after that backslash followed by newline continues the text on the
-- next line, backslash followed by anything else is unescaped and used.
-- EOF or a newline not preceded by a backslash terminates the text.
pTextArgument = BS.pack <$> (line0 <|> wsThen line1)
  where
    -- If the first data is backslash, newline, then it's ignored and starts a
    -- multiline text.
    line0 = char '\\' *> char '\n' *> line1
    line1 = choice $
      [ list (char '\\' *> (pEscaped <|> anyChar)) line1
      , [] <$ char '\n'
      , [] <$ eof
      , list anyChar line1]

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
slashWith re term = BS.concat <$> many p <* char term
  where
  -- On the regexp side, handle character classes specially. On the replacement
  -- side, [ is just a literal.
  p | re        = choice (charClass : commonParsers term)
    | otherwise = choice (commonParsers term)
  -- TODO Kind of similar to slashWith ']', but we don't want to unescape
  -- things like \], and we should unescape the terminator. Getting all
  -- the corner cases really right requires more work.
  charClass = BS.concat <$> (charBS '[' $>$$ many charInClass $$>$ charBS ']')
  charInClass = choice (commonParsers ']')
  charBS c = BS.singleton <$> char c
  commonParsers term =
    [ BS.singleton <$> noneOf [term,'\n','\\']
    -- See the "escaping precedence" chapter of the GNU sed manual. Basically
    -- we unescape everything we recognize our here before parsing the regexp.
    , BS.singleton <$> try (char '\\' >> char term)
    , BS.singleton <$> try (char '\\' *> pEscaped)
    -- Any other characters except the terminator get passed through to the
    -- regexp engine including the backslash.
    , (\x y -> BS.pack [x,y]) <$> char '\\' <*> anyChar ]

stringTerm :: Char -> Parser S
stringTerm term = slashWith False term

pRegexp :: Char -> Parser (Maybe S)
pRegexp term = re <$> slashWith True term

pEscaped = choice [ unescape <$> oneOf "afnrtv"
                  , try (hexUnescape <$> char 'x' <*> hexDigit <*> hexDigit)
                  , hexUnescape1 <$> char 'x' <*> hexDigit
                  , char 'c' *> (controlChar <$> anyChar)]

-- Parse a replacement and the closing terminator. \ escapes the terminator and
-- starts a back reference. & is a reference to the whole pattern.
pReplacement :: Char -> Parser Replacement
pReplacement term = combineLiterals <$> many (choice ps) <* char term
  where
  ps = [ WholeMatch <$ char '&'
       , charLit <$> noneOf [term,'\n','\\']
       , char '\\' >> choice escaped ]
  escaped = [ charLit <$> pEscaped
            , BackReference . digitToInt <$> digit
            , SetCaseConv Lower <$ char 'L'
            , SetCaseConv LowerChar <$ char 'l'
            , SetCaseConv Upper <$ char 'U'
            , SetCaseConv UpperChar <$ char 'u'
            , SetCaseConv NoConv <$ char 'E'
            , charLit <$> anyChar ]
  charLit = Literal . BS.singleton

combineLiterals xs = go "" xs
  where
    go s1 (Literal s2:xs) = go (BS.append s1 s2) xs
    go s1 (x:xs) = s1 `literalThen` (x : go "" xs)
    go s1 [] = s1 `literalThen` []
    literalThen s xs | BS.null s = xs
                     | otherwise = Literal s : xs

($>$$) :: Applicative f => f a -> f [a] -> f [a]
head $>$$ tail = (:) <$> head <*> tail

($$>$) :: Applicative f => f [a] -> f a -> f [a]
head $$>$ tail = (\xs y -> xs ++ [y]) <$> head <*> tail

maybeP p = option Nothing (Just <$> p)
maybeNonEmpty s | BS.null s = Nothing | otherwise = Just s

setSubstType   t   (_,act) = (t,act)
setSubstAction act (t,_) = (t,act)
sFlag = choice $
  -- integer: substitute only the nth occurrence
  [ setSubstType . SubstNth <$> int
  -- w file: write result to file
  , setSubstAction . SActionWriteFile <$> (char 'w' *> pFileName)
  -- p int for printing to a given file descriptor. probably conflicts with
  -- existing syntax though, since s///p1 should replace the first match and
  -- print.
  --, setSubstAction . SActionPrint <$> (char 'p' *> option 0 int)
  , sCharFlag
  ]
sCharFlag = charSwitch $
  -- First, flags: control or tweak the matching
  [ ('g', setSubstType SubstAll)
  -- i/I: match case-insensitively
  -- m/M: make ^ and $ match start/end of line in a multi-line buffer
  --      (with \` and \' matching start/end of whole buffer)
  -- would like to allow using m or M for messaging. Why did they use both?
  -- (GNU extension though - doesn't (necessarily) need to be supported)

  -- Actions, decide how to make the substitution
  , ('e', setSubstAction SActionExec)
  -- p without argument, print to stdout
  , ('p', setSubstAction (SActionPrint 0))
  ]

-- TODO Parse the replacement into e.g. a list of strings and references instead
-- of doing that on the fly in the interpreter.
mkSubst pat rep flags = Subst pat rep subst action
  where
    (subst,action) = foldr (.) id flags (SubstFirst, SActionNone)

pQuit print = Quit print . intToExit <$> option 0 wsInt

pCommand = charSwitchM $
  [ ('{', Block <$> pBlock)
  , (':', Label <$> wsThen pRequiredLabel)
  , ('<', Redirect <$> wsThen int <*> maybeP (ws1Then int))
  -- Is it relevant to have file number here? It does have no other arguments
  -- at least, but it's a nice character to overload with another meaning if
  -- given an argument.
  , ('=', PrintLineNumber <$> option 0 wsInt)
  , ('a', Append <$> pTextArgument)
  , ('A', Accept <$> wsThen int <*> ws1Then int)
  , ('b', Branch <$> pLabel)
  , ('c', Change <$> pTextArgument)
  , ('d', pure Delete)
  , ('D', pure DeleteFirstLine)
  , ('f', Fork <$> wsThen pLine)
  , ('g', Get <$> pRegister)
  , ('G', GetA <$> pRegister)
  , ('h', Hold <$> pRegister)
  , ('H', HoldA <$> pRegister)
  , ('x', Exchange <$> pRegister)
  , ('i', Insert <$> pTextArgument)
  , ('l', PrintLiteral <$> option 70 wsInt)
  , ('L', Listen <$> int <*> wsMaybeP pHostName <*> (char ':' *> int))
  , ('m', Message <$> maybeNonEmpty <$> wsThen pTextArgument)
  , ('n', Next <$> option 0 wsInt)
  , ('N', NextA <$> option 0 wsInt)
  , ('p', Print <$> option 0 wsInt)
  , ('P', PrintFirstLine <$> option 0 wsInt)
  , ('q', pQuit True)
  , ('Q', pQuit False)
  , ('r', ReadFile <$> pFileName)
  --, ('R', ReadLine <$> pFileName)
  , ('s', anyChar >>= (\c -> mkSubst <$> pRegexp c
                                     <*> pReplacement c
                                     <*> many sFlag))
  , ('t', Test <$> pLabel)
  , ('T', TestNot <$> pLabel)
  , ('w', WriteFile <$> pFileName)
  -- TODO W for WriteFileFirstLine
  , ('y', anyChar >>= (\c -> Trans <$> stringTerm c <*> stringTerm c))
  , ('z', pure Clear)
  ]

charSwitchM cps = choice [char c *> p | (c,p) <- cps]
charSwitch cps = charSwitchM [(c, pure p) | (c,p) <- cps]

intToExit 0 = ExitSuccess
intToExit n = ExitFailure n

toUTF8 = UTF8.fromString . BS.unpack

parseString :: ByteString -> [Sed]
parseString input = case parseOnly pFile (toUTF8 input) of
    Success p -> p
    Failure e -> error (show e)

-- TODO: Include a parseFile here so we can get diagnostics with nice and
-- proper file/line messaages.

parseOnly p = parseByteString p mempty . toUTF8
