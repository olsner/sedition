{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Applicative
import Control.Monad

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as BS
import Data.Maybe

import System.Exit

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

unescape 'n' = '\n'
unescape 'r' = '\r'
unescape c   = c

list p1 p2 = (:) <$> p1 <*> p2

-- not eof, blank, }, ; or #
pLabel = BS.pack <$> wsThen (some (noneOf "; \t\n\f\t\v\r#"))
pRegister = pLabel
-- Same but also delimited by : (for :port)
pHostName = BS.pack <$> wsThen (some (noneOf ":; \t\n\f\t\v\r#"))
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
      [ char '\\' *> (list (char '\n') line1
                      <|> list (unescape <$> noneOf "\n") line1)
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
slashWith re term = BS.pack . concat <$> many p <* char term
  where
  p = choice $
    [ (:[]) <$> noneOf [term,'\n','\\']
    -- TODO It's possible to use a regexp-special character as the delimiter,
    -- which makes this a bit wonky. I think we may need to detect those and
    -- treat them as explicitly literals (?), which may mean adding the \\
    -- depending on if we use BRE or EREs.
    , [term] <$ try (char '\\' >> char term)
    -- Any other characters except the terminator get passed through to the
    -- regexp engine including the backslash.
    , (\x y -> [x,y]) <$> char '\\' <*> anyChar ]

maybeP p = option Nothing (Just <$> p)

flags accepted = oneOf accepted
setSubstType   t   (Subst pat rep _ act) = Subst pat rep t act
setSubstAction act (Subst pat rep t _  ) = Subst pat rep t act
sFlag = charSwitch $
  -- First, flags: control or tweak the matching
  [ ('g', setSubstType SubstAll)
  -- integer: substitute only the nth occurrence
  -- i/I: match case-insensitively
  -- m/M: make ^ and $ match start/end of line in a multi-line buffer
  --      (with \` and \' matching start/end of whole buffer)
  -- would like to allow using m or M for messaging. Why did they use both?
  -- (GNU extension though - doesn't (necessarily) need to be supported)

  -- Actions, decide how to make the substitution
  , ('e', setSubstAction SActionExec)
  -- TODO p int for printing to a given file descriptor
  , ('p', setSubstAction (SActionPrint 0))
  -- w file: write result to file
  ]

mkSubst pat rep flags = foldr (.) id flags (Subst pat rep SubstFirst SActionNone)

pQuit print = Quit print . intToExit <$> option 0 wsInt

pCommand = charSwitchM $
  [ ('{', Block <$> pBlock)
  , ('!', NotAddr <$> wsThen pCommand)
  , (':', Label <$> pLabel)
  , ('<', Redirect <$> wsThen int <*> maybeP (ws1Then int))
  , ('A', Accept <$> wsThen int <*> ws1Then int)
  , ('L', Listen <$> int <*> maybeP pHostName <*> (char ':' *> int))
  , ('b', Branch <$> maybeP pLabel)
  , ('d', pure Delete)
  , ('f', Fork <$> wsThen pLine)
  , ('g', Get <$> maybeP pRegister)
  , ('G', GetA <$> maybeP pRegister)
  , ('h', Hold <$> maybeP pRegister)
  , ('H', HoldA <$> maybeP pRegister)
  , ('n', Next <$> option 0 wsInt)
  , ('p', Print <$> option 0 wsInt)
  , ('q', pQuit True)
  , ('Q', pQuit False)
  , ('m', Message <$> wsThen (maybeP pTextArgument))
  , ('s', anyChar >>= (\c -> mkSubst <$> (re <$> slashWith True c)
                                     <*> slashWith False c
                                     <*> many sFlag))
  , ('a', Append <$> pTextArgument)
  , ('i', Insert <$> pTextArgument)
  , ('z', pure Clear)
  ]

charSwitchM cps = choice [char c *> p | (c,p) <- cps]
charSwitch cps = charSwitchM [(c, pure p) | (c,p) <- cps]

intToExit 0 = ExitSuccess
intToExit n = ExitFailure n

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

