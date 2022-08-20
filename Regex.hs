{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}

module Regex (parseString, parseOnly, pRegex, Regex(..)) where

import Control.Applicative

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import Data.Char (digitToInt)
import Data.Set (Set)

import Text.Trifecta hiding (parseString)
import Text.Trifecta.Delta

data Regex
  = Any
  | Char Char
  | CClass (Set Char)
  | CNotClass (Set Char)
  -- Min repeats and max repeats (Nothing for unlimited)
  | Repeat Int (Maybe Int) Regex
  | AnchorStart
  | AnchorEnd
  | Group Regex
  | Concat [Regex]
  | Empty
  | Or [Regex]
  | BackRef Int
  deriving (Show,Ord,Eq)

-- Assumes that Concat is never used elsewhere, so there can't be nested
-- concatenations or anything annoying like that.
rconcat :: [Regex] -> Regex
rconcat [] = Empty
rconcat [x] = x
rconcat xs = Concat xs

flatten (Concat xs) = concatMap flatten xs
flatten x = [x]

ror [] = Empty
ror [a] = a
ror xs = Or xs

-- {m} = exactly m copies
rep 1   Nothing         = id
rep min Nothing         = Repeat min (Just min)
-- {m,} = at least m copies, parsed as Just Nothing
-- {m,n} = m..n copies, parsed as Just (Just n)
rep 1   (Just (Just 1)) = id
rep min (Just max)      = Repeat min max

-- Parser utilities (some duplicated from Parser.hs...)
maybeP p = option Nothing (Just <$> p)
int :: Parser Int
int = fromInteger <$> decimal

-- Need a try to avoid getting stuck after consuming a \ when we need to
-- backtrack to a completely different bit of grammar to parse what follows.
escaped p = try (char '\\' *> p)
escapedChar c = escaped (char c)

pRegex True = pERE
pRegex False = pBRE

pBRE = rconcat <$> many breAlternate
breAlternate = ror <$> sepBy1 breBranch (escapedChar '|')
breBranch = rconcat <$> some breSimple
breSimple = flip id <$> breNondupl <*> option id breDuplSym
breNondupl = choice [breGroup, backRef, anchorStart, anchorEnd, breOneChar]

breOneChar = breOrdChar <|> breQuotedChar <|> breAny -- <|> bracketExpression
breDuplSym :: Parser (Regex -> Regex)
breDuplSym = choice [star, breBracedCount, escaped plus, escaped question]

star :: Parser (Regex -> Regex)
star = Repeat 0 Nothing <$ char '*'
plus = Repeat 1 Nothing <$ char '+'
question = Repeat 0 (Just 1) <$ char '?'
breAny = Any <$ char '.'
ereAny = breAny
anchorStart = AnchorStart <$ char '^'
anchorEnd = AnchorEnd <$ char '$'

counts = rep <$> int <*> maybeP (char ',' *> maybeP int)
breBraces = between (escapedChar '{') (escapedChar '}')
ereBraces = between (char '{') (char '}')

breBracedCount = breBraces counts
ereBracedCount = ereBraces counts

breSpecialChars = "$*.[\\^"
breQuotedChar :: Parser Regex
breQuotedChar = Char <$> escaped (oneOf breSpecialChars)
-- TODO '*' is ordinary when it's the first character in a BRE
breOrdChar :: Parser Regex
breOrdChar = Char <$> noneOf breSpecialChars
breGroup :: Parser Regex
breParens = between (escapedChar '(') (escapedChar ')')
breGroup = breParens (Group <$> pBRE)

backRef = BackRef . digitToInt <$> (escaped digit)

pERE = ereAlternate
ereAlternate = ror <$> sepBy ereBranch (char '|')

ereBranch = rconcat <$> some ereExpr
ereExpr = flip id <$> ereNondupl <*> option id ereDuplSym
ereNondupl = choice [ereOneChar, anchorStart, anchorEnd, backRef, ereGroup]
ereDuplSym = star <|> plus <|> question <|> ereBracedCount
ereGroup = char '(' *> (Group <$> pERE) <* char ')'

ereOneChar = ereOrdChar <|> ereQuotedChar <|> ereAny -- <|> bracketExpression
ereSpecialChars = "$()*+.?[\\^{|"
ereQuotedChar = Char <$> escaped (oneOf ereSpecialChars)
ereOrdChar = Char <$> noneOf ereSpecialChars

-- TODO backrefs in EREs too

parseString :: Bool -> ByteString -> Regex
parseString ere input = case parseOnly (pRegex ere) input of
    Success p -> p
    Failure e -> error (show e)

parseOnly p = parseByteString p (Lines 0 0 0 0)
