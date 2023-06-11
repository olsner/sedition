{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}

module Regex.Regex (
    parseString, parseOnly,
    Regex(..),
    reString,
    tdfa2cCompatible,
    anchoredAtStart,
    anchoredAtEnd,
    canMatch
    ) where

import Control.Applicative

import qualified Data.ByteString.Char8 as C
import Data.Char (digitToInt)
import Data.List (intercalate, (\\))
import qualified Data.Set as S

-- 'brackets' and a few similar combinators are "smart" and ignore whitespace
-- and such. Don't get confused :)
import Text.Trifecta hiding (parseString, brackets)

data Regex
  = Any
  | Char Char
  | CClass [Char]
  | CNotClass [Char]
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

instance Semigroup Regex where
  Empty     <> y         = y
  x         <> Empty     = x
  Concat xs <> Concat ys = Concat (xs ++ ys)
  Concat xs <> y         = Concat (xs ++ [y])
  x         <> Concat ys = Concat (x:ys)
  x         <> y         = Concat [x, y]

-- Assumes that Concat is never used elsewhere (i.e. this is a smart constructor
-- for Concat), so there can't be nested concatenations to process here.
rconcat :: [Regex] -> Regex
rconcat [] = Empty
rconcat [x] = x
rconcat xs = Concat xs

ror [] = Empty
ror [a] = a
ror xs = Or xs

charRange min max = enumFromTo min max
uniq = S.toList . S.fromList
cClass cs = CClass (uniq cs)
cNotClass cs = CNotClass (uniq cs)
spaceClass = cClass " \r\n\t\v\f"
notSpaceClass = cNotClass " \r\n\t\v\f"

-- {m} = exactly m copies
rep 1   Nothing         = id
rep min Nothing         = Repeat min (Just min)
-- {m,} = at least m copies, parsed as Just Nothing
-- {m,n} = m..n copies, parsed as Just (Just n)
rep 1   (Just (Just 1)) = id
rep min (Just max)      = Repeat min max

int :: Parser Int
int = fromInteger <$> decimal

-- Need a try to avoid getting stuck after consuming a \ when we need to
-- backtrack to a completely different bit of grammar to parse what follows.
escaped p = try (char '\\' *> p)
escapedChar c = escaped (char c)

pBRE = rconcat <$> many breAlternate
breAlternate = ror <$> sepBy1 breBranch (escapedChar '|')
breBranch = rconcat <$> some breSimple
breSimple = choice [ flip id <$> breNondupl <*> option id breDuplSym
                   , Char <$> char '*' ]
breNondupl = choice [breGroup, backRef, breOneChar]

breOneChar = choice $
  [ breOrdChar
  , spaceClass <$ escapedChar 's'
  , notSpaceClass <$ escapedChar 'S'
  , breQuotedChar
  , Char <$> try (char '\\' <* eof)
  , breAny
  , bracketExpression ]
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

counts = rep <$> int <*> optional (char ',' *> optional int)
breBraces = between (escapedChar '{') (escapedChar '}')
ereBraces = between (char '{') (char '}')

breBracedCount = breBraces counts
ereBracedCount = ereBraces counts

breSpecialChars = "*.[\\"
breQuotedChar :: Parser Regex
-- Don't include characters that get special meaning with backslash, this is
-- all characters that keep (or get) non-special meaning when escaped.
breQuotedChar = Char <$> escaped (noneOf "|()")
breOrdChar :: Parser Regex
breOrdChar = Char <$> noneOf breSpecialChars
breGroup :: Parser Regex
breParens = between (escapedChar '(') (escapedChar ')')
breGroup = breParens (Group <$> pBRE)

backRef = BackRef . digitToInt <$> (escaped digit)

pERE = ereAlternate
ereAlternate = ror <$> sepBy ereBranch (char '|')

ereBranch = rconcat <$> many ereExpr
ereExpr = flip id <$> ereNondupl <*> option id ereDuplSym
ereNondupl = choice [ereOneChar, anchorStart, anchorEnd, backRef, ereGroup]
ereDuplSym = star <|> plus <|> question <|> ereBracedCount
ereGroup = between (char '(') (char ')') (Group <$> pERE)

ereOneChar = choice $
  [ ereOrdChar
  , ereQuotedChar
  , ereAny
  , bracketExpression
  , spaceClass <$ escapedChar 's'
  , notSpaceClass <$ escapedChar 'S' ]
ereSpecialChars = "$()*+.?[\\^{|"
ereQuotedChar = Char <$> escaped (oneOf ereSpecialChars)
ereOrdChar = Char <$> noneOf ereSpecialChars

-- Allegedly shared between BRE and ERE syntax.
brackets = between (char '[') (char ']')
bracketExpression = brackets (nonMatchingList <|> matchingList)
matchingList = cClass <$> bracketList
nonMatchingList = char '^' *> (cNotClass <$> bracketList)
bracketList = (++) <$> initList <*> option [] (string "-")
initList = (++) <$> option [] (string "-" <|> string "]") <*> followList
followList = concat <$> many expressionTerm

-- left-factor and remove tries?
expressionTerm :: Parser [Char]
expressionTerm = try rangeExpression <|> singleExpression
singleExpression = (:[]) <$> endRange -- <|> characterClass <|> equivalenceClass
rangeExpression = try (charRange <$> startRange <*> endRange) <|>
                  -- e.g. [x--], a range ending at '-'
                  (charRange <$> startRange <*> char '-')
startRange = endRange <* char '-'
-- any char except ^, - or ], but only when they have special meaning?
endRange = noneOf "-]" <?> "end of range" -- <|> collatingSymbol
{-
dotBracket = between (string "[.") (string ".]")
eqBracket = between (string "[=") (string "=]")
colonBracket = between (string "[:") (string ":]")
collatingSymbol = dotBracket anyChar
equivalenceClass = eqBracket anyChar -- not meta char?
characterClass = charClass <$> colonBracket (many alphaNum)
-}

-- Always outputs an ERE. Our regexps include some ERE features, and also the
-- syntax is nicer.
reString Any                = "."
reString (Char c)
    | c `elem` ereSpecialChars = ['\\', c]
    | otherwise             = [c]
-- TODO ] must come first, - must be last, ^ can be anywhere except first.
reString (CClass cs)        = "[" ++ shuffleClass cs ++ "]"
reString (CNotClass cs)     = "[^" ++ shuffleClass cs ++ "]"
reString (Repeat 0 Nothing  r) = reString r ++ "*"
reString (Repeat 0 (Just 1) r) = reString r ++ "?"
reString (Repeat 1 Nothing  r) = reString r ++ "+"
reString (Repeat m Nothing  r) = reString r ++ "{" ++ show m ++ ",}"
reString (Repeat m (Just n) r)
    | n == m                = reString r ++ "{" ++ show m ++ "}"
    | True                  = reString r ++ "{" ++ show m ++ "," ++ show n ++ "}"
reString AnchorStart        = "^"
reString AnchorEnd          = "$"
reString (Group r)          = "(" ++ reString r ++ ")"
reString (Concat rs)        = concatMap reString rs
reString Empty              = ""
reString (Or rs)            = intercalate "|" (map reString rs)
reString (BackRef i)        = "\\" ++ show i

-- TODO Add a CharSet (and use that for CClass), convert to ranges here and
-- avoid special cases if - or ^ are in the middle of a range.
shuffleClass cs
    | ']' `elem` cs = putFirst ']'
    | '-' `elem` cs = putLast '-'
    | '^' `elem` cs = putLast '^'
    | otherwise = cs
  where
    putFirst c = [c] ++ shuffleClass (cs \\ [c])
    putLast  c = shuffleClass (cs \\ [c]) ++ [c]

hasBackrefs (Repeat _ _ r)  = hasBackrefs r
hasBackrefs (Group r)       = hasBackrefs r
hasBackrefs (Concat rs)     = or (map hasBackrefs rs)
hasBackrefs (Or rs)         = or (map hasBackrefs rs)
hasBackrefs (BackRef _)     = True
hasBackrefs _               = False

-- Doesn't currently need to look inside composite regexes, since it's only
-- used by anchoredAtEnd. Could be more sophisticated since there are infinite
-- ways to write a regex that matches anything. Perhaps this could be done in
-- the TNFA or TDFA stage to unify some of the ways?
matchesAnyForever (Repeat 0 Nothing Any) = True
matchesAnyForever _ = False

-- Anchored at start. Includes starts-with-wildcard because the longest-match
-- rule means that something like .*foo will match up until the *last* foo.
anchoredAtStart AnchorStart = True
anchoredAtStart (Group re)  = anchoredAtStart re
-- TODO Handle repeats and concatenations where we *eventually* get to an
-- anchored regexp after matching zero characters. e.g. (^)+ matches at least
-- one anchor, .*^foo matches ^foo after a silly zero-length match, but (^)*
-- might not require the anchor to match. For now, only look at the very
-- start in the simplest way.
anchoredAtStart (Concat xs) = anchoredAtStart (head xs)
anchoredAtStart (Or xs)     = all anchoredAtStart xs
anchoredAtStart re          = matchesAnyForever re

-- Anchored at the end, *or* ends with a wildcard match (in all branches).
anchoredAtEnd AnchorEnd   = True
anchoredAtEnd (Group re)  = anchoredAtEnd re
-- TODO Handle repeats and concatenations similarly to ^ above, but backwards.
anchoredAtEnd (Concat xs) = anchoredAtEnd (last xs)
anchoredAtEnd (Or xs)     = all anchoredAtEnd xs
anchoredAtEnd re          = matchesAnyForever re

-- Look for impossibilities, like anchors after something must have consumed
-- characters.
canMatch :: Regex -> Bool
canMatch _ = True

tdfa2cCompatible re = not (hasBackrefs re)

-- Special case since special-casing the parsing of $ at the end in BREs is
-- cumbersome. TODO Only on BREs?
eatAnchors :: Applicative f => (C.ByteString -> f Regex) -> C.ByteString -> f Regex
eatAnchors f s = go
  where
    go | C.null s = pure Empty
       | C.head s == '^' = (AnchorStart <>) <$> go2 (C.tail s)
       | otherwise       = go2 s
    go2 s | C.null s = pure Empty
          | C.last s == '$' = (<> AnchorEnd) <$> f (C.init s)
          | otherwise       = f s

parseString :: Bool -> C.ByteString -> Regex
parseString ere input = case parseOnly ere input of
    Success p -> p
    Failure e -> error (show e)

parseOnly :: Bool -> C.ByteString -> Result Regex
parseOnly False = eatAnchors (parseByteString (pBRE <* eof) mempty)
parseOnly True  = parseByteString (pERE <* eof) mempty
