{-# LANGUAGE OverloadedStrings, ApplicativeDo #-}

module Regex (
    parseString, parseOnly,
    pRegex,
    Regex(..),
    reString, re2c,
    hasAnchorStart, hasAnchorEnd,
    unanchor,
    hasAnchors, hasBackrefs, reanchor, re2cCompatible
    ) where

import Control.Applicative

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as C
import Data.Char (digitToInt)
import Data.List (intercalate, (\\))
import Data.Set (Set)
import qualified Data.Set as S

-- 'brackets' and a few similar combinators are "smart" and ignore whitespace
-- and such. Don't get confused :)
import Text.Trifecta hiding (parseString, brackets)
import Text.Trifecta.Delta

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

pRegex True = pERE
pRegex False = pBRE

pBRE = rconcat <$> many breAlternate
breAlternate = ror <$> sepBy1 breBranch (escapedChar '|')
breBranch = rconcat <$> some breSimple
breSimple = flip id <$> breNondupl <*> option id breDuplSym
breNondupl = choice [breGroup, backRef, anchorStart, anchorEnd, breOneChar]

breOneChar = choice $
  [ breOrdChar
  , breQuotedChar
  , breAny
  , bracketExpression
  , spaceClass <$ escapedChar 's'
  , notSpaceClass <$ escapedChar 'S']
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

hasAnchors (Repeat _ _ r)  = hasAnchors r
hasAnchors (Group r)       = hasAnchors r
hasAnchors (Concat rs)     = or (map hasAnchors rs)
hasAnchors (Or rs)         = or (map hasAnchors rs)
hasAnchors AnchorStart     = True
hasAnchors AnchorEnd       = True
hasAnchors _               = False

re2cEsc = concatMap f
  where
    f '\n' = "\\n"
    f ']'  = "\\]"
    f '\\'  = "\\\\"
    f c    = [c]

re2c Any                    = "."
re2c (Char c)               = show [c]
re2c (CClass cs)            = "[" ++ re2cEsc (shuffleClass cs) ++ "]"
re2c (CNotClass cs)         = "[^" ++ re2cEsc (shuffleClass cs) ++ "]"
re2c (Repeat 0 Nothing  r)  = re2c r ++ "*"
re2c (Repeat 1 Nothing  r)  = re2c r ++ "+"
re2c (Repeat m Nothing  r)  = re2c r ++ "{" ++ show m ++ ",}"
re2c (Repeat m (Just n) r)  = re2c r ++ "{" ++ show m ++ "," ++ show n ++ "}"
-- re2c anchors all regular expressions at the start implicitly. Not sure how
-- to deal with end-of-string anchor yet. Probably by matching and checking,
-- but this also has trouble when some branches match on $ and some don't.
re2c AnchorStart        = error "Attempted to re2c a ^-anchored expression"
re2c AnchorEnd          = error "Attempted to re2c a $-anchored expression"
-- NB: if we don't use POSIX mode, groups need additional tags
re2c (Group r)          = "( " ++ re2c r ++ " )"
re2c (Concat rs)        = unwords (map re2c rs)
re2c Empty              = ""
re2c (Or rs)            = intercalate " | " (map re2c rs)
re2c (BackRef _)        = error "back references are not supported by re2c"

-- Adjust the regexp to work with re2c's implicit anchoring.
-- ^re -> (re) and
-- re without ^ -> ^.*(re)
-- The matching code is similarly adjusted to offset the group indexing and
-- treat group 1 as the "whole match" group.
-- If the start anchor appears anywhere except first, error out.
reanchor :: Regex -> Regex
reanchor re
    | hasAnchorStart re = Group (removeAnchorStart re)
    | otherwise         = Concat [Repeat 0 Nothing Any, Group re]

unanchor = removeAnchorStart . removeAnchorEnd

-- A bit weird to have an anchor repeating thing. (^foo)? could make sense, but
-- it can't match more than once.
hasAnchorStart (Repeat _ _ r) = hasAnchorStart r
hasAnchorStart (Group r)      = hasAnchorStart r
hasAnchorStart (Concat (r:_)) = hasAnchorStart r
-- (foo|^bar) is useful, but not possible for reanchor to handle yet. As long
-- as all branches match, we can factor out the ^ to the start.
hasAnchorStart (Or rs)        = and (map hasAnchorStart rs)
hasAnchorStart AnchorStart    = True
hasAnchorStart _              = False

hasAnchorEnd (Repeat _ _ r) = hasAnchorEnd r
hasAnchorEnd (Group r)      = hasAnchorEnd r
hasAnchorEnd (Concat rs)    = hasAnchorEnd (last rs)
-- (foo|bar$) can't be handled yet, but if every alternative ends in $ we can.
hasAnchorEnd (Or rs)        = and (map hasAnchorEnd rs)
hasAnchorEnd AnchorEnd      = True
hasAnchorEnd _              = False


removeAnchorStart (Repeat min max r) = Repeat min max (removeAnchorStart r)
removeAnchorStart (Group r)          = Group (removeAnchorStart r)
removeAnchorStart (Concat (r:rs))    = Concat (removeAnchorStart r:rs)
removeAnchorStart (Or rs)            = Or (map removeAnchorStart rs)
removeAnchorStart AnchorStart        = Empty -- TODO Arrange to remove it instead of replacing with Empty?
removeAnchorStart other              = other -- error ("Tried to remove ^ anchor from unanchored expression " ++ show other)

removeAnchorEnd (Repeat min max r) = Repeat min max (removeAnchorEnd r)
removeAnchorEnd (Group r)          = Group (removeAnchorEnd r)
removeAnchorEnd (Concat rs)        = Concat (mapLast removeAnchorEnd rs)
removeAnchorEnd (Or rs)            = Or (map removeAnchorEnd rs)
removeAnchorEnd AnchorEnd          = Empty -- TODO Arrange to remove it instead of replacing with Empty?
removeAnchorEnd other              = other -- error ("Tried to remove $ anchor from unanchored expression " ++ show other)

mapLast _ [] = []
mapLast f [x] = [f x]
mapLast f (x:xs) = x : mapLast f xs

re2cCompatible Empty = False
-- These could (should?) just be handled by special code... Or even be
-- optimized away before we even get to consider trying to match against them.
-- e.g: always successful once, NextMatch always fails, resulting start/end
-- match offsets are constant 0 or length-of-string.
re2cCompatible AnchorStart = False
re2cCompatible AnchorEnd = False
re2cCompatible re = not (hasBackrefs re || hasAnchors (unanchor re))

parseString :: Bool -> ByteString -> Regex
parseString ere input = case parseOnly (pRegex ere) input of
    Success p -> p
    Failure e -> error (show e)

parseOnly p = parseByteString p (Lines 0 0 0 0)
