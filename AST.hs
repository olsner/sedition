module AST where

import System.Exit

import Text.Regex.TDFA

import Data.ByteString.Char8 as C
type S = ByteString

-- TODO Replace with actual compiled regexp
data RE = RE S Regex
type Label = S

instance Show RE where
  show (RE s _) = show s
instance Eq RE where
  RE s _ == RE t _ = s == t
instance Ord RE where
  compare (RE s _) (RE t _) = compare s t

re :: S -> Maybe RE
re s | C.null s  = Nothing
     -- TODO With options
     | otherwise = RE s <$> makeRegexM s

data SubstType
  = SubstFirst
  | SubstNth Int
  | SubstAll
  -- TODO More flags
  deriving (Show, Ord, Eq)

data SubstAction
  = SActionNone
  | SActionPrint Int
  | SActionExec
  deriving (Show, Ord, Eq)

data Address = Line Int | Match (Maybe RE) | EOF | IRQ
    deriving (Show, Ord, Eq)
data MaybeAddress
  = Always
  | At Address
  | Between Address Address
  deriving (Show, Ord, Eq)
data Sed = Sed MaybeAddress Cmd deriving (Show, Ord, Eq)
data Cmd
  = Block [Sed]
  | Fork Sed
  | NotAddr Cmd
  | Label Label
  | Branch (Maybe Label)
  -- | Test Label
  -- | TestNot Label
  | Next Int
  | NextA Int
  | Print Int
  | PrintA Int
  -- fork flags are parsed separately to an event address with fork
  | Listen Int (Maybe S) Int
  | Accept Int Int
  | Redirect Int (Maybe Int)
  | Subst (Maybe RE) S SubstType SubstAction
  | Trans S S

  -- dD
  | Delete
  | DeleteA
  -- hH/gG
  | Hold (Maybe S)
  | HoldA (Maybe S)
  | Get (Maybe S)
  | GetA (Maybe S)

  | Message (Maybe S)

  -- qQ (print before exit) (exit code)
  | Quit Bool ExitCode
  deriving (Show, Ord, Eq)

