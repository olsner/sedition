module AST where

import Data.ByteString.Char8
type S = ByteString

-- Compiled regexp
type RE = String
type Label = String

data Address = Line Int | Match RE | EOF | IRQ
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
  | Branch Label
  -- | Test Label
  -- | TestNot Label
  | Next Int
  -- nextappend
  | Print Int
  -- printfirstline
  -- fork flags are parsed separately to an event address with fork
  | Listen Int (Maybe S) Int
  | Accept Int Int
  | Redirect Int (Maybe Int)
  | Subst RE RE

  -- hH/gG
  | Hold (Maybe S)
  | HoldA (Maybe S)
  | Get (Maybe S)
  | GetA (Maybe S)
  deriving (Show, Ord, Eq)

