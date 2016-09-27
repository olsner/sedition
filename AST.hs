module AST where

import Data.ByteString.Char8 as C
type S = ByteString

-- TODO Replace with actual compiled regexp
newtype RE = RE S deriving (Show, Ord, Eq)
type Label = S

re :: S -> Maybe RE
re s | C.null s  = Nothing
     | otherwise = Just (RE s)

data SubstFlag
  = SubstGlobal
  | SubstExec
  | SubstPrint Int
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
  | Subst (Maybe RE) S [SubstFlag]
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
  deriving (Show, Ord, Eq)

