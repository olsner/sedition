{-# LANGUAGE FlexibleContexts,ExistentialQuantification #-}

module AST where

import System.Exit

import Data.ByteString.Char8 as C
type S = ByteString

type Label = S

re :: S -> Maybe S
re s | C.null s  = Nothing
     | otherwise = Just s

data CaseConv
  = NoConv
  | LowerChar
  | Lower
  | UpperChar
  | Upper
  deriving (Ord,Eq,Show)
data Subst
  = Literal S
  | BackReference Int
  | WholeMatch
  | SetCaseConv CaseConv
  deriving (Ord,Eq,Show)
type Replacement = [Subst]

data SubstType
  = SubstFirst
  | SubstNth Int
  | SubstAll
  -- TODO More flags
  deriving (Show, Ord, Eq)

data SubstAction
  = SActionNone
  | SActionPrint Int
  | SActionWriteFile S
  | SActionExec
  deriving (Show, Ord, Eq)

data Address = Line Int | Match (Maybe S) | EOF | IRQ
    deriving (Show, Ord, Eq)
data MaybeAddress
  -- Perhaps the "Always" case should not be here since that allows e.g. (NotAddr Always)
  = Always
  | At Address
  | Between Address Address
  | NotAddr MaybeAddress
  deriving (Show, Ord, Eq)
data Sed = Sed MaybeAddress Cmd deriving (Show, Ord, Eq)
data Cmd
  = Block [Sed]
  | Fork Sed
  | Label Label
  | Branch (Maybe Label)
  | Test (Maybe Label)
  | TestNot (Maybe Label)
  | Next Int
  | NextA Int
  | Print Int
  | PrintFirstLine Int
  | PrintLiteral Int
  | PrintLineNumber Int
  -- fork flags are parsed separately to an event address with fork
  | Listen Int (Maybe S) Int
  | Accept Int Int
  | Redirect Int (Maybe Int)
  -- s///
  | Subst (Maybe S) Replacement SubstType SubstAction
  -- y///
  | Trans S S

  -- a: append text after this cycle finishes (TODO for this: needs more state)
  | Append S
  -- i: insert text, outputing it immediately
  | Insert S
  -- c: replace text in matching address range with new text, restarts cycle
  -- every time since we'll clear the pattern space whenever it matches.
  | Change S

  -- d - clear pattern space and start new cycle
  | Delete
  -- D - clear until the first newline, then start new cycle
  | DeleteFirstLine
  -- hH/gG
  | Hold (Maybe S)
  | HoldA (Maybe S)
  | Get (Maybe S)
  | GetA (Maybe S)
  | Exchange (Maybe S)

  | ReadFile S
  | WriteFile S
  -- TODO line variants of r/w (R/W). Need parsing and IR code.

  | Message (Maybe S)

  -- qQ (print before exit) (exit code)
  | Quit Bool ExitCode
  -- z
  | Clear
  deriving (Show, Ord, Eq)

