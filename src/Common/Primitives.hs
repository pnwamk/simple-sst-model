module Common.Primitives
  ( Id(..)
  , Const(..)
  , Prim(..)
  ) where

data Id = Ident String deriving (Eq, Show, Ord)

data Const = IntC Integer | BoolC Bool
  deriving (Eq, Show, Ord)

data Prim =
  Add1
  | Sub1
  | IsZero
  | IsNum
  | IsTrue
  | IsFalse
  | IsPair
  | IsProc
  deriving (Eq, Show, Ord)


