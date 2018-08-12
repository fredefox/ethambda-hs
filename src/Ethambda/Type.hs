-- | The core type system.
module Ethambda.Type
  ( Type(Var,Fun,Constr)
  , Constr(Product, Sum, Unit)
  ) where

import Ethambda.Common

data Type a where
  Var     ∷               a → Type a
  Fun     ∷ Type a → Type a → Type a
  Constr  ∷        Constr a → Type a

data Constr a where
  Product  ∷ Type a → Type a → Constr a
  Sum      ∷ Type a → Type a → Constr a
  Unit     ∷ Constr a

instance Show a => Show (Type a) where
  show = \case
    Var a → show a
    Fun a b → mbrackets (show a) <.> "→" <.> show b
      where
      mbrackets = case a of
        Var{} → id
        Fun{} → brackets
        Constr{} → brackets
      brackets s = "(" <> s <> ")"
    Constr c → show c

instance Show a ⇒ Show (Constr a) where
  show = \case
    Product a b → show a <.> "*" <.> show b
    Sum a b → show a <.> "+" <.> show b
    Unit → "Unit"
