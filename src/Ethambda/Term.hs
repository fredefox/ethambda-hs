-- | The core type system.
module Ethambda.Term
  ( Term(Var, Fun, App, Constr)
  , Constr(Unit, Product, Injl, Injr)
  ) where

-- | Raw terms
data Term a where
  Var     ∷               a → Term a
  Fun     ∷          Term a → Term a
  App     ∷ Term a → Term a → Term a
  Constr  ∷        Constr a → Term a

data Constr a where
  Unit    ∷                   Constr a
  Product ∷ Term a → Term a → Constr a
  Injl    ∷          Term a → Constr a
  Injr    ∷          Term a → Constr a
