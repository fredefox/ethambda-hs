module Ethambda.Common ((<.>), (<.)) where

(<.>) :: String -> String -> String
(<.>) s = \case
  [] -> s
  s' -> s <> " " <> s'

(<.) :: String -> ShowS -> ShowS
s <. c = (s <.>) . c
infixr 3 <.
  
