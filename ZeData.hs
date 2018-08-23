{-# Language UnicodeSyntax, LambdaCase, NamedWildCards #-}
module ZeData (types) where

import Control.Monad hiding (void)

import Ethambda.System

import Equivalence (equivalence)

-- "a"
-- pos: a
a :: Type Int
a = Var 0

-- "b"
-- pos: b
b :: Type Int
b = Var 1

-- "a -> a"
-- neg: a; pos: a
i :: Type Int
i = Fun a a

-- "a -> b -> a"
-- neg: a, b; pos: a
k :: Type Int
k = a `Fun` (b `Fun` a)

-- "i -> b"
-- uninhabited
void :: Type Int
void = Fun i b

-- "b -> i"
point :: Type Int
point = Fun b i

c :: Type Int
c = Var 2

-- "void -> c"
f0 :: Type Int
f0 = Fun void c

-- "c -> void"
f1 :: Type Int
f1 = Fun c void

types :: [Type Int]
types = [ a, b, i, k, void, point, c, f0, f1 ]

main :: IO ()
main = mapM_ go types
  where
  go t = do
    print t
    print $ equivalence t
    putStrLn ""

class Unfold a where
  unfold ∷ a → [a]

instance Unfold () where
  unfold = pure

-- instance Unfold a ⇒ Unfold [a] where
--   unfold = _ . map unfold

interleave ∷ [a] → [a] → [a]
interleave xs = \case
  [] → xs
  (y:ys) → y : interleave ys xs

instance Unfold a ⇒ Unfold (Type a) where
  -- unfold ∷ Type a → [Type a]
  unfold t = t : case t of
    Var a → (Var <$> unfold a) <> _
    Fun n m → zipWith Fun (unfold n) (unfold m)

unfoldInf ∷ Unfold a ⇒ a → [a]
unfoldInf a = let xs = unfold a in xs <> concatMap unfoldInf xs
-- unfoldInf a = do
--   x ← unfold a
--   unfoldInf x
