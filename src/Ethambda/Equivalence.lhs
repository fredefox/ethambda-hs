> {-# Language UnicodeSyntax, ConstraintKinds
> , FlexibleContexts, LambdaCase, NamedWildCards
> , FunctionalDependencies, TupleSections
> , ScopedTypeVariables #-}
>
> module Ethambda.Equivalence where
>
> import Data.Map (Map)
> import Data.Functor
> import Control.Arrow
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> import Control.Monad.Reader
> import Control.Monad.Writer
>
> import qualified Ethambda.System as Eth

In this module I'm trying to find an algorithm for determining
isomorphism between types in System Fω.

neg: {a, b}, pos: {b}
      -    -   +

> k ∷ a → (b → b)
> k _ b = b

neg: {b}, pos: {b, b}
       +    -    +

> f₁ ∷ (b → b) → b
> f₁ f = undefined

Have the same "@PosNeg@-representation" but are not equivalent.  This
can quickly be realized becuase @f₀@ is inhabited but @f₁@ is not.

- → (+ → -) → +
- → (+ → -) → +

a → (a → b) → b : #0 : {a: {}, {b: {}}
a → (b → a) → b : #0
a → (b → b) → a : #1



⊢ 0 → (1 → 2) → 3
  0 ⊢ (1 → 2) → 3
... (sub procedure)
  0 | ⊢ 1 → 2
  0 | 1 ⊢ 2       : {2: {0, 1}}
    (i.e. 2 can be constructed from 0 and 1
...
  0 , 2 ⊢ 3       : {1: {}, 3: {0, 2: {0, 1}}}

          ⊢ 0 → (1 → 2) → 3
{0: {}}       ⊢ (1 → 2) → 3      (shift)
{0: {}} |     ⊢  1 → 2           (closure)
{0: {}} | {1: {0}} ⊢ 2           (shift)
{0: {}  ,  2: {1: {0}}} ⊢ 3      (un-closure)
{3: {0: {}  ,  2: {1: {0}}}      (un-closure)


          ⊢ 0 → (1 → 2) → 3
{0: []}       ⊢ (1 → 2) → 3     (shift)
{0: []}|      ⊢  1 → 2          (closure)
{0: []}| {1: []}   ⊢ 2          (shift)
{0: [] , 2: [1]}        ⊢ 3     (unclosure)
{3: [0, 1, 2]}              ⊢   (unclosure)

    ⊢ 0 → 1 → 2 → 3 → 4
{0: }   ⊢ 1 → 2 → 3 → 4
{0: , 1: }  ⊢ 2 → 3 → 4


> type Env a = Map a (Set a)
>
> elemsSet ∷ Ord a ⇒ Env a → Set a
> elemsSet = Set.unions . Map.elems
>
> flatten ∷ Ord a ⇒ Env a → Set a
> flatten mp = Set.union (Map.keysSet mp) (elemsSet mp)
>
> type App a m = MonadWriter (Env a) m
>
> shift ∷ Ord a ⇒ App a m ⇒ a → m ()
> shift a = tell (Map.singleton a mempty)
>
> localW ∷ Monoid w ⇒ MonadWriter w m ⇒ m (w → w) → m ()
> localW = pass . fmap ((),)
>
> closure
>   ∷ ∀ a m . Ord a ⇒ App a m
>   ⇒ Eth.Type a → m (Env a → Env a)
> --closure = tell . merge . runWriter . solve
> closure = merger . runWriter . solve
>   where
>   merger ∷ (a, Env a) → m (Env a → Env a)
>   merger = pure . merge
>   merge ∷ (a, Env a) → Env a → Env a
>   merge (k, vs) mp = Map.insert k (flatten vs) mp
>
> solve
>   ∷ Ord a ⇒ App a m
>   ⇒ Eth.Type a → m a
> solve = \case
>   Eth.Var a → shift a $> a
>   Eth.Fun n p → do
>     localW $ closure n
>     solve p
>
> equivalence ∷ Ord a ⇒ Eth.Type a → Env a
> equivalence = execWriter . solve
