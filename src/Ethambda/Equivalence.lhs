> {-# Language UnicodeSyntax, ConstraintKinds
> , FlexibleContexts, LambdaCase, NamedWildCards
> , FunctionalDependencies, TupleSections
> , ScopedTypeVariables, TypeApplications #-}
>
> module Ethambda.Equivalence
>   ( equivalence
>   )
>   where
>
> import Data.Map (Map)
> import Data.Functor
> import Control.Arrow
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> import Control.Monad.State
>
> import qualified Ethambda.System as Eth
>
> import Debug.Trace
> import Unsafe.Coerce

In this module I'm trying to find an algorithm for determining some

normal form for terms and types in System Fω.  Currently I haven't
generalized the system to that, I currently just have polymorphic type
variables and fucntion types.  See @Ethambda.System@.

My idea is that we could somehow group parameters into those occuring
in a positive position and those that occur in a negative position.
However, this is clearly not enough.  Consider functions with the
"shape":

    _ → (_ → _) → _

If we annotate this with the polarty of the holes:

    - → (+ → -) → +

This type:

< f ∷ a → (b → b) → a

is inhabited, whereas this isn't:

< g ∷ b → (a → b) → a

My next thought was that we could look at, for each hole, which other
holes are in scope at that point.  So we need an environment of
variables that are in scope at a given point:

> type MultiSet a = [a]
>
> type Env a = Map a (MultiSet a)

We only need to be able to extend the mappings from variables to what
variables are in scope, but we also need to be able to recall what
variables are actually in scope.

> type App a m =
>   ( MonadState (Env a) m
>   )

The procedure is as follows:


1. If we encounter a variable, then we just put the variable, @a@,
   into the environment along with all the variables that are in scope
   (in the environment) at this point:

> shift ∷ ∀ a m . Ord a ⇒ App a m ⇒ a → m ()
> shift a = get >>= extend . entry a

> entry ∷ Ord a ⇒ a → Env a → Env a
> entry a env = Map.singleton a (elemsSet env)

2. If we encounter a function type, then we recurse on the type in the
   negative position.  We return the type variable in the the positive
   position as well as the environment at that point.

> closure ∷ Ord a ⇒ Eth.Type a → Env a → (a, Env a)
> closure tp env = runState (solve tp) env

3. Which we use to add to the environment.  The returned type variable
   depends on all the variables in scope at this point.

> unclosure ∷ Ord a ⇒ App a m ⇒ (a, Env a) → m ()
> -- unclosure (a, env) = extend (entry a env)
> unclosure (a, env) = extend $ Map.singleton a (elemsSet env)

4. And finally we just continue recursing on the type in the positive
   position.

All together now:

> solve
>   ∷ ∀ a m . Ord a ⇒ App a m
>   ⇒ Eth.Type a → m a
> solve = \case
>   Eth.Var a → shift a $> a
>   Eth.Fun n p → do
>     env <- closure n <$> get
>     unclosure env
>     solve p
>

Heres an example of a run of the program:

          ⊢ 0 → (1 → 2) → 3
{0: []}       ⊢ (1 → 2) → 3     (shift)
{0: []}|      ⊢  1 → 2          (closure)
{0: []}| {1: []}   ⊢ 2          (shift)
{0: [] , 2: [1]}        ⊢ 3     (unclosure)
{3: [0, 1, 2]}              ⊢   (unclosure)


Utility functions
---

Equivalent to `tell` from the @MonadWriter@:

> extend ∷ Monoid s ⇒ MonadState s m ⇒ s → m ()
> extend s = modify (mappend s)

Flatten all the values into a single set.

> elemsSet ∷ ∀ a . Ord a ⇒ Env a → MultiSet a
> elemsSet = 
> --  = unsafeCoerce @(MultiSet Int) @(MultiSet a)
> --  . traceShowId
> --  . unsafeCoerce @(MultiSet a) @(MultiSet Int)
>   concat
>   . Map.elems
>
> equivalence ∷ Ord a ⇒ Eth.Type a → Env a
> equivalence = execStateEmpty . solve
>
> execStateEmpty ∷ Monoid s ⇒ State s a → s
> execStateEmpty m = execState m mempty
