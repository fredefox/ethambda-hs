-- | The core type system.
module Ethambda.Typecheck
  ( typecheck
  ) where

import Prelude hiding (lookup)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Control.Category ((>>>))
import Control.Exception
import Control.Monad.State
import Control.Monad.Catch (MonadThrow(throwM))
import Data.Function

import Ethambda.Type (Type(Fun))
import qualified Ethambda.Type as Type
import Ethambda.Term (Term(App))
import qualified Ethambda.Term as Term

-- * Type checking implementation

type VarMap a = IntMap (Type a)

data Env a = Env
  { envMap ∷ VarMap a
  , envIdx ∷ Int
  }

-- We shouldn't really need this, but @base@ does not provide a
-- version of 'Monoid' without 'mappend'.
instance Semigroup (Env a) where
  Env mp n <> Env mp' n' = Env (mp <> mp') (n + n')

instance Monoid (Env a) where
  mempty = Env mempty 0
  mappend = (<>)

class Nesting a where
  nesting ∷ a → Int

sameNesting ∷ Nesting a ⇒ a → a → Bool
sameNesting = (==) `on` nesting

type TC a m =
  -- We maintain a mapping from variables to their types, as well as
  -- an index indicating how many lambdas we are nested inside.
  ( MonadState (Env a) m
  -- Typechecking may fail.
  , MonadThrow m
  , Nesting a
  )

getMap ∷ TC a m ⇒ m (VarMap a)
getMap = envMap <$> get

getIdx ∷ TC a m ⇒ m Int
getIdx = envIdx <$> get

incrIdx ∷ ∀ a m . TC a m ⇒ m ()
incrIdx = modify go
  where
  go ∷ Env a → Env a
  go (Env m idx) = Env m (succ idx)

decrIdx ∷ ∀ a m . TC a m ⇒ m ()
decrIdx = modify go
  where
  go ∷ Env a → Env a
  go (Env m idx) = Env m (pred idx)

liftMaybe ∷ MonadThrow m ⇒ Exception e ⇒ e → Maybe a → m a
liftMaybe e = \case
  Nothing → throwM e
  Just a → pure a

lookup
 ∷ Exception e ⇒ MonadThrow m
 ⇒ e → Int → IntMap v → m v
lookup e a = liftMaybe e . IntMap.lookup a

lookupVar
 ∷ ∀ a m e . Exception e ⇒ TC a m
 ⇒ e → a → m (Type a)
-- lookupVar e = getMap >>= _lookup e
lookupVar e a = do
  idx ← getIdx
  mp  ← getMap
  lookup e (nesting a + idx) mp

data AppException
  = VarNotFoundInEnv
  | IncompatibleTypes -- (Type a) (Type a)

instance Show AppException where
  show = \case
    VarNotFoundInEnv → "Variable not found in environment"
    IncompatibleTypes → "Incompatible types"

instance Exception AppException where

weaken ∷ TC a m ⇒ m ()
weaken = incrIdx

strengthen ∷ TC a m ⇒ m ()
strengthen = decrIdx

weakened ∷ TC a m ⇒ m b → m b
weakened m = do
  weaken
  x ← m
  strengthen
  pure x

tcLambda ∷ TC a m ⇒ Term a → m (Type a)
tcLambda = weakened . tc

sameType ∷ TC a m ⇒ Type a → Type a → m ()
Type.Var a `sameType` Type.Var b
  = if a `sameNesting` b then pure () else throwM IncompatibleTypes
Fun a0 a1 `sameType` Fun b0 b1
  = id <$ a0 `sameType` b0 <*> a1 `sameType` b1
Type.Constr a `sameType` Type.Constr b = a `sameTFormer` b
_ `sameType` _ = throwM IncompatibleTypes

sameTFormer ∷ TC a m ⇒ Type.Constr a → Type.Constr a → m ()
Type.Product a0 a1 `sameTFormer` Type.Product b0 b1
  = id <$ a0 `sameType` b0 <*> a1 `sameType` b1
Type.Sum a0 a1 `sameTFormer` Type.Sum b0 b1
  = id <$ a0 `sameType` b0 <*> a1 `sameType` b1
Type.Unit `sameTFormer` Type.Unit = pure ()
_ `sameTFormer` _ = throwM IncompatibleTypes

checkCompatible ∷ TC a m ⇒ Type a → Type a → m (Type a)
checkCompatible t u = case t of
  Type.Var{}    → throwM IncompatibleTypes
  Fun t0 t1     → sameType t0 u *> pure t1
  Type.Constr{} → throwM IncompatibleTypes  

tcApp ∷ TC a m ⇒ Term a → Term a → m (Type a)
tcApp t u = do
  tT ← tc t
  uT ← tc u
  checkCompatible tT uT

fresh ∷ TC a m ⇒ m a
fresh = error "TODO fresh"

tcSum ∷ TC a m ⇒ Term a → m (Type a, Type a)
tcSum t = do
  x ← fresh
  tT ← tc t
  pure $ (Type.Var x, tT)

tcConstr ∷ TC a m ⇒ Term.Constr a → m (Type.Constr a)
tcConstr = \case
  Term.Unit        → pure                     $  Type.Unit
  Term.Product t u → Type.Product            <$> tc t    <*> tc u
  Term.Injl t      → uncurry       Type.Sum  <$> tcSum t
  Term.Injr t      → uncurry (flip Type.Sum) <$> tcSum t

tc ∷ TC a m ⇒ Term a → m (Type a)
tc = \case
  Term.Var a    → lookupVar VarNotFoundInEnv a
  Term.Fun t    → tcLambda t
  App t u       → tcApp t u
  Term.Constr e → Type.Constr <$> tcConstr e


-- * Implementation of 'TC'

newtype SimpleVar = SimpleVar Int

instance Nesting SimpleVar where
  nesting (SimpleVar idx) = idx

type TypeChecker m a
  = StateT (Env SimpleVar) m a

runTypechecker ∷ MonadThrow m ⇒ TypeChecker m a → m a
runTypechecker = (`evalStateT` mempty)

typecheck
  ∷ MonadThrow m
  ⇒ Term SimpleVar → m (Type SimpleVar)
typecheck = tc >>> runTypechecker
