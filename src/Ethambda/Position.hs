{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module Ethambda.Position (position) where

import Data.Bool (bool)
import Data.List (intercalate)
import Control.Monad.Writer
  (MonadWriter, WriterT, Writer, execWriterT, execWriter, tell)
import Control.Monad.Reader
  (MonadReader, ReaderT, Reader, runReaderT, runReader, ask, local)

import Ethambda.Common ((<.))
import Ethambda.Type (Type(Var, Fun))


-- * The 'PosNeg' type.

data PosNeg a = PN
  { negatives :: [a]
  , positives :: [a]
  }

instance Show a => Show (PosNeg a) where
  showsPrec _ (PN n p)
    = "PN"
    <. stuff "neg" n
    <. stuff "pos" p
    <. id

stuff :: Show a => String -> [a] -> String
stuff ttl = \case
  [] -> mempty
  s  -> ttl <> ": " <> intercalate "," (map show s)

instance Semigroup (PosNeg a) where
  PN p n <> PN p' n' = PN (p <> p') (n <> n')

instance Monoid (PosNeg a) where
  mempty = PN mempty mempty

pos :: a -> PosNeg a
pos a = PN mempty (pure a)

neg :: a -> PosNeg a
neg a = PN (pure a) mempty


-- * Core algorithm.
type AppM a m =
  ( MonadWriter (PosNeg a) m
  , MonadReader Bool m
  )

type App0 a x = WriterT (PosNeg a) (Reader Bool) x
type App1 a x = ReaderT Bool (Writer (PosNeg a)) x

execApp0 :: App0 a x -> PosNeg a
execApp0 = (`runReader` True) . execWriterT

execApp1 :: App1 a x -> PosNeg a
execApp1 = execWriter . (`runReaderT` True)

tellPos :: AppM a m => a -> m ()
tellPos = tell . pos

tellNeg :: AppM a m => a -> m ()
tellNeg = tell . neg

tellIt :: AppM a m => a -> m ()
tellIt a = ask >>= bool (tellNeg a) (tellPos a)

positionM :: AppM a m => Type a -> m ()
positionM = \case
  Var a -> tellIt a
  Fun t u -> do
    positionM u
    local not $ positionM t
  _ → error "TODO"

position :: Type a -> PosNeg a
position = execApp0 . positionM
