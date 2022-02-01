{-# LANGUAGE GADTs, ConstraintKinds, DataKinds, AllowAmbiguousTypes, FlexibleInstances, KindSignatures, TypeOperators, TypeFamilies, QuantifiedConstraints, FlexibleContexts, UndecidableInstances, UndecidableSuperClasses, RankNTypes, BlockArguments, ApplicativeDo, PolyKinds, FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, PartialTypeSignatures, LiberalTypeSynonyms, LambdaCase, InstanceSigs, ImpredicativeTypes #-}
module Trans where

import Control.Monad
import GHC.TypeLits
import GHC.Exts
-- import Control.Monad.IO.Class
-- import Control.Monad.Base
import Data.Constraint
import Data.Type.Equality
import Data.Dynamic
import Data.Proxy
import Type.Reflection
import Unsafe.Coerce
import Trans.Class
import Inductive

type family IsT t m where
  IsT t (t m) = 'True
  IsT t m = 'False

data IsTE t m where
  IsTTrue  :: forall t m m' . (IsT t m ~ 'True, m ~ (t m')) => IsTE t m
  IsTFalse :: forall t m    .  IsT t m ~ 'False => IsTE t m

unsafeEvidence :: forall c . Dict c
unsafeEvidence = unsafeCoerce $ Dict @()

instance MonadBase IO IO where
  liftBase = id

instance (MonadTrans t, MonadBase b m) => MonadBase b (t m) where
  liftBase = lift . liftBase

instance Inductive (MonadBase b) where
  istep _ _ = Sub Dict

class Monad m => MonadIO m where
  liftIO :: IO a -> m a

instance MonadIO IO where
  liftIO = id

instance (MonadTrans t, MonadIO m, Monad m) => MonadIO (t m) where
  liftIO = lift . liftIO

instance Inductive MonadIO where
  istep _ _ = Sub Dict

newtype ReaderT r (m :: * -> *) a = ReaderT { runReaderT :: r -> m a }

instance Functor m => Functor (ReaderT r m) where
  fmap f m = ReaderT $ fmap f . runReaderT m

instance Applicative m => Applicative (ReaderT r m) where
  pure x = ReaderT \_ -> pure x
  mf <*> mx = ReaderT \r -> runReaderT mf r <*> runReaderT mx r

instance Monad m => Monad (ReaderT r m) where
  return x = ReaderT \_ -> return x
  m >>= f  = ReaderT \r -> do
    x <- runReaderT m r
    runReaderT (f x) r

instance MonadTrans (ReaderT r) where
  lift = ReaderT . const

class Monad m => MonadReader' r b m | m -> r where
  ask' :: m r

instance (Monad m, t ~ ReaderT r) => MonadReader' r 'True (t m) where
  ask' = ReaderT return

-- instance
--   ( MonadReader' r (IsT (ReaderT r) m) m
--   , MonadTrans t
--   , IsT (ReaderT r) (t m) ~ 'False
--   ) => MonadReader' r 'False (t m) where
--   ask' = lift $ ask' @r @(IsT (ReaderT r) m)

instance
  ( MonadReader r m
  , MonadTrans t
  , IsT (ReaderT r) (t m) ~ 'False
  ) => MonadReader' r 'False (t m) where
  ask' = lift $ ask

class (MonadReader' r (IsT (ReaderT r) m) m, Monad m) => MonadReader r m | m -> r where
  ask :: m r

instance (MonadReader' r (IsT (ReaderT r) m) m, Monad m) => MonadReader r m where
  ask = ask' @r @(IsT (ReaderT r) m)

instance Typeable (ReaderT r) => Inductive (MonadReader r) where
  istep tc (tt :: TypeRep t) = case eqTypeRep tt $ typeRep @(ReaderT r) of
    Just HRefl -> Sub Dict
    Nothing    ->
      let dct :: forall m . MonadReader r m :- MonadReader r (t m)
          dct = Sub Dict \\ unsafeEvidence @(IsT (ReaderT r) (t m) ~ 'False)
      in  dct