{-# LANGUAGE GADTs, ConstraintKinds, DataKinds, AllowAmbiguousTypes, FlexibleInstances, KindSignatures, TypeOperators, TypeFamilies, QuantifiedConstraints, FlexibleContexts, UndecidableInstances, UndecidableSuperClasses, RankNTypes, BlockArguments, ApplicativeDo, PolyKinds, FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, PartialTypeSignatures, LiberalTypeSynonyms, LambdaCase #-}
module Trans.Class where

import Control.Monad
import GHC.TypeLits
import GHC.Exts
import Data.Constraint
import Data.Type.Equality
import Data.Dynamic
import Data.Proxy
import Type.Reflection

class (forall m . Monad m => Monad (t m)) => MonadTrans t where
  lift :: Monad m => m a -> t m a

class (Monad b, Applicative b, Monad m, Applicative m) => MonadBase b m | m -> b where
  liftBase :: b a -> m a