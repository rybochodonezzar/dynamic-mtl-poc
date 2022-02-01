{-# LANGUAGE GADTs, ConstraintKinds, DataKinds, AllowAmbiguousTypes, FlexibleInstances, KindSignatures, TypeOperators, TypeFamilies, QuantifiedConstraints, FlexibleContexts, UndecidableInstances, UndecidableSuperClasses, RankNTypes, BlockArguments, ApplicativeDo, PolyKinds, FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, PartialTypeSignatures, LiberalTypeSynonyms, LambdaCase #-}
module Inductive where

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
import Trans.Class

class Inductive (c :: (* -> *) -> Constraint) where
  istep :: MonadTrans t => TypeRep c -> TypeRep t -> (forall m . c m :- c (t m))

data DictCache m cs where
  DCNil  :: DictCache m '[]
  DCCons :: forall m c cs .
    ( c m
    , Inductive c
    ) => TypeRep c -> DictCache m cs -> DictCache m (c ': cs)

liftDCache :: forall t m cs . MonadTrans t => TypeRep t -> DictCache m cs -> DictCache (t m) cs
liftDCache _ DCNil = DCNil
liftDCache tt (DCCons tc ds) = withDict (istep tc tt @m) $ DCCons tc $ liftDCache tt ds

type family AllC cs x :: Constraint where
  AllC '[] x = ()
  AllC (c ': cs) x = (c x, AllC cs x)

class MkDCache cs m  where
  mkDCache :: DictCache m cs

instance MkDCache '[] m where
  mkDCache = DCNil

instance (MkDCache cs m, Typeable c, Inductive c, c m) => MkDCache (c ': cs) m where
  mkDCache = DCCons typeRep $ mkDCache @cs 

class LookupDCache (cs :: [(* -> *) -> Constraint]) where
  lookupDCache :: DictCache m cs' -> Maybe (Dict (AllC cs m))

instance LookupDCache '[] where lookupDCache _ = Just Dict
instance (Typeable c, LookupDCache cs) => LookupDCache (c ': cs) where
  lookupDCache DCNil = Nothing
  lookupDCache dc =
    let findDC :: forall c' m cs' . Typeable c' => DictCache m cs' -> (Maybe (Dict (c' m)))
        findDC DCNil = Nothing
        findDC (DCCons tc dc') = case testEquality tc (typeRep @c') of
          Nothing   -> findDC @c' dc'
          Just Refl -> Just Dict
    in  case (findDC @c dc, lookupDCache @cs dc) of
      (Just Dict, Just Dict) -> Just Dict
      _ -> Nothing

concatDC :: DictCache m cx -> DictCache m cy -> DictCache m (cx ++ cy)
concatDC DCNil dy = dy
concatDC (DCCons tc ds) dy = DCCons tc $ concatDC ds dy

type family xs ++ ys where
  (x ': xs) ++ ys = x ': (xs ++ ys)
  '[] ++ ys = ys
