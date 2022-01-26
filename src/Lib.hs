{-# LANGUAGE GADTs, ConstraintKinds, DataKinds, AllowAmbiguousTypes, FlexibleInstances, KindSignatures, TypeOperators, TypeFamilies, QuantifiedConstraints, FlexibleContexts, UndecidableInstances, UndecidableSuperClasses, RankNTypes, BlockArguments, ApplicativeDo, PolyKinds, FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, PartialTypeSignatures, LiberalTypeSynonyms, LambdaCase #-}
module Lib
    ( someFunc
    ) where

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

--------------

-- stack version of transformers doesn't support QuantifiedConstraits
class (forall m . Monad m => Monad (t m)) => MonadTrans t where
  lift :: Monad m => m a -> t m a

class (Monad b, Applicative b, Monad m, Applicative m) => MonadBase b m | m -> b where
  liftBase :: b a -> m a

instance {-# OVERLAPS #-} MonadBase IO IO where
  liftBase = id

instance {-# OVERLAPPABLE #-} (MonadTrans t, MonadBase b m) => MonadBase b (t m) where
  liftBase = lift . liftBase

newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

type family IsReaderT m where
  IsReaderT (ReaderT r m) = 'True
  IsReaderT m = 'False

instance Functor m => Functor (ReaderT r m) where
  fmap f m = ReaderT \r -> fmap f $ runReaderT m r

instance Applicative m => Applicative (ReaderT r m) where
  pure x = ReaderT \_ -> pure x
  mf <*> mx = ReaderT \r -> runReaderT mf r <*> runReaderT mx r

instance Monad m => Monad (ReaderT r m) where
  return x = ReaderT \_ -> return x
  m >>= f  = ReaderT \r -> do
    x <- runReaderT m r
    runReaderT (f x) r

-- instance MonadTrans (ReaderT r) where
--   lift = ReaderT . const

-- class MonadReader r m | m -> r where ask :: m r

-- instance (MonadReader r m, Monad m, MonadTrans t) => MonadReader r (t m) where
--   ask = lift ask

-- instance Monad m => MonadReader r (ReaderT r m) where
--   ask = ReaderT return


------- wierd reader -------------

class    (forall t m . (c m (IsT b m), Monad m, MonadTrans t) => c (t m) 'False) => Inductive2 b c
instance (forall t m . (c m (IsT b m), Monad m, MonadTrans t) => c (t m) 'False) => Inductive2 b c

type family IsT t m where
  IsT t (t m) = 'True
  IsT t m = 'False

class Monad m => MonadReader' r m b | m -> r where ask' :: m r

instance Monad m => MonadReader' r (ReaderT r m) 'True where ask' = ReaderT return

instance (MonadTrans t, MonadReader' r m (IsT (ReaderT r) m), Monad m) => MonadReader' r (t m) 'False where
  ask' = undefined -- lift $ ask' @r @(t m) @(IsT (ReaderT r) m)

class MonadReader' r m (IsT (ReaderT r) m) => MonadReader r m | m -> r where
  ask :: m r

instance MonadReader' r m  (IsT (ReaderT r) m) => MonadReader r m where
  ask = undefined -- ask' @(IsT (ReaderT r) m)
-- class MonadReader' (IsT (ReaderT r) m) r m => MonadReader r m | m -> r where
--   ask :: m r

-- instance MonadReader' (IsT (ReaderT r) m) r m => MonadReader r m where
--   ask = ask' @(IsT (ReaderT r) m)

foo :: Dict (Inductive2 (ReaderT r) (MonadReader' r))
foo = Dict

bar :: Dict (Inductive (MonadReader r))
bar = Dict

--------------------------

class Monad m => MonadIO m where liftIO :: IO a -> m a
instance MonadIO IO where liftIO = id
instance (MonadTrans t, MonadIO m, Monad m) => MonadIO (t m) where liftIO = lift . liftIO

--------------------------------

class AllC cs x
instance AllC '[] x
instance (c x, AllC cs x) => AllC (c ': cs) x

data H2 b m where
  HBase  :: MonadBase m m => DictCache m cs -> H2 m m
  HTrans :: forall t b m cs .
          ( MonadBase b (t m)
          , MonadTrans t
          ) => (forall f x . t f x -> f x) -> DictCache (t m) cs -> H2 b m -> H2 b (t m)

instance HasDict (MonadBase b m) (H2 b m) where
  evidence (HBase _)      = Dict
  evidence (HTrans _ _ _) = Dict

class    (forall t m . (c m, Monad m, MonadTrans t) => c (t m)) => Inductive c
instance (forall t m . (c m, Monad m, MonadTrans t) => c (t m)) => Inductive c

data DictCache :: (* -> *) -> [(* -> *) -> Constraint] -> * where
  DCNil  :: DictCache m '[]
  DCCons :: forall m c cs .
    ( c m
    , Monad m
    , Inductive c
    ) => TypeRep c -> DictCache m cs -> DictCache m (c ': cs)

liftDCache :: forall t cs m . (MonadTrans t, Monad m) => DictCache m cs -> DictCache (t m) cs
liftDCache DCNil = DCNil
liftDCache (DCCons tr ds) = DCCons tr (liftDCache ds)

class    MkDCache cs m  where mkDCache :: DictCache m cs
instance MkDCache '[] m where mkDCache = DCNil
instance (MkDCache cs m, Typeable c, Inductive c, c m, Monad m) => MkDCache (c ': cs) m where
  mkDCache = DCCons typeRep $ mkDCache @cs

class LookupDCache (cs :: [(* -> *) -> Constraint]) where
  lookupDCache :: DictCache m cs' -> Maybe (Dict (AllC cs m))

instance LookupDCache '[] where lookupDCache _ = Just Dict
instance (Typeable c, LookupDCache cs) => LookupDCache (c ': cs) where
  lookupDCache DCNil = Nothing
  lookupDCache dc =
    let findDC :: forall c' m cs' . Typeable c' => DictCache m cs' -> (Maybe (Dict (c' m)))
        findDC DCNil = Nothing
        findDC (DCCons tr dc') = case testEquality tr (typeRep @c') of
          Nothing   -> findDC @c' dc'
          Just Refl -> Just Dict
    in  case (findDC @c dc, lookupDCache @cs dc) of
      (Just Dict, Just Dict) -> Just Dict
      _ -> Nothing

type family xs ++ ys where
  (x ': xs) ++ ys = x ': (xs ++ ys)
  '[] ++ ys = ys

concatDC :: DictCache m cx -> DictCache m cy -> DictCache m (cx ++ cy)
concatDC DCNil dy = dy
concatDC (DCCons tr ds) dy = DCCons tr $ concatDC ds dy

data DEff b a where
  Pure   :: (forall m . H2 b m -> m a) -> DEff b a
  Free   :: (forall m . H2 b m -> m (DEff b a)) -> DEff b a
  Unload :: (Bool -> DEff b a) -> DEff b a
  Load   :: forall cs t b m a .
          ( MonadTrans t
          , Inductive (MonadBase b)
          ) => (forall m a . t m a -> m a) -> (forall m . Monad m => DictCache (t m) cs) -> DEff b a -> DEff b a

interpret :: forall b m a . (MonadBase b m) => H2 b m -> DEff b a -> m a
interpret hs (Pure k) = k hs
interpret hs (Free k) = interpret hs =<< k hs
interpret hs@(HBase dc) (Load i dc' m) = i $ interpret (HTrans i (dc' `concatDC` liftDCache dc) hs) m
interpret hs@(HTrans _ dc _) (Load i dc' m) = i $ interpret (HTrans i (dc' `concatDC` liftDCache dc) hs) m
interpret (HBase dc) (Unload k) = interpret (HBase dc) $ k False
interpret (HTrans i _ hs) (Unload k) = case hs of
  (HBase dc)        -> lift . interpret hs $ k True
  hs@(HTrans _ _ _) -> lift . interpret hs $ k True

-- instance Monad b => MonadBase b (DEff b) where
--   liftBase m = Pure \hs -> liftBase m \\ hs

instance Monad m => Functor (DEff m) where
  fmap f (Pure k)      = Pure \hs -> f <$> k hs \\ hs
  fmap f (Free k)      = Free \hs -> fmap f <$> k hs \\ hs
  fmap f (Load i dc m) = Load i dc $ f <$> m
  fmap f (Unload m)    = Unload \b -> f <$> m b

instance Monad m => Applicative (DEff m) where
  pure x = Pure (\hs -> pure x \\ hs)
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x

instance Monad m => Monad (DEff m) where
  return x = Pure \hs -> return x \\ hs
  (Pure k)      >>= f = Free \hs -> (return . f =<< k hs) \\ hs
  (Free k)      >>= f = Free \hs -> (k hs >>= \x -> (return $ x >>= f)) \\ hs
  (Load i dc m) >>= f = Load i dc $ m >>= f
  (Unload m)    >>= f = Unload \b -> m b >>= f

---------------

load :: forall cs t b
     .  (MonadTrans t, MonadBase b b, Inductive (MonadBase b), forall m . Monad m => MkDCache cs (t m))
     => (forall m a . t m a -> m a) -> DEff b ()
load i = Load i (mkDCache @cs) $ return ()

unload :: Monad b => DEff b Bool
unload = Unload return

liftD :: forall cs b a . LookupDCache cs => (forall m . (Monad m, AllC cs m) => m a) -> DEff b (Maybe a)
liftD m = Pure \case
  HBase dc -> case lookupDCache @cs dc of
    Nothing   -> return Nothing
    Just Dict -> Just <$> m
  HTrans _ dc _ -> case lookupDCache @cs dc of
    Nothing   -> return Nothing
    Just Dict -> Just <$> m

liftBaseD :: b a -> DEff b a
liftBaseD m = Pure \hs -> liftBase m \\ hs

ioHandler :: H2 IO IO
ioHandler = HBase $ mkDCache @'[MonadIO]

unload' :: DEff IO ()
unload' = unload >>= \case
  True  -> liftBaseD $ putStrLn "unload OK"
  False -> liftBaseD $ putStrLn "falied to unload: empty stack"

someFunc :: IO ()
someFunc = interpret ioHandler do
  liftBaseD $ putStrLn "hello"
  unload'
  -- load @'[MonadReader Int] @(ReaderT Int) $ flip runReaderT 3