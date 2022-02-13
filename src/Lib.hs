{-# LANGUAGE GADTs, ConstraintKinds, DataKinds, AllowAmbiguousTypes, FlexibleInstances, KindSignatures, TypeOperators, TypeFamilies, QuantifiedConstraints, FlexibleContexts, UndecidableInstances, UndecidableSuperClasses, RankNTypes, BlockArguments, PolyKinds, FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, PartialTypeSignatures, LiberalTypeSynonyms, LambdaCase #-}
-- {-# LANGUAGE ApplicativeDo #-} -- with this on it loops forever, dunno why
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
import Inductive
import Trans
import Trans.Class

data Handlers b m where
  HBase  :: (MonadBase m m, Typeable m) => TypeRep m -> DictCache m cs -> Handlers m m
  HTrans :: forall t b m cs .
          ( MonadBase b (t m)
          , MonadTrans t
          ) => (forall f x . t f x -> f x) -> TypeRep (t m) -> DictCache (t m) cs -> Handlers b m -> Handlers b (t m)

instance HasDict (MonadBase b m) (Handlers b m) where
  evidence (HBase _ _)      = Dict
  evidence (HTrans _ _ _ _) = Dict

data DEff b a where
  Pure   :: (forall m . Handlers b m -> m a) -> DEff b a
  Free   :: (forall m . Handlers b m -> m (DEff b a)) -> DEff b a
  Unload :: (Bool -> DEff b a) -> DEff b a
  Load   :: forall cs t b a .
          ( MonadTrans t
          , Inductive (MonadBase b) 
          ) => (forall m a . t m a -> m a) 
            -> (forall m . Dict (Monad m) -> DictCache (t m) cs) 
            -> TypeRep t -> DEff b a -> DEff b a

interpret :: forall b m a . (MonadBase b m) => Handlers b m -> DEff b a -> m a
interpret hs (Pure k) = k hs
interpret hs (Free k) = interpret hs =<< k hs
interpret hs@(HBase tm dcx) (Load i dcy tt m) =
  let ttm = App tt tm
      dcz = (dcy Dict) `concatDC` liftDCache tt dcx
      hs' = HTrans i ttm dcz hs
  in  i $ interpret hs' m 
interpret hs@(HTrans _ tm dcx _) (Load i dcy tt m) =
  let ttm = App tt tm
      dcz = (dcy Dict) `concatDC` liftDCache tt dcx
      hs' = HTrans i ttm dcz hs
  in  i $ interpret hs' m 
interpret hs@(HBase _ _) (Unload k) = interpret hs $ k False
interpret (HTrans i (App tt tm) _ hs) (Unload k) = case hs of
  (HBase tm dc)       -> lift . interpret hs $ k True
  hs@(HTrans _ _ _ _) -> lift . interpret hs $ k True

-- instance Monad b => MonadBase b (DEff b) where
--   liftBase m = Pure \hs -> liftBase m \\ hs

instance Monad m => Functor (DEff m) where
  fmap f (Pure k)         = Pure \hs -> f <$> k hs \\ hs
  fmap f (Free k)         = Free \hs -> fmap f <$> k hs \\ hs
  fmap f (Load i dc tt m) = Load i dc tt $ f <$> m
  fmap f (Unload m)       = Unload \b -> f <$> m b

instance Monad m => Applicative (DEff m) where
  pure x = Pure (\hs -> pure x \\ hs)
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x

instance Monad m => Monad (DEff m) where
  return x = Pure \hs -> return x \\ hs
  (Pure k)         >>= f = Free \hs -> (return . f =<< k hs) \\ hs
  (Free k)         >>= f = Free \hs -> (k hs >>= \x -> (return $ x >>= f)) \\ hs
  (Load i dc tt m) >>= f = Load i dc tt $ m >>= f
  (Unload m)       >>= f = Unload \b -> m b >>= f

---------------

load :: forall cs t b.
    ( MonadTrans t
    , Typeable t
    , MonadBase b b
    , Inductive (MonadBase b)
    , forall m . Monad m => MkDCache cs (t m)
    ) => (forall m a . t m a -> m a) -> DEff b ()
load i = Load i (mkDCache @cs \\) (typeRep @t) $ return ()

unload :: Monad b => DEff b Bool
unload = Unload return

liftD :: forall cs b a . (LookupDCache cs, Typeable b)
      => (forall m . (Typeable m, Monad m, AllC cs m) => m a) -> DEff b (Maybe a)
liftD m = Pure \case
  HBase tm dc -> case lookupDCache @cs dc of
    Nothing   -> return Nothing
    Just Dict -> Just <$> m
  HTrans _ tm dc _ -> case lookupDCache @cs dc of
    Nothing   -> return Nothing
    Just Dict -> Just <$> m \\ tm

class    (Typeable m, Monad m, AllC cs m) => Req m cs
instance (Typeable m, Monad m, AllC cs m) => Req m cs

data Require cs a where
  Require :: (forall m . Dict (Req m cs) -> m a) -> Require cs a

liftD2 :: forall cs b a . (LookupDCache cs, Typeable b) => Require cs a -> DEff b (Maybe a)
liftD2 (Require mf) = Pure \case
  HBase tm dc -> case lookupDCache @cs dc of
    Nothing   -> return Nothing
    Just Dict -> Just <$> mf Dict
  HTrans _ tm dc _ -> case lookupDCache @cs dc of
    Nothing   -> return Nothing
    Just Dict -> Just <$> mf Dict \\ tm

liftBaseD :: b a -> DEff b a
liftBaseD m = Pure \hs -> liftBase m \\ hs

ioHandler :: Handlers IO IO
ioHandler = HBase typeRep $ mkDCache @'[MonadIO]

unload' :: DEff IO ()
unload' = unload >>= \case
  True  -> liftBaseD $ putStrLn "unload OK"
  False -> liftBaseD $ putStrLn "falied to unload: empty stack"

printme :: forall (a :: *) . (Typeable a, Show a) => DEff IO ()
printme = do
  mm <- liftD @'[MonadIO, MonadReader a] $ ask @a >>= liftIO . print
  case mm of
    Nothing -> liftBaseD $ putStrLn "printme failed"
    Just () -> return ()


someFunc :: IO ()
someFunc = interpret ioHandler do
  liftBaseD $ putStrLn "hello"
  unload'
  printme @Int
  load @'[MonadReader Int] @(ReaderT Int) $ flip runReaderT 3
  printme @Int
  unload'
  load @'[MonadReader Int] @(ReaderT Int) $ flip runReaderT 7
  printme @Int
  load @'[MonadReader Int] @(ReaderT Int) $ flip runReaderT 9
  printme @Int
  unload'
  load @'[MonadReader String] @(ReaderT String) $ flip runReaderT "foo"
  printme @String
  printme @Int