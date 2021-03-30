{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Rewrite where

import           Prelude hiding (id, (.))

import           Control.Category
import           Control.Monad
import           Control.Applicative

import           Control.Monad.Identity
import           Control.Monad.State

import           Data.Data
import           Data.Profunctor
import           Data.Generics.Uniplate.Data hiding (rewrite)

data Transform a b = Transform String (a -> Maybe b)

type Rewrite a = Transform a a

instance Profunctor Transform where
  dimap f g (Transform s t) = Transform s (fmap g . t . f)

instance Functor (Transform a) where
  fmap f (Transform s t) = Transform s (fmap f . t)

runRewrite :: Rewrite a -> a -> Maybe a
runRewrite (Transform _ f) = f

class Postprocess a where
  postprocess :: a -> a

instance Postprocess String where
  postprocess = id

-- rewrite :: Postprocess a => (a -> Maybe a) -> Rewrite a
-- rewrite = Transform "" . (fmap postprocess .)

getRewriteErr :: Rewrite a -> String
getRewriteErr (Transform e _) = e

rewriteWithErr :: Postprocess a => String -> (a -> Maybe a) -> Rewrite a
rewriteWithErr e = Transform e . (fmap postprocess .)

instance Category Transform where
  id = Transform "" pure
  Transform eF f . Transform eG g = Transform ("{" ++ unlines [eF ++ ";", eG] ++ "}") (f <=< g)

untilNothingR :: forall a. Postprocess a => Rewrite a -> Rewrite a
untilNothingR re = rewriteWithErr ("untilNothingR (" <> getRewriteErr re <> ")") $ untilNothing re

untilNothing :: forall a. Postprocess a => Rewrite a -> a -> Maybe a
untilNothing (Transform _ f) x0 = do
  x <- f x0
  return $ go x
  where
    go x =
      case f x of
        Nothing -> x
        Just x' -> go x'

try :: Postprocess a => Rewrite a -> Rewrite a
try re = rewriteWithErr ("try " <> getRewriteErr re) $ \z ->
  case runRewrite re z of
    Nothing -> Just z
    z' -> z'

data Progress = MadeProgress | NoProgress

instance Semigroup Progress where
  (<>) = mappend

instance Monoid Progress where
  mempty = NoProgress
  mappend NoProgress NoProgress = NoProgress
  mappend _ _ = MadeProgress

newtype ProgressT m a = ProgressM (StateT Progress m a)
  deriving (Functor, Applicative, Monad, MonadState Progress, Alternative, MonadTrans)

type ProgressM = ProgressT Identity

-- newtype ProgressM a = ProgressM (State Progress a)

evalProgressM :: ProgressM a -> a
evalProgressM (ProgressM p) = evalState p NoProgress

evalProgressT :: Monad m => ProgressT m a -> m a
evalProgressT (ProgressM p) = evalStateT p NoProgress

runProgressM :: ProgressM a -> (a, Progress)
runProgressM (ProgressM p) = runState p NoProgress

runProgressT :: Monad m => ProgressT m a -> m (a, Progress)
runProgressT (ProgressM p) = runStateT p NoProgress

doIfNoProgress :: (a -> Maybe a) -> (a -> ProgressM a)
doIfNoProgress f x = do
  p <- get
  case p of
    MadeProgress -> return x
    NoProgress ->
      case f x of
        Nothing -> return x
        Just x' -> do
          put MadeProgress
          return x'

oneTD :: forall a. (Postprocess a, Uniplate a) => Rewrite a -> Rewrite a
oneTD re = rewriteWithErr ("one_td (" <> getRewriteErr re <> ")") $ \z ->
  case runProgressM (go z) of
    (_, NoProgress) -> Nothing
    (r, MadeProgress) -> Just r

  where
    f = runRewrite re

    go :: a -> ProgressM a
    go x = do
      p <- get
      case p of
        MadeProgress -> return x
        NoProgress ->
          case children x of
            [] -> return x
            _  -> descendM (doIfNoProgress f >=> go) x

