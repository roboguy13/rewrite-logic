{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Rewrite where

import           Prelude hiding (id, (.))

import           Control.Category
import           Control.Monad
import           Control.Applicative

import           Control.Monad.State

import           Data.Data
import           Data.Generics.Uniplate.Data hiding (rewrite)

data Transform a b = Transform String (a -> Maybe b)

type Rewrite a = Transform a a

runRewrite :: Rewrite a -> a -> Maybe a
runRewrite (Transform _ f) = f

rewrite :: (a -> Maybe a) -> Rewrite a
rewrite = Transform ""

getRewriteErr :: Rewrite a -> String
getRewriteErr (Transform e _) = e

rewriteWithErr :: String -> (a -> Maybe a) -> Rewrite a
rewriteWithErr = Transform

instance Category Transform where
  id = Transform "" pure
  Transform eF f . Transform eG g = Transform ("{" ++ unlines [eF ++ ";", eG] ++ "}") (f <=< g)

untilNothingR :: forall a. Rewrite a -> Rewrite a
untilNothingR = rewrite . untilNothing

untilNothing :: forall a. Rewrite a -> a -> Maybe a
untilNothing (Transform _ f) x0 = do
  x <- f x0
  return $ go x
  where
    go x =
      case f x of
        Nothing -> x
        Just x' -> go x'

try :: Rewrite a -> Rewrite a
try re = rewrite $ \z ->
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

newtype ProgressM a = ProgressM (State Progress a)
  deriving (Functor, Applicative, Monad, MonadState Progress)

evalProgressM :: ProgressM a -> a
evalProgressM (ProgressM p) = evalState p NoProgress

runProgressM :: ProgressM a -> (a, Progress)
runProgressM (ProgressM p) = runState p NoProgress

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

oneTD :: forall a. Uniplate a => Rewrite a -> Rewrite a
oneTD re = rewrite $ \z ->
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

