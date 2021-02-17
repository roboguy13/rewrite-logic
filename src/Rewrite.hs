{-# LANGUAGE ScopedTypeVariables #-}

module Rewrite where

import           Prelude hiding (id, (.))

import           Control.Category
import           Control.Monad

newtype Transform a b = Transform (a -> Maybe b)

type Rewrite a = Transform a a

runRewrite :: Rewrite a -> a -> Maybe a
runRewrite (Transform f) = f

rewrite :: (a -> Maybe a) -> Rewrite a
rewrite = Transform

instance Category Transform where
  id = Transform pure
  Transform f . Transform g = Transform (f <=< g)

untilNothing :: forall a. Rewrite a -> a -> Maybe a
untilNothing (Transform f) x0 = do
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

