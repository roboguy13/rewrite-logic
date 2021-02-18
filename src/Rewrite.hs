{-# LANGUAGE ScopedTypeVariables #-}

module Rewrite where

import           Prelude hiding (id, (.))

import           Control.Category
import           Control.Monad

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

