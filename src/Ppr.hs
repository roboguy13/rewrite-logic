{-# LANGUAGE FlexibleInstances #-}

module Ppr where

class Ppr a where
  ppr :: a -> String

instance Ppr [Char] where
  ppr = id

