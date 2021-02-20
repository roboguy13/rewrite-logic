module Theory where

import           Rewrite

import           Data.Data
import           Data.Generics.Uniplate.Data

import           Data.Monoid
import           Data.Foldable

import           Data.Maybe (fromMaybe)

data Equality a = a :=: a

data EqSide = LHS | RHS deriving (Show)
data EqRewrite = EqSym deriving (Show)

data ProofStep a
  = EqStep      EqRewrite
  | RewriteStep EqSide (Rewrite a)

class Data a => Theory a where
  checkEquality :: Equality a -> [ProofStep a] -> Either String [a]
  rewriteRules :: [Rewrite a]

oneRewrite :: Theory a => a -> a
oneRewrite x = fromMaybe x $ getFirst $ fold $ map (\r -> First $ runRewrite (oneTD r) x) rewriteRules

