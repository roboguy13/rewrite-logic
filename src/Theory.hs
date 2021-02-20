{-# LANGUAGE TypeFamilies #-}

module Theory where

import           Rewrite

import           Data.Data
import           Data.Generics.Uniplate.Data hiding (rewrite)

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

class Theory a => Unify a where
  type UnifyVar a

  unify :: Equality a -> (Equality a, [(UnifyVar a, a)])

oneRewriteR :: Theory a => Rewrite a
oneRewriteR = rewrite $ \x -> getFirst $ fold $ map (\r -> First $ runRewrite (oneTD r) x) rewriteRules

oneRewrite :: Theory a => a -> a
oneRewrite x = fromMaybe x $ runRewrite oneRewriteR x

-- XXX: This might not terminate, depending on the collection of rewrite
-- rules
fullReduceR :: Theory a => Rewrite a
fullReduceR = untilNothingR oneRewriteR

