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
  -- deriving (Show)

class Data a => Theory a where
--   checkEquality :: Equality a -> [ProofStep a] -> Either String [a]
  rewriteRules :: [Rewrite a]


class Ppr a where
  ppr :: a -> String

instance Ppr a => Ppr (Equality a) where
  ppr (x :=: y) = unwords [ppr x, "=", ppr y]

checkEqProof :: (Eq a, Ppr a) => Equality a -> [ProofStep a] -> Either String [a]
checkEqProof eql@(x :=: y) []
  | x == y = Right [x]
  | otherwise = Left $ "RHS and LHS not syntactically equal after rewrite rules: " ++ ppr eql
checkEqProof eql@(x :=: y) (RewriteStep side r:rs) =
  case runRewrite r getSide of
    Nothing -> Left (unlines ["Rewrite failed on " ++ show side ++ ": " ++ getRewriteErr r, "Final goal: " ++ ppr eql])
    Just z -> fmap (getSide:) (checkEqProof (setSide z) rs)
  where
    getSide =
      case side of
        LHS -> x
        RHS -> y

    setSide z =
      case side of
        LHS -> (z :=: y)
        RHS -> (x :=: z)
checkEqProof (x :=: y) (EqStep EqSym:rs) = checkEqProof (y :=: x) rs

equalityToRewrite :: (Eq a, Ppr a) => Equality a -> Rewrite a
equalityToRewrite eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
  if z == x
    then Just y
    else Nothing

class Theory a => Unify a where
  type UnifierEnv a

  unify :: Equality a -> (Equality a, UnifierEnv a)

oneRewriteR :: Theory a => Rewrite a
oneRewriteR = rewrite $ \x -> getFirst $ fold $ map (\r -> First $ runRewrite (oneTD r) x) rewriteRules

oneRewrite :: Theory a => a -> a
oneRewrite x = fromMaybe x $ runRewrite oneRewriteR x

-- XXX: This might not terminate, depending on the collection of rewrite
-- rules
fullReduceR :: Theory a => Rewrite a
fullReduceR = untilNothingR oneRewriteR

