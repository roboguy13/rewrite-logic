{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Theory where

import           Rewrite
import           Formula
import           Parser
import           Ppr

import           Control.Applicative

import           Data.Data
import           Data.Generics.Uniplate.Data hiding (rewrite)

import           Data.Monoid
import           Data.Foldable

import           Data.Maybe (fromMaybe)

data Equality a = a :=: a deriving Show

data EqSide = LHS | RHS deriving (Show)
data EqRewrite = EqSym deriving (Show)

data ProofStep a
  = EqStep      EqRewrite
  | RewriteStep EqSide (Rewrite a)
  -- deriving (Show)

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
        LHS -> z :=: y
        RHS -> x :=: z
checkEqProof (x :=: y) (EqStep EqSym:rs) = checkEqProof (y :=: x) rs

equalityToRewrite :: (Eq a, Ppr a) => Equality a -> Rewrite a
equalityToRewrite eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
  if z == x
    then Just y
    else Nothing

data Theory a
  = Theory
      { theoryName :: String
      , theoryProductions :: [Production a]
      , theoryRules :: [Equality (Formula a)]
      }
    deriving Show

theoryRewrites :: (Eq a, Ppr (Formula a)) => Theory a -> [Rewrite (Formula a)]
theoryRewrites th = map equalityToRewrite $ theoryRules th

parseRule :: Parser (Equality (Formula String))
parseRule = do
  wffA <- parseFormula
  some parseSpace
  parseKeyword "==>"
  some parseSpace
  wffB <- parseFormula
  many parseSpace
  parseChar ';'
  return (wffA :=: wffB)

parseTheory :: Parser (Theory String)
parseTheory = do
  parseKeyword "begin theory"
  some parseSpace
  name <- parseName
  some parseNewline

  prods <- parseSection parseProduction
  some parseNewline

  parseKeyword "rules"
  some parseNewline
  rules <- parseSection parseRule
  some parseNewline

  parseKeyword "end theory"
  return (Theory name prods rules)
  where
    parseSection p = (:) <$> (many parseSpace >> p) <*> many (some parseNewline >> many parseSpace >> p)

-- oneRewriteR :: Theory a => Rewrite a
-- oneRewriteR = rewrite $ \x -> getFirst $ fold $ map (\r -> First $ runRewrite (oneTD r) x) rewriteRules

-- oneRewrite :: Theory a => a -> a
-- oneRewrite x = fromMaybe x $ runRewrite oneRewriteR x


-- -- XXX: This might not terminate, depending on the collection of rewrite
-- -- rules
-- fullReduceR :: Theory a => Rewrite a
-- fullReduceR = untilNothingR oneRewriteR

