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

data RuleVar =
  ProdVar String | RuleVar String
  deriving (Show)

data Theory' a
  = Theory
      { theoryName :: String
      , theoryProductions :: [Production']
      , theoryRules :: [(String, Equality (Formula a))]
      , theoryNumNotation :: Maybe String
      }
    deriving Show

type Theory = Theory' RuleVar

theoryRewrites :: (Eq a, Ppr (Formula a)) => Theory' a -> [Rewrite (Formula a)]
theoryRewrites th = map (equalityToRewrite . snd) $ theoryRules th

instance Parseable RuleVar where
  parse = fmap RuleVar ruleVar <|> fmap ProdVar parseMetaVar'
    where
      ruleVar = parseChar '?' >> some (parseAlphaUnderscore <|> parseDigit)

parseRule :: Parser (String, (Equality (Formula RuleVar)))
parseRule = do
  name <- some (parseAlphaUnderscore <|> parseDigit)
  many parseSpace
  parseChar ':'
  some parseSpace

  wffA <- parseFormula
  some parseSpace
  parseKeyword "==>"
  some parseSpace
  wffB <- parseFormula
  many parseSpace
  parseChar ';'
  return (name, (wffA :=: wffB))

parseTheory :: Parser Theory
parseTheory = do
  parseKeyword "begin theory"
  some parseSpace
  name <- parseName
  some parseSpace

  prods <- parseSection parseProduction
  some parseSpace

  numNotation_maybe <- maybeParse (numNotation <* some parseSpace)

  parseKeyword "rules"
  some parseSpace
  rules <- parseSection parseRule
  some parseSpace

  parseKeyword "end theory"
  return (Theory name prods rules numNotation_maybe)
  where
    parseSection p = (:) <$> (many parseSpace >> p) <*> many (some parseSpace >> p)
    numNotation = parseKeyword "numeral notation" >> some parseSpace >> parseMetaVar'

-- oneRewriteR :: Theory a => Rewrite a
-- oneRewriteR = rewrite $ \x -> getFirst $ fold $ map (\r -> First $ runRewrite (oneTD r) x) rewriteRules

-- oneRewrite :: Theory a => a -> a
-- oneRewrite x = fromMaybe x $ runRewrite oneRewriteR x


-- -- XXX: This might not terminate, depending on the collection of rewrite
-- -- rules
-- fullReduceR :: Theory a => Rewrite a
-- fullReduceR = untilNothingR oneRewriteR

