{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}

module Theory.Theory where

import           Rewrite
import           Theory.Formula
import           Parser
import           Ppr
import           Theory.Type
import           Theory.Wff

import           Control.Applicative

import           Data.Data
import           Data.Generics.Uniplate.Data hiding (rewrite)

import           Data.Monoid
import           Data.Foldable

import           Data.Profunctor

import           Data.Maybe (fromMaybe)

import Debug.Trace

data EqSide = LHS | RHS deriving (Show)
data EqRewrite = EqSym deriving (Show)

data ProofStep a
  = EqStep      EqRewrite
  | RewriteStep EqSide (Rewrite a)
  -- deriving (Show)

mapProofStep :: (b -> a) -> (a -> b) -> ProofStep a -> ProofStep b
mapProofStep _ _ (EqStep r) = EqStep r
mapProofStep f g (RewriteStep s r) = RewriteStep s (dimap f g r)

checkEqProof :: (Show a, Eq a, Ppr a) => Equality a -> [ProofStep a] -> Either String [a]
checkEqProof eql@(x :=: y) []
  -- case unify x y of
  --   Just _ -> Right [x]
  --   Nothing -> Left $ "RHS and LHS not syntactically equal after rewrite rules: " ++ show eql

  | x == y = Right [x]
  | otherwise = Left $ "RHS and LHS not syntactically equal after rewrite rules: " ++ ppr eql
checkEqProof eql@(x :=: y) (RewriteStep side r:rs) =
  case runRewrite r getSide of
    Nothing -> Left (unlines ["Rewrite failed on " ++ show side ++ ": " ++ getRewriteErr r, "Final goal: " ++ ppr eql])
    Just z ->
      trace ("Rewriting " ++ ppr x ++ " ==to==> " ++ ppr z) $
      -- trace ("  with " ++ ppr eql) $
      fmap (getSide:) (checkEqProof (setSide z) rs)
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

-- parseRule :: [Production'] ->  Parser WffRewrite
-- parseRule prods =
  -- name <- some (parseAlphaUnderscore <|> parseDigit)
  -- many parseSpace
  -- parseChar ':'
  -- some parseSpace

  -- wffA <- parseWff Nothing prods
  -- some parseSpace
  -- parseKeyword "==>"
  -- some parseSpace
  -- wffB <- parseWff Nothing prods
  -- many parseSpace
  -- parseChar ';'
  -- return (name, (wffA :=: wffB))

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
  rules <- parseSection parse
  some parseSpace

  parseKeyword "end theory"
  return (Theory name prods rules numNotation_maybe)
  where
    parseSection p = (:) <$> (many parseSpace >> p) <*> many (some parseSpace >> p)
    numNotation = do
      parseKeyword "numeral notation"
      some parseSpace
      prod <- parseMetaVar'
      some parseSpace
      z <- parseName
      some parseSpace
      s <- parseName
      return (NumProd prod z s)

-- oneRewriteR :: Theory a => Rewrite a
-- oneRewriteR = rewrite $ \x -> getFirst $ fold $ map (\r -> First $ runRewrite (oneTD r) x) rewriteRules

-- oneRewrite :: Theory a => a -> a
-- oneRewrite x = fromMaybe x $ runRewrite oneRewriteR x


-- -- XXX: This might not terminate, depending on the collection of rewrite
-- -- rules
-- fullReduceR :: Theory a => Rewrite a
-- fullReduceR = untilNothingR oneRewriteR

