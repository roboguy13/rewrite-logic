{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}

module Theorem where

import           Rewrite
import           Ppr
import           Parser

import           Control.Applicative
import           Control.Monad
import           Data.Maybe (fromMaybe)

import           Data.Data

import           Theory.Theory
import           Theory.Type
import           Theory.Wff
import           Theory.Formula

import Debug.Trace

-- | Apply left-to-right
applyLR :: a -> a -> Rewrite a -> (a -> a -> r) -> Maybe r
applyLR x y re combine =
  let xM = runRewrite re x
      yM = runRewrite re y

      x' = fromMaybe x xM
      y' = fromMaybe y yM
  in
  case (xM, yM) of
    (Nothing, Nothing) -> Nothing
    (Just _, Just _) -> Just (combine x' y)
    _ -> Just (combine x' y')

data Proof
  = Qed
  | ProofRewrite EqSide ParsedRewrite Proof
  | ProofEqRewrite EqRewrite Proof
  deriving (Show)

data Def =
  TheoremDef String (Equality Wff') Proof

data ParsedRewrite
  = BasicRewrite String (Maybe UnifierEnv)
  | OneTD String (Maybe UnifierEnv)
  deriving (Show)

parseWithClause :: Maybe NumProd -> [Production'] -> Parser UnifierEnv
parseWithClause numProd prods = do
  parseKeyword "with"
  some parseSpace

  formula <- parse :: Parser Formula'


  let --go = ((:) <$> parseWithBinding <*> (parseChar ',' *> some parseSpace *> go)) <|> fmap (:[]) parseWithBinding
      go = fmap (:[]) parseWithBinding

      parseWithBinding = do
        var <- parse :: Parser UnifierVar
        some parseSpace
        parseKeyword ":="
        some parseSpace
        wff <- parseWff' numProd prods formula :: Parser Wff'
        return (var, wff)

  some parseSpace

  parseChar '['
  some parseSpace
  env <- go
  some parseSpace
  parseChar ']'

  traceM $ "unifier env = " ++ show env
  return (UnifierEnv env)

parseRewrite :: Maybe NumProd -> [Production'] -> Parser (String, Maybe UnifierEnv)
parseRewrite numProd prods = do
  parseKeyword "rewrite"
  some parseSpace
  name <- parseName
  withClause <- opt Nothing (some parseSpace *> fmap Just (parseWithClause numProd prods))
  return (name, withClause)


parseRewrite' :: Maybe NumProd -> [Production'] -> Parser ParsedRewrite
parseRewrite' numProd prods = do
  one_td <- (parseKeyword "one_td" >> some parseSpace >> pure True) <|> pure False
  if one_td
    then fmap (uncurry OneTD) (parseRewrite numProd prods)
    else fmap (uncurry BasicRewrite) (parseRewrite numProd prods)

parseEqRewrite :: Parser EqRewrite
parseEqRewrite = parseSym -- <|> parseTrans
  where
    parseSym = do
      parseKeyword "sym"
      return EqSym

parseSided :: Parser a -> Parser (EqSide, a)
parseSided p = lhs <|> rhs
  where
    lhs = do
      parseKeyword "lhs:"
      some parseSpace
      fmap (LHS,) p
    rhs = do
      parseKeyword "rhs:"
      some parseSpace
      fmap (RHS,) p


parseProof :: Maybe NumProd -> [Production'] -> Parser Proof
parseProof numProd prods = go <|> parseQed
  where
    go = many parseSpace >> (parseSidedRewrite <|> parseEqRewrites)

    parseQed = parseKeyword "qed" >> return Qed

    parseSidedRewrite = do
      (side, re) <- parseSided (parseRewrite' numProd prods)
      parseNewline
      rest <- parseProof numProd prods
      return $ ProofRewrite side re rest

    parseEqRewrites = do
      re <- parseEqRewrite
      parseNewline
      rest <- parseProof numProd prods
      return $ ProofEqRewrite re rest

parseEquality :: Maybe NumProd -> [Production'] -> Parser (Equality Wff)
parseEquality numProd prods = do
  x <- parseTheoryWff numProd prods
  many parseSpace
  parseChar '='
  many parseSpace
  y <- parseTheoryWff numProd prods
  return (x :=: y)

parseTheorem :: Maybe NumProd -> [Production'] -> Parser Def
parseTheorem numProd prods = do
  parseKeyword "theorem"
  some parseSpace
  name <- parseName

  many parseSpace
  parseChar ':'
  many parseSpace

  x :=: y <- parseEquality numProd prods

  some (parseSpace <|> parseNewline)

  parseKeyword "proof"

  some (parseSpace <|> parseNewline)

  proof <- parseProof numProd prods

  return (TheoremDef name (wffParsed x :=: wffParsed y) proof)

parseDefs :: Maybe NumProd -> [Production'] -> Parser [Def]
parseDefs numProd prods = do
  x <- parseTheorem numProd prods
  xs <- (some parseNewline >> parseDefs numProd prods) <|> fmap (const []) parseEOF
  return (x:xs)

