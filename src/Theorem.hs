{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}

module Theorem where

import           Rewrite
import           Ppr
import           Parser

import           Control.Applicative
import           Data.Maybe (fromMaybe)

import           Data.Data

import           Theory.Theory
import           Theory.Type
import           Theory.Wff


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
  = BasicRewrite String
  | OneTD String
  deriving (Show)

parseRewrite :: Parser String
parseRewrite = do
  parseKeyword "rewrite"
  some parseSpace
  parseName

parseRewrite' :: Parser ParsedRewrite
parseRewrite' = do
  one_td <- (parseKeyword "one_td" >> some parseSpace >> pure True) <|> pure False
  if one_td
    then fmap OneTD parseRewrite
    else fmap BasicRewrite parseRewrite

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


parseProof :: Theory -> Maybe NumProd -> Parser Proof
parseProof th numProd = go <|> parseQed
  where
    go = many parseSpace >> (parseSidedRewrite <|> parseEqRewrites)

    parseQed = parseKeyword "qed" >> return Qed

    parseSidedRewrite = do
      (side, re) <- parseSided parseRewrite'
      parseNewline
      rest <- parseProof th numProd
      return $ ProofRewrite side re rest

    parseEqRewrites = do
      re <- parseEqRewrite
      parseNewline
      rest <- parseProof th numProd
      return $ ProofEqRewrite re rest

parseEquality :: Theory -> Maybe NumProd -> Parser (Equality Wff)
parseEquality th numProd = do
  x <- parseTheoryWff th numProd
  many parseSpace
  parseChar '='
  many parseSpace
  y <- parseTheoryWff th numProd
  return (x :=: y)

parseTheorem :: Theory -> Maybe NumProd -> Parser Def
parseTheorem th numProd = do
  parseKeyword "theorem"
  some parseSpace
  name <- parseName

  many parseSpace
  parseChar ':'
  many parseSpace

  x :=: y <- parseEquality th numProd

  some (parseSpace <|> parseNewline)

  parseKeyword "proof"

  some (parseSpace <|> parseNewline)

  proof <- parseProof th numProd

  return (TheoremDef name (wffParsed x :=: wffParsed y) proof)

parseDefs :: Theory -> Maybe NumProd -> Parser [Def]
parseDefs th numProd = do
  x <- parseTheorem th numProd
  xs <- (some parseNewline >> parseDefs th numProd) <|> fmap (const []) parseEOF
  return (x:xs)

