{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Theory.Formula where

import           Parser
import           Ppr

import           Control.Applicative

import           Data.List


data Formula a
  = Terminal String
  | Juxt [Formula a]
  | FormulaAlts [Formula a]
  | Empty
  | Space
  | MetaVar a
  deriving (Eq, Show, Functor, Foldable, Traversable)

newtype FormulaMetaVar = FormulaMetaVar { getFormulaMetaVar :: String } deriving (Show, Eq)

type Formula' = Formula FormulaMetaVar

instance Parseable FormulaMetaVar where
  parse = fmap FormulaMetaVar parseMetaVar'

instance Ppr (Formula String) where
    ppr (Terminal t) = t
    ppr (Juxt wffs) = unwords (map ppr wffs)
    ppr (FormulaAlts alts) = unwords (intersperse "|" (map ppr alts))
    ppr Empty = "<empty>"
    ppr Space = "<space>"
    ppr (MetaVar v) = '<' : ppr v ++ ">"

data Production a = Production String (Formula a) deriving Show

type Production' = Production FormulaMetaVar

-- data ParsedFormula a
--   = ParsedSymbol Char (ParsedFormula a)
--   | ParsedVar a (ParsedFormula a)
--   | ParsedSpace
--   | ParsedEmpty

parseTerminal' :: Parser String
parseTerminal' = parseName

parseTerminal :: Parser (Formula a)
parseTerminal = fmap Terminal parseTerminal'

parseMetaVar' :: Parser String
parseMetaVar' = do
  parseChar '<'
  cs <- some (parseAlphaUnderscore <|> parseDigit <|> parseChar '-')
  parseChar '>'
  return cs

parseMetaVar :: Parseable a => Parser (Formula a)
parseMetaVar = fmap MetaVar parse

parseJuxt :: Parseable a => Parser (Formula a)
parseJuxt = fmap Juxt $
  (:) <$> parseFormulaNonRec <*> some (some parseSpace >> parseFormulaNonRec)

parseAlts :: Parseable a => Parser (Formula a)
parseAlts = fmap FormulaAlts $
  (:) <$> go <*> some (some parseSpace >> parseChar '|' >> some parseSpace >> go)
  where
    go = parseJuxt <|> parseFormulaNonRec

parseEmpty :: Parser (Formula a)
parseEmpty = do
  parseKeyword "<empty>"
  return Empty

parseFormulaNonRec :: Parseable a => Parser (Formula a)
parseFormulaNonRec = parseTerminal <|> parseEmpty <|> parseWhitespace <|> parseMetaVar
  where
    parseWhitespace = parseKeyword "<space>" >> return Space

parseFormula :: Parseable a => Parser (Formula a)
parseFormula = parseAlts <|> parseJuxt <|> parseFormulaNonRec

instance Parseable a => Parseable (Formula a) where
  parse = parseFormula

parseProduction :: Parseable a => Parser (Production a)
parseProduction = do
  name <- parseMetaVar'

  some parseSpace
  parseKeyword "::="
  some parseSpace

  wff <- parseFormula

  many parseSpace
  parseChar ';'

  return (Production name wff)

lookupProduction :: [Production a] -> String -> Maybe (Formula a)
lookupProduction ps name = lookup name (map prodToPair ps)
  where
    prodToPair (Production x y) = (x, y)

lookupProduction' :: [Production a] -> String -> Maybe (Production a)
lookupProduction' ps name = fmap (Production name) $ lookup name (map prodToPair ps)
  where
    prodToPair (Production x y) = (x, y)

