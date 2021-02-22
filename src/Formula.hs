{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Formula where

import           Parser
import           Ppr

import           Control.Applicative

import           Data.List


data Formula a
  = Terminal String
  | Juxt [Formula a]
  | FormulaAlts [Formula a]
  | Empty
  | Whitespace
  | MetaVar a
  deriving (Eq, Show)

instance Ppr (Formula String) where
    ppr (Terminal t) = t
    ppr (Juxt wffs) = unwords (map ppr wffs)
    ppr (FormulaAlts alts) = unwords (intersperse "|" (map ppr alts))
    ppr Empty = "<empty>"
    ppr Whitespace = "<whitespace>"
    ppr (MetaVar v) = '<' : ppr v ++ ">"

data Production a = Production a (Formula a) deriving Show

parseTerminal' :: Parser String
parseTerminal' = do
  -- parseFails parseMetaVar
  parseName
  -- some (notOneOf " \n\t\r=")

parseTerminal :: Parser (Formula a)
parseTerminal = fmap Terminal parseTerminal'

parseMetaVar' :: Parser String
parseMetaVar' = do
  parseChar '<'
  cs <- parseName
  -- cs <- some (notOneOf " \n\t\r=")
  -- parseTerminal'
  parseChar '>'
  return cs

parseMetaVar :: Parser (Formula String)
parseMetaVar = fmap MetaVar parseMetaVar'

parseJuxt :: Parser (Formula String)
parseJuxt = fmap Juxt $
  (:) <$> parseFormulaNonRec <*> some (some parseSpace >> parseFormulaNonRec)
  where
    -- go = ((:) <$> parseFormulaNonRec <*> (some parseSpace >> go)) <|> return []

parseAlts :: Parser (Formula String)
parseAlts = fmap FormulaAlts $
  (:) <$> go <*> some (some parseSpace >> parseChar '|' >> some parseSpace >> go)
  where
    go = parseJuxt <|> parseFormulaNonRec

parseEmpty :: Parser (Formula String)
parseEmpty = do
  parseKeyword "<empty>"
  return Empty

parseFormulaNonRec :: Parser (Formula String)
parseFormulaNonRec = parseTerminal <|> parseEmpty <|> parseWhitespace <|> parseMetaVar
  where
    parseWhitespace = parseKeyword "<whitespace>" >> return Whitespace

parseFormula :: Parser (Formula String)
parseFormula = parseAlts <|> parseJuxt <|> parseFormulaNonRec

parseProduction :: Parser (Production String)
parseProduction = do
  name <- parseMetaVar'

  some parseSpace
  parseChar '='
  some parseSpace

  wff <- parseFormula

  many parseSpace
  parseChar ';'

  return (Production name wff)

