module Formula where

import           Parser

import           Control.Applicative

data Formula a
  = Terminal String
  | Juxt [Formula a]
  | FormulaAlts [Formula a]
  | Empty
  | Whitespace
  | MetaVar a

data Production a = Production a (Formula a)

parseTerminal' :: Parser String
parseTerminal' = do
  c <- notOneOf "?"
  cs <- some (notOneOf " \n\t\r=")
  return (c:cs)

parseTerminal :: Parser (Formula a)
parseTerminal = fmap Terminal parseTerminal'

parseMetaVar' :: Parser String
parseMetaVar' = do
  parseChar '?'
  parseTerminal'

parseMetaVar :: Parser (Formula String)
parseMetaVar = fmap MetaVar parseMetaVar'

parseJuxt :: Parser (Formula String)
parseJuxt = fmap Juxt $
  (:) <$> parseFormulaNonRec <*> many (parseSpace >> parseFormula)

parseEmpty :: Parser (Formula String)
parseEmpty = do
  parseKeyword "?empty"
  return Empty

parseFormulaNonRec :: Parser (Formula String)
parseFormulaNonRec = parseTerminal <|> parseMetaVar <|> parseEmpty <|> parseWhitespace
  where
    parseWhitespace = parseKeyword "?whitespace" >> return Whitespace

parseFormula :: Parser (Formula String)
parseFormula = parseFormulaNonRec <|> parseJuxt

parseProduction :: Parser (Production String)
parseProduction = do
  name <- parseMetaVar'

  some parseSpace
  parseChar '='
  some parseSpace

  wff <- parseFormula
  parseNewline

  return (Production name wff)

