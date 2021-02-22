{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Parser where

-- import           Theorem
-- import           Theory
import           Rewrite

import           Control.Monad
import           Control.Applicative

import           Data.Char

type ParseError = String

newtype Parser a = Parser { runParser :: String -> Either ParseError (String, a) }

execParser :: Parser a -> String -> Either ParseError a
execParser p s =
  case runParser p s of
    Right ("", x) -> Right x
    Right (s, _) -> Left $ "Incomplete parse. Remaining string: " <> s
    Left err -> Left $ "Parse error: " <> err

instance Functor Parser where
  fmap f (Parser p) = Parser $ (fmap . fmap) f . p

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Monad Parser where
  return x = Parser (\s -> return (s, x))

  Parser p >>= f = Parser $ \s -> do
    (s', x) <- p s
    runParser (f x) s'

instance Alternative Parser where
  empty = Parser $ const $ Left "Alternative Parser: empty"

  Parser p <|> Parser q = Parser $ \s ->
    case (p s, q s) of
      (Right x, _) -> Right x
      (_, Right y) -> Right y
      (Left a, Left b) -> Left ("[" <> unlines [a <> ";", b] <> "]")


parseCharWhen :: String -> (Char -> Bool) -> Parser Char
parseCharWhen errStr f = Parser $ \case
  (c:cs)
    | f c -> return (cs, c)
  (c:_) -> Left $ "parseCharWhen: Saw " <> show c <> ", expected " <> errStr
  [] -> Left $ "parseCharWhen: Empty. Expected " <> errStr

parseChar :: Char -> Parser Char
parseChar c = parseCharWhen (show c) (== c)

parseAlphaUnderscore :: Parser Char
parseAlphaUnderscore = parseChar '_' <|> parseCharWhen "isAlpha" isAlpha

parseDigit :: Parser Char
parseDigit = parseCharWhen "isDigit" isDigit

parseNum :: Parser Integer
parseNum = read <$> some parseDigit

parseKeyword :: String -> Parser String
parseKeyword [] = return ""
parseKeyword (c:cs) = (:) <$> parseChar c <*> parseKeyword cs

parseEndOfInput :: Parser ()
parseEndOfInput = Parser $ \case
  "" -> Right ("", ())
  _ -> Left "Expected end of input"

parseEOF :: Parser ()
parseEOF = do
  many (parseNewline <|> parseSpace)
  parseEndOfInput

parseFails :: Parser a -> Parser ()
parseFails p = Parser $ \s ->
  case runParser p s of
    Left _ -> Right (s, ())
    Right _ -> Left "parseFails"

-- | Parse name characters occuring after the first character of a name
parseNameChar :: Parser Char
parseNameChar = parseAlphaUnderscore <|> parseDigit

parseName :: Parser String
parseName = (:) <$> parseAlphaUnderscore <*> go
  where
    go = many parseNameChar

parseSpace :: Parser Char
parseSpace = (parseChar ' ' <|> parseChar '\t')

parseNewline :: Parser Char
parseNewline = (parseChar '\n')

parseBinOp :: String -> Parser a -> Parser a -> Parser (a, a)
parseBinOp op p q = do
  x <- p
  many parseSpace
  parseKeyword op
  many parseSpace
  y <- q
  return (x, y)

opt :: a -> Parser a -> Parser a
opt def p = p <|> return def

maybeParse :: Parser a -> Parser (Maybe a)
maybeParse p = fmap Just p <|> return Nothing

notOneOf :: [Char] -> Parser Char
notOneOf cs = parseCharWhen "notOneOf" (`notElem` cs)
