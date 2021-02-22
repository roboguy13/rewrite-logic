{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Parser where

-- import           Theorem
-- import           Theory
import           Rewrite
import           Ppr

import           Control.Monad
import           Control.Arrow
import           Control.Applicative

import           Data.Char

type ParseError = String

data ErrorCtx = ErrorCtx
  { errLineNum :: Int
  , errColNum  :: Int
  }

newtype Parser a = Parser { runParser :: (ErrorCtx, String) -> (ErrorCtx, Either ParseError (String, a)) }

initialErrorCtx :: ErrorCtx
initialErrorCtx = ErrorCtx 1 1

instance Ppr ErrorCtx where
  ppr ctx =
    unlines
      [ "On line " ++ show (errLineNum ctx)
      , "at column " ++ show (errColNum ctx)
      ]

errorCtxCaret :: ErrorCtx -> String
errorCtxCaret ctx = replicate (errColNum ctx) ' '

incrCol :: ErrorCtx -> ErrorCtx
incrCol ctx = ctx { errColNum = errColNum ctx + 1 }

incrLine :: ErrorCtx -> ErrorCtx
incrLine ctx = ctx { errLineNum = errLineNum ctx + 1, errColNum = 1 }

incrForChar :: ErrorCtx -> Char -> ErrorCtx
incrForChar ctx '\n' = incrLine ctx
incrForChar ctx _    = incrCol ctx

execParser :: Parser a -> String -> Either ParseError a
execParser p s =
  case runParser p (initialErrorCtx, s) of
    (_, Right ("", x)) -> Right x
    (ctx, Right (s, _)) -> Left $ "Incomplete parse\n" <> ppr ctx
    -- Right (s, _) -> Left $ "Incomplete parse. Remaining string: " <> s
    (ctx, Left err) -> Left $ "Parse error: " <> err <> "\n" <> ppr ctx

instance Functor Parser where
  fmap f (Parser p) = Parser $ (fmap . fmap) (second f) . p

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Monad Parser where
  return x = Parser (\(ctx, s) -> (ctx, return (s, x)))

  Parser p >>= f = Parser $ \(ctx, s) -> do
    case p (ctx, s) of
      (ctx', Right (s', x)) ->
        runParser (f x) (ctx', s')
      (ctx', Left err) -> (ctx', Left err)

instance Alternative Parser where
  empty = Parser $ const $ (initialErrorCtx, Left "Alternative Parser: empty")

  Parser p <|> Parser q = Parser $ \(ctx, s) ->
    case (p (ctx, s), q (ctx, s)) of
      ((ctxP, Right x), _) -> (ctxP, Right x)
      (_, (ctxQ, Right y)) -> (ctxQ, Right y)
      ((_, Left a), (_, Left b)) -> (ctx, Left a)
      -- ((_, Left a), (_, Left b)) -> (ctx, Left ("[" <> unlines [a <> ";", b] <> "]"))


parseCharWhen :: String -> (Char -> Bool) -> Parser Char
parseCharWhen errStr f = Parser $ \case
  (ctx, (c:cs))
    | f c -> (incrForChar ctx c, return (cs, c))
  (ctx, (c:_)) -> (ctx, Left $ "parseCharWhen: Saw " <> show c <> ", expected " <> errStr)
  (ctx, []) -> (ctx, Left $ "parseCharWhen: Empty. Expected " <> errStr)

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
parseEndOfInput = Parser $ second $ \case
  "" -> Right ("", ())
  _ -> Left "Expected end of input"

parseEOF :: Parser ()
parseEOF = do
  many (parseNewline <|> parseSpace)
  parseEndOfInput

-- parseFails :: Parser a -> Parser ()
-- parseFails p = Parser $ \s ->
--   case runParser p s of
--     Left _ -> Right (s, ())
--     Right _ -> Left "parseFails"

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

