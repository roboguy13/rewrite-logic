{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Parser where

import           Theorem
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

data BuiltinRewrite = CbvStep | FullCbv deriving (Show)

data Proof
  = Qed
  | ProofBuiltinRewrite GoalSide BuiltinRewrite Proof
  | ProofRewrite GoalSide String Proof
  | ProofGoalRewrite GoalRewrite Proof
  deriving (Show)

data Def =
  TheoremDef String Theorem Proof
  deriving (Show)

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

parseArithNat :: Parser Arith
parseArithNat = fmap fromInteger parseNum

parseArith :: Parser Arith
parseArith = parseArithNat <|> go
  where
    go = parseAdd <|> parseMul

parseBinOp :: String -> Parser a -> Parser a -> Parser (a, a)
parseBinOp op p q = do
  x <- p
  many parseSpace
  parseKeyword op
  many parseSpace
  y <- q
  return (x, y)

parseAdd :: Parser Arith
parseAdd = do
  parseChar '('
  (x, y) <- parseBinOp "+" parseArith parseArith
  parseChar ')'
  return $ Add x y

parseMul :: Parser Arith
parseMul = do
  parseChar '('
  (x, y) <- parseBinOp "*" parseArith parseArith
  parseChar ')'
  return $ Mul x y

parseRewrite :: Parser String
parseRewrite = do
  parseKeyword "rewrite"
  some parseSpace
  parseName

parseBuiltinRewrite :: Parser BuiltinRewrite
parseBuiltinRewrite = parseCbvStep <|> parseFullCbv
  where
    parseCbvStep = do
      parseKeyword "cbv_step"
      return CbvStep

    parseFullCbv = do
      parseKeyword "cbv"
      return FullCbv

parseGoalRewrite :: Parser GoalRewrite
parseGoalRewrite = parseSym -- <|> parseTrans
  where
    parseSym = do
      parseKeyword "sym"
      return GoalSym

parseSided :: Parser a -> Parser (GoalSide, a)
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

opt :: a -> Parser a -> Parser a
opt def p = p <|> return def

parseProof :: Parser Proof
parseProof = go <|> parseQed
  where
    go = many parseSpace >> (parseSidedBuiltinRewrite <|> parseSidedRewrite <|> parseGoalRewrites)

    parseQed = parseKeyword "qed" >> return Qed

    parseSidedBuiltinRewrite = do
      (side, re) <- parseSided parseBuiltinRewrite
      parseNewline
      rest <- parseProof
      return $ ProofBuiltinRewrite side re rest

    parseSidedRewrite = do
      (side, re) <- parseSided parseRewrite
      parseNewline
      rest <- parseProof
      return $ ProofRewrite side re rest

    parseGoalRewrites = do
      re <- parseGoalRewrite
      parseNewline
      rest <- parseProof
      return $ ProofGoalRewrite re rest

parseEquality :: Parser (Arith, Arith)
parseEquality = do
  x <- parseArith
  many parseSpace
  parseChar '='
  many parseSpace
  y <- parseArith
  return (x, y)

parseTheorem :: Parser Def
parseTheorem = do
  parseKeyword "theorem"
  some parseSpace
  name <- parseName

  many parseSpace
  parseChar ':'
  many parseSpace

  (x, y) <- parseEquality

  some (parseSpace <|> parseNewline)

  parseKeyword "proof"

  some (parseSpace <|> parseNewline)

  proof <- parseProof

  return (TheoremDef name (x, y) proof)

parseDefs :: Parser [Def]
parseDefs = do
  x <- parseTheorem
  xs <- (parseNewline >> parseDefs) <|> fmap (const []) parseEndOfInput
  return (x:xs)


