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

import           Theory

data FixF f = FixF (f (FixF f))

-- data Theorem atom rule
--   = Theorem (atom rule)
--   deriving (Show)

data NatF a = Z' | S' a deriving (Show, Eq, Data)

type Nat = FixF NatF

pattern NZ :: Nat
pattern NZ = FixF Z'

pattern NS :: Nat -> Nat
pattern NS x = FixF (S' x)

data BCKW a = BCKW_Val a | B | C | K | W | BCKW_App (BCKW a) (BCKW a)
  deriving (Show, Eq)

data Arith
  = ArithNat (NatF Arith)
  -- | ArithBCKW (BCKW Arith)
  | Add Arith Arith
  | Mul Arith Arith
  deriving (Show, Eq, Data)

pattern Z :: Arith
pattern Z = ArithNat Z'

pattern S :: Arith -> Arith
pattern S x = ArithNat (S' x)

arithNat :: Nat -> Arith
arithNat NZ = Z
arithNat (NS x) = S (arithNat x)

arithNatToInteger :: NatF Arith -> Maybe Integer
arithNatToInteger Z' = Just 0
arithNatToInteger (S' (ArithNat x)) = fmap succ (arithNatToInteger x)
arithNatToInteger _ = Nothing

pprArith :: Arith -> String
pprArith Z = "0"
pprArith (ArithNat n@(S' x)) =
  case arithNatToInteger n of
    Nothing -> "(S " ++ pprArith x ++ ")"
    Just i -> show i

pprArith (Add x y) =
  "(" ++ pprArith x ++ " + " ++ pprArith y ++ ")"

pprArith (Mul x y) =
  "(" ++ pprArith x ++ " * " ++ pprArith y ++ ")"

instance Ppr Arith where
  ppr = pprArith

-- pprEquality :: (Arith, Arith) -> String
-- pprEquality (x, y) = pprArith x ++ " = " ++ pprArith y

-- oneTD :: Rewrite Arith -> Rewrite Arith
-- oneTD re = rewrite $ \z ->
--   case runRewrite re z of
--     Just z' -> Just z'
--     Nothing ->
--       case z of
--         ArithNat Z' -> Nothing
--         ArithNat (S' x) -> fmap (ArithNat . S') (runRewrite (oneTD re) x)
--         Add x y -> applyLR x y (oneTD re) Add
--         Mul x y -> applyLR x y (oneTD re) Mul

instance Num Arith where
  fromInteger 0 = Z
  fromInteger x
    | x < 0 = error "Num Arith: fromInteger (x < 0)"
    | otherwise = S (fromInteger (x-1))

data ArithEqual
  = ArithEqual Arith Arith
  | ArithSym ArithEqual
  | ArithRefl Arith
  | ArithTrans ArithEqual ArithEqual -- | XXX: This must be verified

reduceEq :: ArithEqual -> Maybe (Arith, Arith)
reduceEq = go False
  where
    go True (ArithEqual x y) = Just (y, x)
    go False (ArithEqual x y) = Just (x, y)
    go flipEq (ArithSym eq) = go (not flipEq) eq
    go flipEq (ArithTrans eqA eqB) = do
      (x, y) <- reduceEq eqA
      (y', z) <- reduceEq eqB
      if y == y'
        then go flipEq (ArithEqual x z)
        else Nothing

arithEqualRewrite :: ArithEqual -> Maybe (Rewrite Arith)
arithEqualRewrite eq = do
  (x, y) <- reduceEq eq
  return $ rewrite $ \z ->
    if z == x
      then Just y
      else Nothing

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

-- | One call-by-value evaluation step
cbvStep :: Rewrite Arith
cbvStep = rewrite $ \case
  ArithNat Z' -> Nothing
  ArithNat (S' a) -> fmap (ArithNat . S') (runRewrite cbvStep a)
  Add Z y -> Just y
  Add (S x) y -> Just (S (Add x y))
  Add x y ->
    applyLR x y cbvStep Add
  Mul Z y -> Just Z
  Mul (S x) y -> Just (Add y (Mul x y))
  Mul x y ->
    applyLR x y cbvStep Mul

fullCbv :: Rewrite Arith
fullCbv = rewrite $ \case
  ArithNat {} -> Nothing
  x -> untilNothing cbvStep x

data BuiltinRewrite = CbvStep | FullCbv deriving (Show)

data Proof
  = Qed
  | ProofBuiltinRewrite EqSide BuiltinRewrite Proof
  | ProofRewrite EqSide ParsedRewrite Proof
  | ProofEqRewrite EqRewrite Proof
  deriving (Show)

data Def =
  TheoremDef String (Equality Arith) Proof
  -- deriving (Show)

data ParsedRewrite
  = BasicRewrite String
  | OneTD String
  deriving (Show)
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

parseRewrite' :: Parser ParsedRewrite
parseRewrite' = do
  one_td <- (parseKeyword "one_td" >> some parseSpace >> pure True) <|> pure False
  if one_td
    then fmap OneTD parseRewrite
    else fmap BasicRewrite parseRewrite

parseBuiltinRewrite :: Parser BuiltinRewrite
parseBuiltinRewrite = parseCbvStep <|> parseFullCbv
  where
    parseCbvStep = do
      parseKeyword "cbv_step"
      return CbvStep

    parseFullCbv = do
      parseKeyword "cbv"
      return FullCbv

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


parseArithNat :: Parser Arith
parseArithNat = fmap fromInteger parseNum

parseArith :: Parser Arith
parseArith = parseArithNat <|> go
  where
    go = parseAdd <|> parseMul

parseProof :: Parser Proof
parseProof = go <|> parseQed
  where
    go = many parseSpace >> (parseSidedBuiltinRewrite <|> parseSidedRewrite <|> parseEqRewrites)

    parseQed = parseKeyword "qed" >> return Qed

    parseSidedBuiltinRewrite = do
      (side, re) <- parseSided parseBuiltinRewrite
      parseNewline
      rest <- parseProof
      return $ ProofBuiltinRewrite side re rest

    parseSidedRewrite = do
      (side, re) <- parseSided parseRewrite'
      parseNewline
      rest <- parseProof
      return $ ProofRewrite side re rest

    parseEqRewrites = do
      re <- parseEqRewrite
      parseNewline
      rest <- parseProof
      return $ ProofEqRewrite re rest

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

  return (TheoremDef name (x :=: y) proof)

parseDefs :: Parser [Def]
parseDefs = do
  x <- parseTheorem
  xs <- (some parseNewline >> parseDefs) <|> fmap (const []) parseEOF
  return (x:xs)
