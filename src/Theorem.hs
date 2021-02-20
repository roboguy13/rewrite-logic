{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Theorem where

import           Rewrite

import           Control.Applicative
import           Data.Maybe (fromMaybe)

import           Data.Data

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

pprEquality :: (Arith, Arith) -> String
pprEquality (x, y) = pprArith x ++ " = " ++ pprArith y

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

type Theorem = (Arith, Arith)

data GoalSide = LHS | RHS deriving (Show)
data GoalRewrite = GoalSym deriving (Show)

equalityToRewrite :: (Arith, Arith) -> Rewrite Arith
equalityToRewrite (x, y) = rewriteWithErr (pprEquality (x, y)) $ \z ->
  if z == x
    then Just y
    else Nothing

checkEqPrf :: Theorem -> [Either GoalRewrite (GoalSide, Rewrite Arith)] -> Either String [Arith]
checkEqPrf (x, y) []
  | x == y = Right [x]
  | otherwise = Left $ "RHS and LHS not syntactically equal after rewrite rules: " ++ pprEquality (x, y)
checkEqPrf (x, y) (Right (side, r):rs) =
  case runRewrite r getSide of
    Nothing -> Left (unlines ["Rewrite failed on " ++ show side ++ ": " ++ getRewriteErr r, "Final goal: " ++ pprEquality (x, y)])
    Just z -> fmap (getSide:) (checkEqPrf (setSide z) rs)
  where
    getSide =
      case side of
        LHS -> x
        RHS -> y

    setSide z =
      case side of
        LHS -> (z, y)
        RHS -> (x, z)

checkEqPrf (x, y) (Left GoalSym:rs) = checkEqPrf (y, x) rs

-- fourPrf :: Either String [Arith]
-- fourPrf = checkEqPrf (Add 2 2, 4) [cbvStep, cbvStep, cbvStep]

