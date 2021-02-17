{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Theorem where

import           Rewrite

import           Control.Applicative
import           Data.Maybe (fromMaybe)

data FixF f = FixF (f (FixF f))

-- data Theorem atom rule
--   = Theorem (atom rule)
--   deriving (Show)

data NatF a = Z' | S' a deriving (Show, Eq)

type Nat = FixF NatF

pattern NZ :: Nat
pattern NZ = FixF Z'

pattern NS :: Nat -> Nat
pattern NS x = FixF (S' x)

data Arith
  = ArithNat (NatF Arith)
  | Add Arith Arith
  | Mul Arith Arith
  deriving (Show, Eq)

pattern Z :: Arith
pattern Z = ArithNat Z'

pattern S :: Arith -> Arith
pattern S x = ArithNat (S' x)

arithNat :: Nat -> Arith
arithNat NZ = Z
arithNat (NS x) = S (arithNat x)

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

checkEqPrf :: Theorem -> [Rewrite Arith] -> Either String [Arith]
checkEqPrf (x, y) []
  | x == y = Right [x]
  | otherwise = Left $ "RHS and LHS not syntactically equal after rewrite rules: " ++ show (x, y)
checkEqPrf (x, y) (r:rs) =
  case runRewrite r x of
    Nothing -> Left "Rewrite failed"
    Just x' -> fmap (x:) (checkEqPrf (x', y) rs)


fourPrf :: Either String [Arith]
fourPrf = checkEqPrf (Add 2 2, 4) [cbvStep, cbvStep, cbvStep]


-- arithRewrite (ArithEqual x y) = rewrite $ \z ->
--   if z == x
--     then Just y
--     else Nothing
-- arithRewrite (ArithSym 

-- newtype Arith = Arith (ArithF NatF)




{-
-- data Theorem a
--   = Axiom a
--   | TheoremRewrite (Theorem a) (Rewrite a)

data Proof a
  = AxiomProof a
  | RewriteProof (Proof a) (Rewrite a)

-- data Nat = O | S Nat

-- type NatTheorem = Theorem Nat

check :: Eq a => Rewrite a -> Proof a -> Maybe a
check re (AxiomProof y) = runRewrite re y
check re0 (RewriteProof prf re1) = do
  x <- check re1 prf
  case runRewrite re0 x of
    Just y
      | y == x -> Just y
    _ -> Nothing

check' :: Eq a => a -> Proof a -> Maybe a
check' x = check (rewrite go)
  where
    go y
      | y == x = Just y
      | otherwise = Nothing



data NatAxiom
  = NatAxiom Nat
  | NatEq NatEq

data NatEq
  = NatEqRefl Nat
  -- | NatEqTrans NatEq Nat
  | NatEqSym NatEq

data Nat
  = O
  | S Nat
  | NatAdd Nat Nat
  | NatMul Nat Nat

add_nat :: Rewrite Nat
add_nat = rewrite $ \case
  NatAdd O y -> Just y
  NatAdd (S x) y -> do
    x' <- runRewrite add_nat (NatAdd x y)
    Just $ S x'
  _ -> Nothing
-}

