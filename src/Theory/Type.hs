{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

module Theory.Type where

import           Theory.Formula
import           Parser
import           Ppr
import           Rewrite

import           Control.Applicative
import           Control.Arrow
import           Control.Monad.State

import           Data.List
import           Data.Maybe
import           Data.Data

import           Data.Void

import           Data.Generics.Uniplate.Data (transform)

import Debug.Trace

data Equality a = a :=: a deriving (Show, Functor)

instance Ppr a => Ppr (Equality a) where
  ppr (x :=: y) = unwords [ppr x, "=", ppr y]

equalityToRewrite :: (Postprocess a, Eq a, Ppr a) => Equality a -> Rewrite a
equalityToRewrite eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
  if z == x
    then Just y
    else Nothing

data RuleVar =
  ProdVar String | RuleVar String
  deriving (Show)

data WffVar a = WffVarName String | WffVarFilled a deriving (Show, Data, Functor, Traversable, Foldable)

instance Applicative WffVar where
  pure = WffVarFilled
  (<*>) = ap

instance Monad WffVar where
  WffVarName v >>= _ = WffVarName v
  WffVarFilled x >>= f = f x

data Wff'
  = WffTerminal String
  | WffJuxt [Wff']
  -- | WffAlts [Wff']
  | WffEmpty
  | WffSpace
  -- | WffWff Wff
  | WffRuleVar String Wff'
  deriving (Show, Data)

-- Apply once, left-to-right
oneLR :: Rewrite Wff' -> Rewrite Wff'
oneLR re = rewriteWithErr ("oneLR (" <> getRewriteErr re <> ")") go
  where
    wffJuxtCons x (WffJuxt xs) = WffJuxt (x:xs)
    wffJuxtCons x y = flattenWff' (WffJuxt [x, y])

    go :: Wff' -> Maybe Wff'
    go w@(WffJuxt (x:xs)) = runRewrite re w <|> fmap (wffJuxtCons x) (go (WffJuxt xs))
    go w = runRewrite re w

strength1 :: Functor f => (f a, b) -> f (a, b)
strength1 (fa, b) = fmap (,b) fa

class (Monoid (UnifyEnv a)) => Unify a where
  type UnifyEnv a
  unifyWith :: UnifyEnv a -> a -> a -> Maybe (a, UnifyEnv a)
  substUnifyEnv :: UnifyEnv a -> a -> a

unify :: Unify a => a -> a -> Maybe (a, UnifyEnv a)
unify = unifyWith mempty

flattenWff' :: Wff' -> Wff'
flattenWff' (WffJuxt (WffJuxt xs:ys)) =
    case flattenWff' (WffJuxt (map flattenWff' xs)) of
      WffJuxt xs' ->
        case flattenWff' (WffJuxt (map flattenWff' ys)) of
          WffJuxt ys' -> WffJuxt (xs' ++ ys')
flattenWff' (WffJuxt (x:xs)) =
  case flattenWff' (WffJuxt (map flattenWff' xs)) of
    WffJuxt xs' -> WffJuxt (flattenWff' x : xs')
flattenWff' x = x


instance Unify Wff' where
  type UnifyEnv Wff' = [(String, Wff')]

  unifyWith env0 x0 y0 = strength1 $ runState (fmap (fmap flattenWff') (go x0 y0)) env0
    where
      go :: Wff' -> Wff' -> State (UnifyEnv Wff') (Maybe Wff')
      go w@(WffTerminal x) (WffTerminal y)
        | x == y = return $ Just w
      go WffEmpty WffEmpty = return $ Just WffEmpty
      go WffSpace WffSpace = return $ Just WffSpace
      go w@(WffJuxt []) (WffJuxt []) = return $ Just w
      go (WffJuxt (x:xs)) (WffJuxt (y:ys)) = do
        z <- go x y
        zs <- sequence $ zipWith go xs ys
        let r = (:) <$> z <*> sequence zs
        return $ fmap WffJuxt r
      go w@(WffRuleVar x p) (WffRuleVar y q)
        | x == y && isJust (unify p q) = do
            env <- get
            case lookup x env of
              Just z -> return $ Just z
              Nothing -> return $ Just w
        | otherwise = return Nothing  -- Basic unification here
      go (WffRuleVar x p) y = do
        env <- get
        case lookup x env of
          Nothing ->
            case unify p y of
            put ((x,y):env)
            return $ Just y
          Just z -> go y z
      go _ _ = return Nothing

  substUnifyEnv env = flattenWff' . transform go
    where
      go w@(WffRuleVar x) =
        case lookup x env of
          Just y -> y
          Nothing -> w
      go w = w

instance Postprocess Wff' where
  postprocess = flattenWff'

-- instance Unify Wff' where
--   unifyWith env (SimpleWff x) (SimpleWff y) = fmap go (unifyWith env x y)
--     where
--       go = undefined
--   unifyWith env (WffJuxt x xs) (WffJuxt y ys) = do
--     (z, env') <- unifyWith env x y
--     (zs, env'') <- unify env' xs ys
--     return (WffJuxt z zs, env'')

wff'EqToRewrite :: Theory' a -> Equality Wff' -> Rewrite Wff'
wff'EqToRewrite th eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
  case unify x z of
    Just (_, env) -> Just (substUnifyEnv env y)
    Nothing -> Nothing
    -- then Just y
    -- else Nothing

-- -- wff'RewriteWff :: Rewrite Wff' -> Rewrite Wff
-- -- wff'RewriteWff re = rewrite $ \w ->
-- --   case runRewrite re (wffParsed w) of
-- --     Nothing -> Nothing
-- --     Just x -> Just $ w { wffParsed = x }

-- -- wffEqToRewrite :: Theory' a -> Equality Wff -> Rewrite Wff
-- -- wffEqToRewrite th (x :=: y) = wff'RewriteWff (wff'EqToRewrite th (wffParsed x :=: wffParsed y))

wffEqToRewrite' :: Theory' a -> Equality Wff -> Rewrite Wff'
wffEqToRewrite' th (x :=: y) = wff'EqToRewrite th (wffParsed x :=: wffParsed y)

data Wff =
  Wff
  { wffName :: String
  , wffParsed :: Wff'
  }
  deriving (Show, Data)

-- instance Ppr SimpleWff where
--   ppr (WffTerminal t) = t
--   ppr WffEmpty = "<empty>"
--   ppr WffSpace = "<space>"
--   ppr (WffRuleVar v) = '?' : v

instance Ppr Wff' where
  ppr (WffJuxt ws) = unwords (map ppr ws)
  ppr (WffTerminal t) = t
  ppr WffEmpty = "<empty>"
  ppr WffSpace = "<space>"
  ppr (WffRuleVar v) = '?' : v

instance Ppr Wff where
  ppr (Wff name w) = '<' : name ++ "> ::= " ++ ppr w

data NumProd = NumProd String String String
  deriving (Show)

data Theory' a
  = Theory
      { theoryName :: String
      , theoryProductions :: [Production']
      , theoryRules :: [(String, Equality a)]
      , theoryNumNotation :: Maybe NumProd
      }
    deriving Show
type Theory = Theory' Wff

theoryRewrites :: Theory -> [(String, Rewrite Wff')]
theoryRewrites th = map (second (wffEqToRewrite' th)) $ theoryRules th

instance Parseable RuleVar where
  parse = fmap RuleVar ruleVar <|> fmap ProdVar parseMetaVar'
    where
      ruleVar = parseChar '?' >> some (parseAlphaUnderscore <|> parseDigit)

firstNumProd :: [Theory' a] -> Maybe NumProd
firstNumProd th =
    case mapMaybe theoryNumNotation th of
      (numProd:_) -> Just numProd
      _ -> Nothing

parseTheoryNum' :: NumProd -> Parser Wff'
parseTheoryNum' (NumProd name z s) = do
  digits <- some parseDigit
  let num = read digits :: Int
  return $ WffJuxt (map WffTerminal (replicate num s ++ [z]))

parseTheoryNum :: NumProd -> Parser Wff
parseTheoryNum numProd@(NumProd name _ _) =
  fmap (Wff name) (parseTheoryNum' numProd)


