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

equalityToRewrite :: (Eq a, Ppr a) => Equality a -> Rewrite a
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

data SimpleWff a
  = WffTerminal String
  | WffEmpty
  | WffSpace
  | WffRuleVar (WffVar a)
  deriving (Show, Data, Functor, Traversable, Foldable)

instance Applicative SimpleWff where
  pure = WffRuleVar . pure
  (<*>) = ap

instance Monad SimpleWff where
  WffRuleVar (WffVarName v) >>= _ = WffRuleVar (WffVarName v)
  WffRuleVar (WffVarFilled x) >>= f = f x
  WffTerminal s >>= _ = WffTerminal s
  WffEmpty >>= _ = WffEmpty
  WffSpace >>= _ = WffSpace

data Wff'' a
  = WffJuxt (SimpleWff a) (Wff'' a)
  | SimpleWff (SimpleWff a)
  deriving (Show, Data, Functor)

mkJuxt :: [SimpleWff a] -> Wff'' a
mkJuxt [] = error "mkJuxt: []"
mkJuxt (x:xs) = WffJuxt x (mkJuxt xs)

toSimples :: Wff'' a -> [SimpleWff a]
toSimples (SimpleWff w) = [w]
toSimples (WffJuxt s w) = s : toSimples w

instance Applicative Wff'' where
  pure = SimpleWff . pure
  (<*>) = ap

instance Monad Wff'' where
  x >>= f = flatten (fmap f x)
    where
      wffSimpleWff :: Wff'' (SimpleWff a1) -> Wff'' a1
      wffSimpleWff (SimpleWff s) = SimpleWff (join s)
      wffSimpleWff (WffJuxt s w) = WffJuxt (join s) (wffSimpleWff w)

      simpleFlatten :: SimpleWff (Wff'' a) -> Wff'' a
      simpleFlatten = wffSimpleWff . mkJuxt . sequence . fmap toSimples

      flatten :: Wff'' (Wff'' a) -> Wff'' a
      flatten = simpleFlatten . fmap mkJuxt . fmap concat . sequence . toSimples . (fmap toSimples)

-- type UnifyEnv a = [(String, a)]

strength1 :: Functor f => (f a, b) -> f (a, b)
strength1 (fa, b) = fmap (,b) fa

class Unify a where
  type UnifyEnv a
  unifyWith :: UnifyEnv a -> a -> a -> Maybe (a, UnifyEnv a)
  substUnifyEnv :: UnifyEnv a -> a -> a

unify :: (Monoid (UnifyEnv a), Unify a) => a -> a -> Maybe (a, UnifyEnv a)
unify = unifyWith mempty

instance Unify (SimpleWff a) where
  type UnifyEnv (SimpleWff a) = [(String, SimpleWff a)]

  unifyWith env x0 y0 = strength1 $ runState (go x0 y0) env
    where
      go :: SimpleWff a -> SimpleWff a -> State (UnifyEnv (SimpleWff a)) (Maybe (SimpleWff a))
      go _ (WffRuleVar _) = return Nothing -- XXX: "Directional" unification, for now
      go w@(WffRuleVar x) y = do
        traceM $ "Trying to unify " ++ ppr w ++ " with " ++ ppr y
        env <- get
        case lookup x env of
          Nothing -> do
            put ((x, y):env)
            return (Just y)
          Just y' ->
            case unify y' y of
              Nothing -> return Nothing
              Just (z, _) -> return (Just z)
      go w@(WffTerminal x) (WffTerminal y)
        | x == y = return (Just w)
        -- zs <- fmap sequenceA $ sequence $ zipWith go xs ys
        -- return (fmap WffJuxt zs)
      go WffEmpty WffEmpty = return (Just WffEmpty)
      go WffSpace WffSpace = return (Just WffSpace)
      -- go (WffWff w) y = go (wffParsed w) y
      go _ _ = return Nothing

--   substUnifyEnv env w0 = transform go w0
--     where
--       -- go (WffWff w) =
--       --   WffWff w { wffParsed = transform go (wffParsed w) }
--       go w@(WffRuleVar x) =
--         -- trace ("Substituting in " ++ ppr w) $
--         case lookup x env of
--           Nothing -> w
--           Just w' -> w'
--       go w = w

-- instance Unify Wff' where
--   unifyWith env (SimpleWff x) (SimpleWff y) = fmap go (unifyWith env x y)
--     where
--       go = undefined
--   unifyWith env (WffJuxt x xs) (WffJuxt y ys) = do
--     (z, env') <- unifyWith env x y
--     (zs, env'') <- unify env' xs ys
--     return (WffJuxt z zs, env'')

-- wff'EqToRewrite :: Theory' a -> Equality Wff' -> Rewrite Wff'
-- wff'EqToRewrite th eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
--   case unify x z of
--     Just (_, env) -> Just (substUnifyEnv env y)
--     Nothing -> Nothing
--     -- then Just y
--     -- else Nothing

-- -- wff'RewriteWff :: Rewrite Wff' -> Rewrite Wff
-- -- wff'RewriteWff re = rewrite $ \w ->
-- --   case runRewrite re (wffParsed w) of
-- --     Nothing -> Nothing
-- --     Just x -> Just $ w { wffParsed = x }

-- -- wffEqToRewrite :: Theory' a -> Equality Wff -> Rewrite Wff
-- -- wffEqToRewrite th (x :=: y) = wff'RewriteWff (wff'EqToRewrite th (wffParsed x :=: wffParsed y))

-- wffEqToRewrite' :: Theory' a -> Equality Wff -> Rewrite Wff'
-- wffEqToRewrite' th (x :=: y) = wff'EqToRewrite th (wffParsed x :=: wffParsed y)

-- data Wff =
--   Wff
--   { wffName :: String
--   , wffParsed :: Wff'
--   }
--   deriving (Show, Data)

-- instance Ppr SimpleWff where
--   ppr (WffTerminal t) = t
--   ppr WffEmpty = "<empty>"
--   ppr WffSpace = "<space>"
--   ppr (WffRuleVar v) = '?' : v

-- instance Ppr Wff' where
--   ppr (WffJuxt w ws) = unwords [ppr w, ppr ws]

-- instance Ppr Wff where
--     ppr (Wff name w) = '<' : name ++ "> ::= " ++ ppr w

-- data NumProd = NumProd String String String
--   deriving (Show)

-- data Theory' a
--   = Theory
--       { theoryName :: String
--       , theoryProductions :: [Production']
--       , theoryRules :: [(String, Equality a)]
--       , theoryNumNotation :: Maybe NumProd
--       }
--     deriving Show
-- type Theory = Theory' Wff

-- theoryRewrites :: Theory -> [(String, Rewrite Wff')]
-- theoryRewrites th = map (second (wffEqToRewrite' th)) $ theoryRules th

-- instance Parseable RuleVar where
--   parse = fmap RuleVar ruleVar <|> fmap ProdVar parseMetaVar'
--     where
--       ruleVar = parseChar '?' >> some (parseAlphaUnderscore <|> parseDigit)

-- firstNumProd :: [Theory' a] -> Maybe NumProd
-- firstNumProd th =
--     case mapMaybe theoryNumNotation th of
--       (numProd:_) -> Just numProd
--       _ -> Nothing

-- parseTheoryNum' :: NumProd -> Parser Wff'
-- parseTheoryNum' (NumProd name z s) = do
--   digits <- some parseDigit
--   let num = read digits :: Int
--   return $ mkJuxt (map WffTerminal (replicate num s ++ [z]))

-- parseTheoryNum :: NumProd -> Parser Wff
-- parseTheoryNum numProd@(NumProd name _ _) =
--   fmap (Wff name) (parseTheoryNum' numProd)


