{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

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

-- data Wff' a where
--   WffJuxt :: Wff' Void -> Wff' a -> Wff' (Wff' a)
--   WffTerminal :: String -> Wff' a
--   WffEmpty :: Wff' a
--   WffSpace :: Wff' a
--   WffRuleVar :: String -> Wff' a


-- instance Ppr a => Ppr (Wff' a) where
--   ppr (WffJuxt ws) = unwords (map ppr ws)
--   ppr (WffTerminal t) = t
--   ppr WffEmpty = "<empty>"
--   ppr WffSpace = "<space>"
--   ppr (WffRuleVar v) = '?' : v

-- data WffKind = Simple | Compound deriving (Data, Typeable, Show)

-- type family WffVarKind a where
--   WffVarKind String = Simple
--   WffVarKind (Wff' a) = Compound

-- type family WffVarKind a where
--   WffVarKind Simple = String
--   WffVarKind Compound = Wff' Compound (Wff' Simple Void)

-- newtype RuleVar' f a = RuleVar' (f a)

data Wff''
  = WffTerminal String
  | WffEmpty
  | WffSpace
  | WffRuleVar String
  deriving (Show, Data)

data Wff' = WffJuxt Wff'' [Wff''] deriving (Show, Data)

strength1 :: Functor f => (f a, b) -> f (a, b)
strength1 (fa, b) = fmap (,b) fa

class Unify a where
  type UnifyEnv a
  unifyWith :: UnifyEnv a -> a -> a -> Maybe (a, UnifyEnv a)
  substUnifyEnv :: UnifyEnv a -> a -> a

instance Unify Wff' where
  type UnifyEnv Wff' = [(String, Wff')]

  unifyWith env0 x0 y0 = strength1 $ runState (undefined x0 y0) env0
    where
      go' :: Wff'' -> Wff'' -> State (UnifyEnv Wff') (Maybe (Either Wff' Wff''))
      go' (WffTerminal x) (WffTerminal y)
        | x /= y = return Nothing
        | otherwise = return $ Just $ Right $ (WffTerminal x)


      -- go :: Wff' -> Wff' -> State (UnifyEnv Wff') (Maybe Wff')
      -- go (WffJuxt (WffTerminal x) []) (WffJuxt (WffTerminal y) [])
      --   | x /= y = return Nothing
      --   | otherwise = return $ Just $ WffJuxt (WffTerminal x) []

      -- go (WffJuxt x (x':xs)) (WffJuxt y (y':ys)) = do
      --   z <- go (WffJuxt x []) (WffJuxt y [])
      --   zs <- go (WffJuxt x' xs) (WffJuxt y' ys)

      --   return $ WffJuxt <$> z <*> zs

-- deriving instance Show (Wff' Simple)


-- data Wff' (a :: WffKind) where
--   WffJuxt :: [Wff' Simple] -> Wff' Compound
--   WffTerminal :: String -> Wff' Simple
--   WffEmpty :: Wff' Simple
--   WffSpace :: Wff' Simple
--   WffRuleVar :: a -> Wff' (WffVarKind a)

-- deriving instance Typeable (Wff' Simple)

-- deriving instance Data (Wff' Simple)

-- data Wff' a
--   = WffJuxt [a]
--   | WffTerminal String
--   | WffEmpty
--   | WffSpace
--   | WffRuleVar String
--   deriving (Show, Data, Functor)

-- type SimpleWff = Wff' Void
-- type Wff = Wff' (Wff' Void)

-- -- simpleWff :: SimpleWff -> Wff
-- simpleWff :: SimpleWff -> Wff' a
-- simpleWff = fmap absurd

-- -- toSimples :: Wff -> [SimpleWff]
-- toSimples :: Wff' (Wff' a) -> [Wff' a]
-- toSimples (WffJuxt x xs) = x : toSimples xs
-- toSimples (WffTerminal str) = [WffTerminal str]
-- toSimples WffEmpty = [WffEmpty]
-- toSimples WffSpace = [WffSpace]
-- toSimples (WffRuleVar v) = [WffRuleVar v]

-- -- mkJuxt :: SimpleWff -> [SimpleWff] -> Wff

-- mkJuxt :: Wff' Void -> [Wff' Void] -> Wff' (Wff' Void)
-- mkJuxt w [] = simpleWff w
-- mkJuxt w (x:xs) = WffJuxt w (mkJuxt x xs)

-- -- flatten :: Wff' (Wff' a) -> Wff' a
-- -- flatten (WffJuxt x xs) =
-- --   let s = toSimples xs
-- --   in
-- --   _ $ mkJuxt (_ x) _
-- --   -- let s = toSimples xs
-- --   -- in
-- --   -- _

-- instance Semigroup (Wff' a)

-- instance Monoid (Wff' a) where
--   mempty = WffEmpty
--   mappend (WffJuxt xs) (WffJuxt ys) = WffJuxt (xs <> ys)
--   mappend (WffJuxt xs) (WffTerminal str) = WffJuxt (xs <> [WffTerminal str])
--   -- x <> y = WffJuxt (_ x) y


-- -- -- wffApp :: Wff' a -> Wff' a -> Wff' a
-- -- -- wffApp (WffJuxt x xs) ys = WffJuxt x (wffApp xs ys)
-- -- -- wffApp x (WffTerminal str) = _ $ WffJuxt x (WffTerminal str)

-- -- -- toSimples :: Wff'' a -> [SimpleWff a]
-- -- -- toSimples (SimpleWff w) = [w]
-- -- -- toSimples (WffJuxt s w) = s : toSimples w

-- instance Applicative Wff' where
--   pure x = WffJuxt [x]
--   (<*>) = ap

-- instance Monad Wff' where
--   x >>= f = undefined $ fmap f x
--     where
--       flatten :: Wff' (Wff' a) -> Wff' a
--       flatten (WffJuxt []) = WffJuxt []
--       flatten (WffJuxt (x:xs)) =
--         let xs' = flatten (WffJuxt xs)
--         in
--         case x of
--           WffJuxt (y:ys) -> WffJuxt [_]

    -- let x' = f x
    --     xs' = fmap f xs
    -- in
    --   case x' of
    --     WffJuxt p q -> _
    --       -- case xs' of
    --       --   WffJuxt ps qs -> WffJuxt p (WffJuxt _ _)

--   -- x >>= f = flatten (fmap f x)
--     -- where
--     --   flatten :: Wff' (Wff' a) -> Wff' a
--     --   -- flatten x = _ $ toSimples x
--     --   flatten (WffJuxt x xs) = _ -- _ $ toSimples x
--     --     --undefined -- _ $ mkJuxt undefined (toSimples x)

-- --       -- wffSimpleWff :: Wff'' (SimpleWff a1) -> Wff'' a1
-- --       -- wffSimpleWff (SimpleWff s) = SimpleWff (join s)
-- --       -- wffSimpleWff (WffJuxt s w) = WffJuxt (join s) (wffSimpleWff w)

-- --       -- simpleFlatten :: SimpleWff (Wff'' a) -> Wff'' a
-- --       -- simpleFlatten = wffSimpleWff . mkJuxt . sequence . fmap toSimples

-- --       -- flatten :: Wff'' (Wff'' a) -> Wff'' a
-- --       -- flatten = simpleFlatten . fmap mkJuxt . fmap concat . sequence . toSimples . (fmap toSimples)

-- -- -- -- type UnifyEnv a = [(String, a)]

-- -- class Unify a where
-- --   type UnifyEnv a
-- --   unifyWith :: UnifyEnv a -> a -> a -> Maybe (a, UnifyEnv a)
-- --   substUnifyEnv :: UnifyEnv a -> a -> a

-- -- -- instance Unify Void where
-- -- --   type UnifyEnv Void = Void
-- -- --   unifyWith v = absurd v
-- -- --   substUnifyEnv v = absurd v

-- -- unify :: (Monoid (UnifyEnv a), Unify a) => a -> a -> Maybe (a, UnifyEnv a)
-- -- unify = unifyWith mempty

-- -- -- {-
-- -- -- data Wff'' a
-- -- --   = WffJuxt a (Wff'' a)
-- -- --   | ...

-- -- -- type Wff' = Wff'' (Wff'' Void)
-- -- -- -}


-- -- instance Unify (Wff' Void) where
-- --   type UnifyEnv (Wff' Void) = [(String, Wff' Void)]

-- --   unifyWith env0 x0 y0 = strength1 $ runState (go x0 y0) env0
-- --     where
-- --       go _ (WffRuleVar _) = return Nothing -- XXX: "Directional" unification, for now
-- --       go w@(WffRuleVar x) y = do
-- --         -- traceM $ "Trying to unify " ++ ppr w ++ " with " ++ ppr y

-- --         env <- get

-- --         case lookup x env of
-- --           Nothing -> do
-- --             put ((x, y):env)
-- --             return (Just y)
-- --           Just y' ->
-- --             case unify y' y of
-- --               Nothing -> return Nothing
-- --               Just (z, _) -> return (Just z)
-- --       go w@(WffTerminal x) (WffTerminal y)
-- --         | x == y = return (Just w)
-- --       go WffEmpty WffEmpty = return (Just WffEmpty)
-- --       go WffSpace WffSpace = return (Just WffSpace)
-- --       go _ _ = return Nothing

-- -- instance Unify (Wff' (Wff' Void)) where
-- --   type UnifyEnv (Wff' (Wff' Void)) = [(String, Wff' (Wff' Void))]

-- --   -- unifyWith env0 x0 y0 = strength1 $ runState (go x0 y0) env0
-- --   --   where
-- --   --     go :: Wff' (Wff' Void) -> Wff' (Wff' Void) -> State (UnifyEnv (Wff' (Wff' Void))) (Maybe (Wff' (Wff' Void)))
-- --   --     go (WffJuxt x xs) (WffJuxt y ys) = do
-- --   --       env <- get :: _ (UnifyEnv (Wff' (Wff' Void)))
-- --   --       return $ do
-- --   --         (z, env') <- unifyWith (fmap (fmap _) env) x y
-- --   --         -- (zs, env'') <- unifyWith env' xs ys
-- --   --         undefined
-- --   --       -- return (fmap WffJuxt z zs)


-- -- -- instance forall a. (Unify a, Ppr a) => Unify (Wff' a) where
-- -- --   type UnifyEnv (Wff' a) = [(String, Wff' a)]

-- -- --   unifyWith env0 x0 y0 = strength1 $ runState (go x0 y0) env0
-- -- --     where
-- -- --       go :: forall b. Wff' b -> Wff' b -> State (UnifyEnv (Wff' b)) (Maybe (Wff' b))
-- -- --       go _ (WffRuleVar _) = return Nothing -- XXX: "Directional" unification, for now
-- -- --       go w@(WffRuleVar x) y = do
-- -- --         traceM $ "Trying to unify " ++ ppr w ++ " with " ++ ppr y

-- -- --         env <- get

-- -- --         case lookup x env of
-- -- --           Nothing -> do
-- -- --             put ((x, y):env)
-- -- --             return (Just y)
-- -- --           Just y' ->
-- -- --             case unify y' y of
-- -- --               Nothing -> return Nothing
-- -- --               Just (z, _) -> return (Just z)
-- -- --       go w@(WffTerminal x) (WffTerminal y)
-- -- --         | x == y = return (Just w)
-- -- --       go (WffJuxt x xs) (WffJuxt y ys) = do
-- -- --         z <- go (_ x) y
-- -- --         zs <- go xs ys
-- -- --         undefined
-- -- --         -- return (fmap WffJuxt z zs)
-- -- --       -- go (WffRuleVar (WffVarFilled x)) (WffRuleVar (WffVarFilled y)) = undefined

-- -- --       go WffEmpty WffEmpty = return (Just WffEmpty)
-- -- --       go WffSpace WffSpace = return (Just WffSpace)
-- -- --       -- go (WffWff w) y = go (wffParsed w) y
-- -- --       go _ _ = return Nothing







-- -- -- --   substUnifyEnv env w0 = transform go w0
-- -- -- --     where
-- -- -- --       -- go (WffWff w) =
-- -- -- --       --   WffWff w { wffParsed = transform go (wffParsed w) }
-- -- -- --       go w@(WffRuleVar x) =
-- -- -- --         -- trace ("Substituting in " ++ ppr w) $
-- -- -- --         case lookup x env of
-- -- -- --           Nothing -> w
-- -- -- --           Just w' -> w'
-- -- -- --       go w = w

-- -- -- -- instance Unify Wff' where
-- -- -- --   unifyWith env (SimpleWff x) (SimpleWff y) = fmap go (unifyWith env x y)
-- -- -- --     where
-- -- -- --       go = undefined
-- -- -- --   unifyWith env (WffJuxt x xs) (WffJuxt y ys) = do
-- -- -- --     (z, env') <- unifyWith env x y
-- -- -- --     (zs, env'') <- unify env' xs ys
-- -- -- --     return (WffJuxt z zs, env'')

-- -- -- -- wff'EqToRewrite :: Theory' a -> Equality Wff' -> Rewrite Wff'
-- -- -- -- wff'EqToRewrite th eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
-- -- -- --   case unify x z of
-- -- -- --     Just (_, env) -> Just (substUnifyEnv env y)
-- -- -- --     Nothing -> Nothing
-- -- -- --     -- then Just y
-- -- -- --     -- else Nothing

-- -- -- -- -- wff'RewriteWff :: Rewrite Wff' -> Rewrite Wff
-- -- -- -- -- wff'RewriteWff re = rewrite $ \w ->
-- -- -- -- --   case runRewrite re (wffParsed w) of
-- -- -- -- --     Nothing -> Nothing
-- -- -- -- --     Just x -> Just $ w { wffParsed = x }

-- -- -- -- -- wffEqToRewrite :: Theory' a -> Equality Wff -> Rewrite Wff
-- -- -- -- -- wffEqToRewrite th (x :=: y) = wff'RewriteWff (wff'EqToRewrite th (wffParsed x :=: wffParsed y))

-- -- -- -- wffEqToRewrite' :: Theory' a -> Equality Wff -> Rewrite Wff'
-- -- -- -- wffEqToRewrite' th (x :=: y) = wff'EqToRewrite th (wffParsed x :=: wffParsed y)

-- -- -- -- data Wff =
-- -- -- --   Wff
-- -- -- --   { wffName :: String
-- -- -- --   , wffParsed :: Wff'
-- -- -- --   }
-- -- -- --   deriving (Show, Data)

-- -- -- -- instance Ppr Wff where
-- -- -- --     ppr (Wff name w) = '<' : name ++ "> ::= " ++ ppr w

-- -- -- -- data NumProd = NumProd String String String
-- -- -- --   deriving (Show)

-- -- -- -- data Theory' a
-- -- -- --   = Theory
-- -- -- --       { theoryName :: String
-- -- -- --       , theoryProductions :: [Production']
-- -- -- --       , theoryRules :: [(String, Equality a)]
-- -- -- --       , theoryNumNotation :: Maybe NumProd
-- -- -- --       }
-- -- -- --     deriving Show
-- -- -- -- type Theory = Theory' Wff

-- -- -- -- theoryRewrites :: Theory -> [(String, Rewrite Wff')]
-- -- -- -- theoryRewrites th = map (second (wffEqToRewrite' th)) $ theoryRules th

-- -- -- -- instance Parseable RuleVar where
-- -- -- --   parse = fmap RuleVar ruleVar <|> fmap ProdVar parseMetaVar'
-- -- -- --     where
-- -- -- --       ruleVar = parseChar '?' >> some (parseAlphaUnderscore <|> parseDigit)

-- -- -- -- firstNumProd :: [Theory' a] -> Maybe NumProd
-- -- -- -- firstNumProd th =
-- -- -- --     case mapMaybe theoryNumNotation th of
-- -- -- --       (numProd:_) -> Just numProd
-- -- -- --       _ -> Nothing

-- -- -- -- parseTheoryNum' :: NumProd -> Parser Wff'
-- -- -- -- parseTheoryNum' (NumProd name z s) = do
-- -- -- --   digits <- some parseDigit
-- -- -- --   let num = read digits :: Int
-- -- -- --   return $ mkJuxt (map WffTerminal (replicate num s ++ [z]))

-- -- -- -- parseTheoryNum :: NumProd -> Parser Wff
-- -- -- -- parseTheoryNum numProd@(NumProd name _ _) =
-- -- -- --   fmap (Wff name) (parseTheoryNum' numProd)


