{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

-- {-# OPTIONS_GHC -Wall -Wno-unused-imports -Wno-unused-matches #-}

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

import           Data.Coerce

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

newtype UnifierVar = UnifierVar String deriving (Show, Eq)

instance Ppr UnifierVar where
  ppr (UnifierVar str) = '?' : str

instance Parseable UnifierVar where
  parse = parseChar '?' *> fmap UnifierVar parseName

newtype WffRewriteLhs = WffRewriteLhs { getWffRewriteLhs :: Formula (String, UnifierVar) } deriving (Show)

data WffRewrite =
  WffRewrite
    { wffRewriteName :: String
    , wffRewriteLhs :: WffRewriteLhs
    , wffRewriteRhs :: Formula UnifierVar
    } deriving (Show)

wffRewriteScheme :: WffRewrite -> Formula'
wffRewriteScheme WffRewrite { wffRewriteLhs } = fmap go (getWffRewriteLhs wffRewriteLhs)
  where
    go (name, _) = FormulaMetaVar name

instance Parseable WffRewrite where
  parse = do
    name <- parseName

    some parseSpace

    scheme <- parse :: Parser Formula'
    parseChar ':'
    some parseSpace

    lhs0 <- parse :: Parser (Formula UnifierVar)

    uenv <- case checkSchemeMatch scheme lhs0 of
              Left err -> parseError err
              Right x -> return x

    lhs <- case go uenv lhs0 of
             Left err -> parseError err
             Right x -> return $ WffRewriteLhs x

    rhs <- parse :: Parser (Formula UnifierVar)

    return (WffRewrite name lhs rhs)

    where
      go :: [(UnifierVar, FormulaMetaVar)] -> Formula UnifierVar -> Either String (Formula (String, UnifierVar))
      go uenv (Juxt xs) = Juxt <$> mapM (go uenv) xs
      go uenv (FormulaAlts xs) = FormulaAlts <$> mapM (go uenv) xs
      go _ (Terminal str) = return $ Terminal str
      go _ Space = return Space
      go _ Empty = return Empty
      go uenv (MetaVar uvar) =
        case lookup uvar uenv of
          Nothing -> Left $ "!!! Internal error: In rewrite rule: Cannot find UnifierVar " ++ ppr uvar ++ " in environment"
          Just x -> Right $ MetaVar (getFormulaMetaVar x, uvar)

checkSchemeMatch :: Formula' -> Formula UnifierVar -> Either String [(UnifierVar, FormulaMetaVar)]
checkSchemeMatch fX fY = execStateT (go fX fY) []
  where
    go :: Formula' -> Formula UnifierVar -> StateT [(UnifierVar, FormulaMetaVar)] (Either String) ()
    go (Terminal a) (Terminal b) = when (a /= b) $ lift $ Left $ "In rewrite rule: the terminal from the scheme " ++ show a ++ " does not match the terminal from the LHS " ++ show b
    go (Juxt xs) (Juxt ys)       = sequence_ $ map lift (zipWith checkSchemeMatch xs ys)
    go Empty Empty               = return ()
    go Space Space               = return ()
    go (MetaVar prodName) (MetaVar uvar) = do
      env <- get
      case lookup uvar env of
        Just prodName'
          | prodName' /= prodName -> lift $ Left $
              unlines ["In rewrite rule: Variable is used for two different productions:"
                      ,"  Variable:          " ++ show uvar
                      ,"  First production:  " ++ show prodName'
                      ,"  Second production: " ++ show prodName
                      ]
          | otherwise -> return ()
        Nothing -> put ((uvar, prodName):env)

    -- TODO: Add more informative error messages for these cases
    go _ _                       = lift $ Left "In rewrite rule: Scheme and LHS do not match"

newtype UnifierEnv = UnifierEnv [(UnifierVar, Wff')]

emptyUnifierEnv :: UnifierEnv
emptyUnifierEnv = UnifierEnv []

insertUnifierVar :: UnifierVar -> Wff' -> UnifierEnv -> Either Wff' UnifierEnv
insertUnifierVar uv@(UnifierVar var) wff uenv@(UnifierEnv env) =
  case lookupUnifierVar uv uenv of
    Just prevWff -> Left prevWff
    Nothing -> Right $ UnifierEnv ((uv, wff):env)

lookupUnifierVar :: UnifierVar -> UnifierEnv -> Maybe Wff'
lookupUnifierVar (UnifierVar var) (UnifierEnv env) = lookup var (coerce env)

wffRewriteLhsParser :: Maybe NumProd -> [Production'] -> WffRewrite -> Either String (Parser (WffF UnifierVar, UnifierEnv))
wffRewriteLhsParser numProd prods re =
    let WffRewriteLhs lhs = wffRewriteLhs re
    in
    case sequenceA $ fmap (strength1 . first (lookupProduction' prods)) lhs of
      Nothing -> Left "Production used in rewrite rule not found."
      Just lhsWithProds -> Right $ runStateT (go lhsWithProds) emptyUnifierEnv
  where
    goJuxt [] = error "wffRewriteLhsParser.parseJuxt []"
    goJuxt [p] = fmap (:[]) (go p)
    goJuxt (p:ps) = do
      x <- go p
      lift $ some parseSpace
      fmap (x:) (goJuxt ps)

    go :: Formula (Production', UnifierVar) -> StateT UnifierEnv Parser (WffF UnifierVar)
    go (Terminal str) = lift (WffTerminal <$> parseKeyword str)
    go Empty = return WffEmpty
    go Space = return WffSpace
    -- go Space = lift (some parseSpace *> return WffSpace)
    go (Juxt xs) = WffJuxt <$> goJuxt xs
    go (FormulaAlts []) = error "wffRewriteLhsParser: Empty FormulaAlts list"
    go (FormulaAlts xs) = foldr1 (<|>) $ map go xs
    go (MetaVar (p@(Production name prodF), unifierVar)) = do
      env <- get
      wff <- lift $ parseWff' numProd prods prodF
      case insertUnifierVar unifierVar wff env of
        Left wff'
          | not (wffEqual wff wff') -> lift $ parseError "Variable in rewrite rule used for things that parse to two different wffs"
          | otherwise -> return ()
        Right env' -> put env'

      return $ WffNamed unifierVar wff

wffRewritePerform :: UnifierEnv -> WffF UnifierVar -> Wff'
wffRewritePerform uenv = go
  where
    go (WffTerminal str) = WffTerminal str
    go (WffJuxt xs) = WffJuxt $ map go xs
    go WffEmpty = WffEmpty
    go WffSpace = WffSpace

    go (WffNamed uvar _wff) =
      case lookupUnifierVar uvar uenv of
        Nothing -> error $ "!!! Internal error: wffRewritePerform: Cannot find UnifierVar " ++ ppr uvar ++ " in environment"
        Just wff' -> wff'

-- TODO: Propagate error messages upwards
wffRewriteToRewrite0 :: Maybe NumProd -> [Production'] -> WffRewrite -> Rewrite String
wffRewriteToRewrite0 numProd prods re = rewriteWithErr "wffRewriteToRewrite" $ \str ->
  case wffRewriteLhsParser numProd prods re of
    Left err -> Nothing
    Right p ->
      case execParser p str of
        Left (errCtx, err) -> Nothing
        Right (uwff, uenv) -> Just $ ppr (wffRewritePerform uenv uwff)

wffRewriteToRewrite :: Maybe NumProd -> [Production'] -> WffRewrite -> Rewrite Wff'
wffRewriteToRewrite numProd prods re = rewriteWithErr "wffRewriteToRewrite" $ \wff -> do
  str <- runRewrite (wffRewriteToRewrite0 numProd prods re) (ppr wff)
  case execParser (parseWff' numProd prods (wffRewriteScheme re)) str of
    Left (errCtx, err) -> Nothing
    Right wff' -> Just wff'


parseWff' :: Maybe NumProd -> [Production'] -> Formula' -> Parser Wff'
parseWff' numProd ps0 f = parseNumProd <|> go f
  where
    parseNumProd =
      case numProd of
        Just np -> parseTheoryNum' np
        Nothing -> parseError "parseWff': no NumProd"

    go' = parseWff' numProd ps0

    parseRuleVar :: Parser String
    parseRuleVar = parseChar '?' >> some (parseAlphaUnderscore <|> parseDigit)

    goJuxt [] = error "parseJuxt []"
    goJuxt [p] = fmap (:[]) (go' p)
    goJuxt (p:ps) = do
      x <- go' p
      some parseSpace
      fmap (x:) (goJuxt ps)

    go :: Formula' -> Parser Wff'
    go (Terminal str) = WffTerminal <$> parseKeyword str
    go Empty = return WffEmpty
    go Space = return WffSpace
    go (Juxt xs) = WffJuxt <$> goJuxt xs
    go (FormulaAlts []) = error "parseWff': Empty FormulaAlts list"
    go (FormulaAlts xs) = foldr1 (<|>) $ map go' xs
    go (MetaVar (FormulaMetaVar p)) =
      case lookupProduction ps0 p of
        Nothing -> parseError ("Cannot find production named " <> p)
        Just rhs -> do
          wff <- go' rhs
          return wff
          -- return (WffWff (Wff p wff))

data WffVar a = WffVarName String | WffVarFilled a deriving (Show, Data, Functor, Traversable, Foldable)

instance Applicative WffVar where
  pure = WffVarFilled
  (<*>) = ap

instance Monad WffVar where
  WffVarName v >>= _ = WffVarName v
  WffVarFilled x >>= f = f x

data WffF a
  = WffTerminal String
  | WffJuxt [WffF a]
  | WffEmpty
  | WffSpace
  | WffNamed a Wff'
  deriving (Show, Data, Eq)

type Wff' = WffF Void


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
          z -> z
      z -> z
flattenWff' (WffJuxt (x:xs)) =
  case flattenWff' (WffJuxt (map flattenWff' xs)) of
    WffJuxt xs' -> WffJuxt (flattenWff' x : xs')
    z -> z
flattenWff' x = x


wffEqual :: Wff' -> Wff' -> Bool
wffEqual x y = go (flattenWff' x) (flattenWff' y)
  where
    go (WffTerminal a) (WffTerminal b) = a == b
    go (WffJuxt a) (WffJuxt b) = and (zipWith go a b)
    go WffEmpty WffEmpty = True
    go WffSpace WffSpace = True
    go _ _ = False

instance Postprocess Wff' where
  postprocess = flattenWff'

wff'EqToRewrite :: Theory' a -> Equality Wff' -> Rewrite Wff'
wff'EqToRewrite th eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
  if x == z
    then Just y
    else Nothing

-- wff'EqToRewrite :: Theory' a -> Equality Wff' -> Rewrite Wff'
-- wff'EqToRewrite th eql@(x :=: y) = rewriteWithErr (ppr eql) $ \z ->
--   case unify x z of
--     Just (_, env) -> Just (substUnifyEnv env y)
--     Nothing -> Nothing
--     -- then Just y
--     -- else Nothing

-- -- -- wff'RewriteWff :: Rewrite Wff' -> Rewrite Wff
-- -- -- wff'RewriteWff re = rewrite $ \w ->
-- -- --   case runRewrite re (wffParsed w) of
-- -- --     Nothing -> Nothing
-- -- --     Just x -> Just $ w { wffParsed = x }

-- -- -- wffEqToRewrite :: Theory' a -> Equality Wff -> Rewrite Wff
-- -- -- wffEqToRewrite th (x :=: y) = wff'RewriteWff (wff'EqToRewrite th (wffParsed x :=: wffParsed y))

-- wffEqToRewrite' :: Theory' a -> Equality Wff -> Rewrite Wff'
-- wffEqToRewrite' th (x :=: y) = wff'EqToRewrite th (wffParsed x :=: wffParsed y)

data Wff =
  Wff
  { wffName :: String
  , wffParsed :: Wff'
  }
  deriving (Show, Data)

-- -- instance Ppr SimpleWff where
-- --   ppr (WffTerminal t) = t
-- --   ppr WffEmpty = "<empty>"
-- --   ppr WffSpace = "<space>"
-- --   ppr (WffRuleVar v) = '?' : v

instance Ppr Wff' where
  ppr (WffJuxt ws) = unwords (map ppr ws)
  ppr (WffTerminal t) = t
  ppr WffEmpty = "<empty>"
  ppr WffSpace = "<space>"
  -- ppr (WffRuleVar v) = '?' : v

-- instance Ppr Wff where
--   ppr (Wff name w) = '<' : name ++ "> ::= " ++ ppr w

data NumProd = NumProd String String String
  deriving (Show)

data Theory' a
  = Theory
      { theoryName :: String
      , theoryProductions :: [Production']
      , theoryRules :: [WffRewrite]
      , theoryNumNotation :: Maybe NumProd
      }
    deriving Show
type Theory = Theory' Wff

-- theoryRewrites :: Theory -> [(String, Rewrite Wff')]
-- theoryRewrites th = map (second (wffEqToRewrite' th)) $ theoryRules th

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


