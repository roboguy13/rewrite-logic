{-# OPTIONS_GHC -Wall -Wno-unused-do-bind #-}

module Theory.Wff where

import           Parser

import           Theory.Formula
import           Theory.Type

import           Control.Applicative

parseWff' :: [Production'] -> Formula' -> Parser Wff'
parseWff' ps0 f = fmap WffRuleVar parseRuleVar <|> go f
  where
    go' = parseWff' ps0

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
          return (WffWff (Wff p wff))

-- | XXX: Requires a non-empty theory
parseWff :: [Production'] -> Parser Wff
parseWff ps = foldr1 (<|>) $ map go ps
  where
    go (Production name p) = Wff <$> pure name <*> parseWff' ps p

