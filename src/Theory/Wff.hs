{-# OPTIONS_GHC -Wall -Wno-unused-do-bind #-}

module Theory.Wff where

import           Parser

import           Theory.Formula
import           Theory.Type

import           Control.Applicative

parseWff' :: Maybe NumProd -> [Production'] -> Formula' -> Parser Wff'
parseWff' numProd ps0 f = parseNumProd <|> fmap WffRuleVar parseRuleVar <|> go f
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

-- | XXX: Requires a non-empty theory
parseWff :: Maybe NumProd -> [Production'] -> Parser Wff
parseWff numProd ps = foldr1 (<|>) $ map go ps
  where
    go (Production name p) = Wff <$> pure name <*> parseWff' numProd ps p

parseTheoryWff :: Theory -> Maybe NumProd -> Parser Wff
parseTheoryWff th numProd = parseWff numProd (theoryProductions th)

