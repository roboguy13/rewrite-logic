{-# OPTIONS_GHC -Wall -Wno-unused-do-bind #-}

module Theory.Wff where

import           Parser

import           Theory.Formula
import           Theory.Type

import           Control.Applicative

-- | XXX: Requires a non-empty theory
parseWff :: Maybe NumProd -> [Production'] -> Parser Wff
parseWff numProd ps = foldr1 (<|>) $ map go ps
  where
    go (Production name p) = Wff <$> pure name <*> parseWff' numProd ps p

parseTheoryWff :: Theory -> Maybe NumProd -> Parser Wff
parseTheoryWff th numProd = parseWff numProd (theoryProductions th)

