module Theory.Type where

import           Theory.Formula
import           Parser
import           Ppr
import           Rewrite

import           Control.Applicative
import           Data.List

data Equality a = a :=: a deriving Show

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

data Wff'
  = WffTerminal String
  | WffJuxt [Wff']
  -- | WffAlts [Wff']
  | WffEmpty
  | WffSpace
  | WffWff Wff
  | WffRuleVar String
  deriving (Eq, Show)

data Wff =
  Wff
  { wffName :: String
  , wffParsed :: Wff'
  }
  deriving (Eq, Show)

instance Ppr Wff' where
    ppr (WffTerminal t) = t
    ppr (WffJuxt wffs) = unwords (map ppr wffs)
    -- ppr (FormulaAlts alts) = unwords (intersperse "|" (map ppr alts))
    ppr WffEmpty = "<empty>"
    ppr WffSpace = "<space>"
    ppr (WffWff w) = '<' : wffName w ++ ">"
    ppr (WffRuleVar v) = '?' : v

instance Ppr Wff where
    ppr (Wff name w) = '<' : name ++ "> ::= " ++ ppr w

data Theory' a
  = Theory
      { theoryName :: String
      , theoryProductions :: [Production']
      , theoryRules :: [(String, Equality a)]
      , theoryNumNotation :: Maybe (String, String, String)
      }
    deriving Show

type Theory = Theory' Wff

theoryRewrites :: Theory -> [Rewrite Wff]
theoryRewrites th = map (equalityToRewrite . snd) $ theoryRules th

instance Parseable RuleVar where
  parse = fmap RuleVar ruleVar <|> fmap ProdVar parseMetaVar'
    where
      ruleVar = parseChar '?' >> some (parseAlphaUnderscore <|> parseDigit)

