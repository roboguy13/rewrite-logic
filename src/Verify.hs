{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Verify where

import           Rewrite
import           Theorem
import           Theory.Theory
import           Theory.Type
import           Parser
import           Ppr

import           Control.Monad.State
import           Control.Applicative

import Debug.Trace

newtype Verifier a = Verifier { runVerifier :: State [(String, Rewrite Wff')] a }
  deriving (Functor, Applicative, Monad, MonadState [(String, Rewrite Wff')])

execVerifier :: [Theory] -> Verifier a -> a
execVerifier ths = flip evalState (concatMap go ths) . runVerifier
  where
    go :: Theory -> [(String, Rewrite Wff')]
    go th = map (\re -> (wffRewriteName re, wffRewriteToRewrite (theoryNumNotation th) (theoryProductions th) re)) (theoryRules th)

lookupRewrite :: String -> Verifier (Maybe (Rewrite Wff'))
lookupRewrite name = do
  assocs <- get
  return $ lookup name assocs

insertRewrite :: String -> Rewrite Wff' -> Verifier ()
insertRewrite name re = do
  assocs <- get
  put ((name, re):assocs)

proofToRewrites :: Proof -> Verifier [ProofStep Wff']
proofToRewrites Qed = return []
-- proofToRewrites (ProofBuiltinRewrite side builtin rest) = do
--   case builtin of
--     CbvStep -> fmap (RewriteStep side cbvStep :) (proofToRewrites rest)
--     FullCbv -> fmap (RewriteStep side fullCbv :) (proofToRewrites rest)

proofToRewrites (ProofRewrite side (BasicRewrite name) rest) = do
  x <- lookupRewrite name
  case x of
    Nothing -> error $ "No such theorem: " <> name
    Just re -> fmap (RewriteStep side re:) (proofToRewrites rest)

proofToRewrites (ProofRewrite side (OneTD name) rest) = do
  x <- lookupRewrite name
  case x of
    Nothing -> error $ "No such theorem: " <> name
    Just re -> fmap (RewriteStep side (oneTD re):) (proofToRewrites rest)

proofToRewrites (ProofEqRewrite re rest) =
  fmap (EqStep re:) (proofToRewrites rest)

verifyTheoremDef :: Def -> Verifier (Either String [ProofStep Wff'])
verifyTheoremDef (TheoremDef name thm proof) = do
  res <- proofToRewrites proof
  case checkEqProof thm res of
    Left err -> return $ Left ("In theorem " <> name <> ":\n" <> err)
    Right _ -> return (Right res)

verifyAndPushTheoremDef :: Theory -> Def -> Verifier (Either String ())
verifyAndPushTheoremDef th def@(TheoremDef name thm _) = do
  traceM $ "theorem: " ++ ppr thm
  x <- verifyTheoremDef def
  case x of
    Left err -> return $ Left err
    Right _ -> do
      fmap Right $ insertRewrite name (wff'EqToRewrite th thm)

verifyDefs :: Theory -> [Def] -> Verifier (Either String ())
verifyDefs th defs = fmap sequence_ $ mapM (verifyAndPushTheoremDef th) defs

fileParser :: Parser ([Theory], [Def])
fileParser = do
  theories <- some (many parseSpace >> parseTheory >>= \th -> some parseNewline >> return th)
  case theories of
    (th:_) -> do
      case firstNumProd theories of
        Nothing -> error "No numeral notation"
        Just numProd -> do
          defs <- parseDefs th numProd
          return (theories, defs)

verifyFile :: String -> IO ()
verifyFile fileName = do
  contents <- readFile fileName
  case execParser fileParser contents of
    Left (ctx, err) -> putStrLn $ err <> "\n" <> showErrorLine (lines contents) ctx
    Right (theories@(th:_), defs) -> do
      case execVerifier theories (verifyDefs th defs) of
        Left err -> do
          putStrLn $ "Error: " <> err
        Right () -> putStrLn "Correct."
      -- putStrLn "Theories:"
      -- print theories

