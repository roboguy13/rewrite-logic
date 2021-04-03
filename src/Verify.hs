{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Verify where

import           Rewrite
import           Theorem
import           Theory.Theory
import           Theory.Formula
import           Theory.Type
import           Parser
import           Ppr

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Applicative

import Debug.Trace

newtype Verifier a = Verifier { runVerifier :: ReaderT (Maybe NumProd, [Production']) (State [(String, WffRewrite)]) a }
  deriving (Functor, Applicative, Monad, MonadState [(String, WffRewrite)], MonadReader (Maybe NumProd, [Production']))

execVerifier :: [Theory] -> Verifier a -> a
execVerifier ths = flip evalState (concatMap go ths) . flip runReaderT (foldr (<|>) Nothing $ map theoryNumNotation ths, concatMap theoryProductions ths) . runVerifier
  where
    go :: Theory -> [(String, WffRewrite)]
    go th = map (\re -> (wffRewriteName re, re)) (theoryRules th)
    -- go th = map (\re -> (wffRewriteName re, wffRewriteToRewrite th (theoryNumNotation th) (theoryProductions th) re)) (theoryRules th)

lookupRewrite :: String -> Verifier (Maybe WffRewrite)
lookupRewrite name = do
  assocs <- get
  return $ lookup name assocs

insertRewrite :: String -> WffRewrite -> Verifier ()
insertRewrite name re = do
  assocs <- get
  put ((name, re):assocs)

processRewrite :: WffRewrite -> Verifier (Rewrite Wff')
processRewrite re = do
  (numProd, prods) <- ask

  return $ wffRewriteToRewrite numProd prods re

proofToRewrites :: Proof -> Verifier [ProofStep Wff']
proofToRewrites Qed = return []
-- proofToRewrites (ProofBuiltinRewrite side builtin rest) = do
--   case builtin of
--     CbvStep -> fmap (RewriteStep side cbvStep :) (proofToRewrites rest)
--     FullCbv -> fmap (RewriteStep side fullCbv :) (proofToRewrites rest)

proofToRewrites (ProofRewrite side (BasicRewrite name withClause) rest) = do
  x <- lookupRewrite name
  case x of
    Nothing -> error $ "No such theorem: " <> name
    Just re0 -> do
      re <- processRewrite $ setWithClause re0 withClause
      fmap (RewriteStep name side re:) (proofToRewrites rest)

proofToRewrites (ProofRewrite side (OneTD name withClause) rest) = do
  x <- lookupRewrite name
  case x of
    Nothing -> error $ "No such theorem: " <> name
    Just re0 -> do
      re <- processRewrite $ setWithClause re0 withClause
      fmap (RewriteStep name side (oneTD re):) (proofToRewrites rest)

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
  traceM $ "\ntheorem: " ++ ppr thm
  x <- verifyTheoremDef def
  case x of
    Left err -> return $ Left err
    Right _ ->
      case wff'EqToRewrite name thm of
        Nothing -> return $ Left $ "wff'EqToRewrite failed for theorem " ++ name
        Just re0 ->
          fmap Right $ insertRewrite name re0

verifyDefs :: Theory -> [Def] -> Verifier (Either String ())
verifyDefs th defs = fmap sequence_ $ mapM (verifyAndPushTheoremDef th) defs

fileParser :: Parser ([Theory], [Def])
fileParser = do
  theories <- some (many parseSpace >> parseTheory >>= \th -> some parseNewline >> return th)
  case theories of
    (th:_) -> do
      defs <- parseDefs (firstNumProd theories) (concatMap theoryProductions theories)
      return (theories, defs)

verifyFile :: String -> IO ()
verifyFile fileName = do
  contents <- readFile fileName
  case execParser fileParser contents of
    Left (ctx, err) -> putStrLn $ err <> "\n" <> showErrorLine (lines contents) ctx
    Right (theories@(th:_), defs) -> do
      -- putStrLn $ "theory: " ++ show th
      case execVerifier theories (verifyDefs th defs) of
        Left err -> do
          putStrLn $ "Error: " <> err
        Right () -> putStrLn "Correct."
      -- putStrLn "Theories:"
      -- print theories

