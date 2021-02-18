{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Verify where

import           Rewrite
import           Theorem
import           Parser

import           Control.Monad.State

type ProofRewrite = Either GoalRewrite (GoalSide, Rewrite Arith)
-- type ProofRewrite = Rewrite Arith

newtype Verifier a = Verifier { runVerifier :: State [(String, Rewrite Arith)] a }
  deriving (Functor, Applicative, Monad, MonadState [(String, Rewrite Arith)])

execVerifier :: Verifier a -> a
execVerifier = flip evalState [] . runVerifier

lookupRewrite :: String -> Verifier (Maybe (Rewrite Arith))
lookupRewrite name = do
  assocs <- get
  return $ lookup name assocs

insertRewrite :: String -> Rewrite Arith -> Verifier ()
insertRewrite name re = do
  assocs <- get
  put ((name, re):assocs)

proofToRewrites :: Proof -> Verifier [ProofRewrite]
proofToRewrites Qed = return []
proofToRewrites (ProofBuiltinRewrite side builtin rest) = do
  case builtin of
    CbvStep -> fmap (Right (side, cbvStep) :) (proofToRewrites rest)
    FullCbv -> fmap (Right (side, fullCbv) :) (proofToRewrites rest)

proofToRewrites (ProofRewrite side (BasicRewrite name) rest) = do
  x <- lookupRewrite name
  case x of
    Nothing -> error $ "No such theorem: " <> name
    Just re -> fmap (Right (side, re):) (proofToRewrites rest)

proofToRewrites (ProofRewrite side (OneTD name) rest) = do
  x <- lookupRewrite name
  case x of
    Nothing -> error $ "No such theorem: " <> name
    Just re -> fmap (Right (side, oneTD re):) (proofToRewrites rest)

proofToRewrites (ProofGoalRewrite re rest) =
  fmap (Left re:) (proofToRewrites rest)

verifyTheoremDef :: Def -> Verifier (Either String [ProofRewrite])
verifyTheoremDef (TheoremDef name thm proof) = do
  res <- proofToRewrites proof
  case checkEqPrf thm res of
    Left err -> return $ Left ("In theorem " <> name <> ":\n" <> err)
    Right _ -> return (Right res)

verifyAndPushTheoremDef :: Def -> Verifier (Either String ())
verifyAndPushTheoremDef def@(TheoremDef name thm _) = do
  x <- verifyTheoremDef def
  case x of
    Left err -> return $ Left err
    Right _ -> fmap Right $ insertRewrite name (equalityToRewrite thm)

verifyDefs :: [Def] -> Verifier (Either String ())
verifyDefs defs = fmap sequence_ $ mapM verifyAndPushTheoremDef defs

verifyFile :: String -> IO ()
verifyFile fileName = do
  contents <- readFile fileName
  case execParser parseDefs contents of
    Left err -> putStrLn err
    Right defs -> do
      case execVerifier (verifyDefs defs) of
        Left err -> putStrLn $ "Error: " <> err
        Right () -> putStrLn "Correct."

