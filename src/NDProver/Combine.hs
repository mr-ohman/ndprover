
module NDProver.Combine where

import NDProver.Datatypes (Formula, Sequent(..), Proof)
import NDProver.Semantics
import NDProver.Rules
import NDProver.Thread

import Data.Map (Map)
import qualified Data.Map as Map


(|=-) :: [Formula] -> Formula -> IO (Maybe (Either (Map String Bool) Proof))
(|=-) ps c = do res <- forkInterest (ps |= c) (ps |- c)
                return (maybeInEither res)

proveFormal :: [Formula] -> Formula -> IO String
proveFormal ps c = do result <- ps |=- c
                      return $ showResult (Sequent ps c) result

showResult :: Sequent -> Maybe (Either (Map String Bool) Proof) -> String
showResult s =
  maybe (showEvalFormal s) $ either (showCounterFormal s) (showProofFormal s)

showEvalFormal :: Sequent -> String
showEvalFormal s = show s ++ " is falsified directly by evaluation."

showCounterFormal :: Sequent -> Map String Bool -> String
showCounterFormal s m =
  show s ++ " has counterexample:\n" ++ showVarList (Map.toList m)

showProofFormal :: Sequent -> Proof -> String
showProofFormal s prf = show s ++ " has proof:\n" ++ show prf

showVarList = concatMap (\(v,b) -> v ++ " = " ++ show b ++ "\n")

maybeInEither :: Either (Maybe a) (Maybe b) -> Maybe (Either a b)
maybeInEither (Left (Just a)) = Just (Left a)
maybeInEither (Right (Just a)) = Just (Right a)
maybeInEither _ = Nothing
