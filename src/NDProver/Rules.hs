{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module NDProver.Rules where

import NDProver.Datatypes
import NDProver.Proof

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Maybe (isJust, maybeToList)
import Data.Monoid

import Control.Monad.Identity
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Maybe

import Util.Set


newtype ProofT m t p a =
  ProofT { runProofT :: StateT (Map (t, Set t) (Maybe p)) m a }
  deriving (Functor, Applicative, Monad)

type ProofMonad = ProofT Identity Formula Proof

type ProofPair = (Formula, Proof)


andI :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
andI pq@(And p q) ps = runMaybeT $
  do prf1 <- MaybeT $ quickProve p ps
     prf2 <- MaybeT $ quickProve q ps
     return $ prf1 `mappend` prf2 `mappend` Proof [AndI pq p q]
andI _ _ = return Nothing

orE :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
orE p ps = anyProof toProve (getOr (Set.toList ps))
    where getOr (p'@(Or _ _):ps') = p' : getOr ps'
          getOr (_:ps') = getOr ps'
          getOr [] = []
          toProve r@(Or p' q') = runMaybeT $
            do prf1 <- MaybeT $ if p' `Set.member` ps
                                   then quickProve p (Set.delete r ps)
                                   else prove p (Set.insert p' (Set.delete r ps))
               prf2 <- MaybeT $ if q' `Set.member` ps
                                   then quickProve p (Set.delete r ps)
                                   else prove p (Set.insert q' (Set.delete r ps))
               return $ Proof [OrE p r (Proof [Assumption p'] `mappend` prf1)
                                       (Proof [Assumption q'] `mappend` prf2)]

orI :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
orI pq@(Or p q) ps =
  do maybePrf1 <- quickProve p ps
     case maybePrf1 of
       Just prf1 -> return . Just $ prf1 `mappend` Proof [OrI1 pq p]
       Nothing   -> runMaybeT $ do prf2 <- MaybeT $ quickProve q ps
                                   return $ prf2 `mappend` Proof [OrI2 pq q]
orI _ _ = return Nothing

-- Proof (p -> q, ImpliesI {inner proof})
impliesI :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
impliesI pq@(Implies p q) ps = runMaybeT $
    do prf <- MaybeT $ if p `Set.member` ps
                          then quickProve q ps
                          else prove q (Set.insert p ps)
       return $ Proof [ImpliesI pq (Proof [Assumption p] `mappend` prf)]
impliesI _ _ = return Nothing

notI :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
notI np@(Not p) ps = runMaybeT $
    do let ipa = Implies p Absurdity
       prf <- MaybeT $ quickProve ipa ps
       return $ prf `mappend` Proof [NotI np ipa]
notI _ _ = return Nothing

-- Proof (p, Copy p)
copy :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
copy p ps =
  if p `Set.member` ps
     then return . Just $ Proof [Copy p]
     else return Nothing

-- Proof (p, AbsurdityE _|_)
absurdityE :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
absurdityE p ps =
  if Absurdity `Set.member` ps
     then return . Just $ Proof [AbsurdityE p]
     else return Nothing

-- Proof (p, DoubleNegE (p -> _|_) -> _|_)
doubleNegE :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
doubleNegE Absurdity _ = return Nothing
doubleNegE (Implies (Implies _ Absurdity) Absurdity) _ = return Nothing
doubleNegE p ps = runMaybeT $
  do prf <- MaybeT $ quickProve doubleNp ps
     return $ prf `mappend` Proof [DoubleNegE p doubleNp]
    where doubleNp = Implies (Implies p Absurdity) Absurdity

elimination :: Formula -> Set Formula -> ProofMonad [ProofPair]
elimination pq@(And p q) ps =
  return [(p, Proof [AndE1 p pq]), (q, Proof [AndE2 q pq])]
elimination nnp@(Implies (Implies p Absurdity) Absurdity) ps =
  return [(p, Proof [DoubleNegE p nnp])]
elimination pq@(Implies p q) ps =
  if p `Set.member` ps
     then return [(q, Proof [ImpliesE q p pq])]
     else return []
elimination np@(Not p) ps =
  do let ipa = Implies p Absurdity
     return [(ipa, Proof [NotE ipa np])]
elimination p ps = return []

deepElimination :: Formula -> Set Formula -> ProofMonad [ProofPair]
deepElimination pq@(Implies p q) ps = fmap maybeToList $ runMaybeT $
  if q `Set.member` ps
     then fail ""
     else do prf <- MaybeT $ quickProve p ps
             return (q, prf `mappend` Proof [ImpliesE q p pq])
deepElimination p ps = elimination p ps

proofRules :: [Formula -> Set Formula -> ProofMonad (Maybe Proof)]
proofRules = [copy, absurdityE, andI, orI, notI, impliesI, doubleNegE, orE]

-- Preforms elimination, introduction and deep elimination
prove :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
prove c ps =
  do (nps, prf1) <- multiElim elimination ps
     maybePrf2 <- quickProve c nps
     case maybePrf2 of
       Just prf2 -> return . Just $ prf1 `mappend` prf2
       Nothing -> do (nnps, prf3) <- multiElim deepElimination nps
                     maybePrf4 <- anyProof (\f -> f c nnps) proofRules
                     let fprf = case maybePrf4 of
                                  Just prf4 -> Just $ prf1 `mappend` prf3 `mappend` prf4
                                  Nothing   -> Nothing
                     nspps <- ProofT $ get
                     ProofT $ put (Map.insert (c, nps) fprf nspps)
                     return fprf

-- Preforms introduction, skipping elimination
quickProve :: Formula -> Set Formula -> ProofMonad (Maybe Proof)
quickProve c ps =
    do spps <- ProofT $ get
       if ((c, ps) `Map.member` spps)
           then return (spps Map.! (c, ps))
           else do ProofT $ put (Map.insert (c, ps) Nothing spps)
                   maybePrf <- anyProof (\f -> f c ps) proofRules
                   nspps <- ProofT $ get
                   ProofT $ put (Map.insert (c, ps) maybePrf nspps)
                   return maybePrf

(|-) :: [Formula] -> Formula -> (Bool, Maybe Proof)
(|-) ps c = let maybePrf = evalState (runProofT $ prove c (Set.fromList ps)) Map.empty
            in  case maybePrf of
                  Just prf -> (True , (Just . cleanProof)
                            $ mconcat (map (\p -> Proof [Premise p]) ps) `mappend` prf)
                  Nothing  -> (False, Nothing)

anyProof :: Monad m => (a -> m (Maybe Proof)) -> [a] -> m (Maybe Proof)
anyProof f (x:xs) = do maybePrf <- f x
                       case maybePrf of
                         Just prf -> return (Just prf)
                         Nothing  -> anyProof f xs
anyProof f [] = return Nothing

multiElim :: Monad m => (Formula -> Set Formula -> m [ProofPair])
          -> Set Formula -> m (Set Formula, Proof)
multiElim e ps = elim ps Set.empty [Proof []]
    where elim ps prev prfs = if Set.size ps > Set.size prev
                                 then do (nps, prf) <- new ps
                                         elim nps ps (prfs `mappend` prf)
                                 else return (ps, mconcat prfs)
          new ps = do pack <- mapM (\p -> e p ps) (Set.toList ps)
                      let (nps, prfs) = (unzip . concat) $ pack
                      return (multiInsert nps ps, prfs)
