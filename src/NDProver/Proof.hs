
module NDProver.Proof where

import NDProver.Datatypes

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid


getResult :: Rule -> Formula
getResult (Premise p) = p
getResult (Assumption p) = p
getResult (NotE p _) = p
getResult (NotI p _) = p
getResult (AndE1 p _) = p
getResult (AndE2 p _) = p
getResult (AndI p _ _) = p
getResult (OrE p _ _ _) = p
getResult (OrI1 p _) = p
getResult (OrI2 p _) = p
getResult (ImpliesE p _ _) = p
getResult (ImpliesI p _) = p
getResult (Copy p) = p
getResult (AbsurdityE p) = p
getResult (DoubleNegE p _) = p

getUsed :: Rule -> Set Formula
getUsed (Premise _) = Set.empty
getUsed (Assumption _) = Set.empty
getUsed (NotE _ p) = Set.singleton p
getUsed (NotI _ p) = Set.singleton p
getUsed (AndE1 _ p) = Set.singleton p
getUsed (AndE2 _ p) = Set.singleton p
getUsed (AndI _ p q) = q `Set.insert` Set.singleton p
getUsed (OrE _ p prf1 prf2) =
  p `Set.insert` (getUsedProof prf1 `Set.union` getUsedProof prf2)
getUsed (OrI1 _ p) = Set.singleton p
getUsed (OrI2 _ p) = Set.singleton p
getUsed (ImpliesE _ p q) = q `Set.insert` Set.singleton p
getUsed (ImpliesI _ prf) = getUsedProof prf
getUsed (Copy p) = Set.singleton p
getUsed (AbsurdityE _) = Set.singleton Absurdity
getUsed (DoubleNegE _ p) = Set.singleton p

getUsedProof :: Proof -> Set Formula
getUsedProof (Proof xs) = Set.unions $ map getUsed xs

removeUnused :: Proof -> Proof
removeUnused (Proof ps) = rm ps
  where rm ((ImpliesI p prf):xs) =
          if p `Set.member` used
             then Proof [ImpliesI p (removeUnused prf)] `mappend` rm xs
             else rm xs
        rm ((OrE p q prf1 prf2):xs) =
          if p `Set.member` used
             then Proof [OrE p q (removeUnused prf1) (removeUnused prf2)]
                    `mappend` rm xs
             else rm xs
        rm (x@(Assumption _):xs) = Proof [x] `mappend` rm xs
        rm (x@(Premise _):xs) = Proof [x] `mappend` rm xs
        rm (x:xs) =
          if getResult x `Set.member` used
             then Proof [x] `mappend` rm xs
             else rm xs
        rm [] = Proof []
        used = getResult (last ps) `Set.insert` (Set.unions $ map getUsed ps)

removeDuplicate :: Proof -> Proof
removeDuplicate (Proof prfs) = rm Set.empty prfs
    where rm ps [x, Copy p] = rm ps [x] `mappend`
             if getResult x == p
                then Proof []
                else Proof [Copy p]
          rm ps ((ImpliesI p (Proof prf)):xs) =
             if p `Set.member` ps
                then rm ps xs
                else Proof [ImpliesI p (rm ps prf)]
                       `mappend` rm (p `Set.insert` ps) xs
          rm ps ((OrE p q (Proof prf1) (Proof prf2)):xs) =
            if p `Set.member` ps
               then rm ps xs
               else Proof [OrE p q (rm ps prf1) (rm ps prf2)]
                      `mappend` rm (p `Set.insert` ps) xs
          rm ps (x@(Assumption p):xs) = Proof [x] `mappend` rm (p `Set.insert` ps) xs
          rm ps (x:xs) =
            if getResult x `Set.member` ps
               then rm ps xs
               else Proof [x] `mappend` rm (getResult x `Set.insert` ps) xs
          rm _ [] = Proof []

cleanProof :: Proof -> Proof
cleanProof = removeDuplicate . removeUnused . removeDuplicate
