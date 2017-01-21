
module NDProver.Verify (verify) where

import NDProver.Datatypes

import Data.Set (Set)
import qualified Data.Set as Set


verify :: Proof -> Bool
verify (Proof rs) = ver Set.empty rs

ver :: Set Formula -> [Rule] -> Bool
ver ps ((Premise f):rs) = ver (Set.insert f ps) rs
ver ps ((NotI f p):rs) =
  if p `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((NotE f p):rs) =
  if p `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((AndE1 f p):rs) =
  if p `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((AndE2 f p):rs) =
  if p `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((AndI f p q):rs) =
  if p `Set.member` ps && q `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((OrE f p (Proof prf1) (Proof prf2)):rs) =
  if p `Set.member` ps && verA ps prf1 && verA ps prf2
     then ver (Set.insert f ps) rs
     else False
ver ps ((OrI1 f p):rs) =
  if p `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((OrI2 f p):rs) =
  if p `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((ImpliesE f p q):rs) =
  if p `Set.member` ps && q `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((ImpliesI f (Proof prf)):rs) =
  if verA ps prf
     then ver (Set.insert f ps) rs
     else False
ver ps ((Copy f):rs) =
  if f `Set.member` ps
     then ver ps rs
     else False
ver ps ((AbsurdityE f):rs) =
  if Absurdity `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps ((DoubleNegE f p):rs) =
  if p `Set.member` ps
     then ver (Set.insert f ps) rs
     else False
ver ps [] = True
ver _ _ = False

verA :: Set Formula -> [Rule] -> Bool
verA ps ((Assumption f):rs) = ver (Set.insert f ps) rs
verA _ _ = False
