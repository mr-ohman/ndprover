
module NDProver.Semantics where

import NDProver.Datatypes

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

import Util.Maybe


fuse :: Formula -> [Formula] -> Formula
fuse c [] = c
fuse c ps = Implies (foldr1 And ps) c

eval :: Formula -> Map String Bool -> Bool
eval (Not p) l = not (eval p l)
eval (And p q) l = eval p l && eval q l
eval (Or p q) l = eval p l || eval q l
eval (Implies p q) l = not (eval p l) || eval q l
eval Absurdity _ = False
eval (Predicate (ElemName s)) l = l Map.! s

getPred :: Formula -> Set String
getPred (Not p) = getPred p
getPred (And p q) = getPred p `Set.union` getPred q
getPred (Or p q) = getPred p `Set.union` getPred q
getPred (Implies p q) = getPred p `Set.union` getPred q
getPred (Predicate (ElemName s)) = Set.singleton s
getPred Absurdity = Set.empty

generateValues :: Int -> [[Bool]]
generateValues n = gen base n
    where gen xs n
              | n < 1  = error "generateValues"
              | n == 1 = xs
              | otherwise = gen (concatMap (\x -> map (x:) xs) [True, False]) (n-1)
          base = [[True],[False]]

makeLexicons :: Set String -> [Map String Bool]
makeLexicons s = map (\x -> make (Set.toList s) x Map.empty) (generateValues (Set.size s))
    where make (x:xs) (y:ys) m = make xs ys (Map.insert x y m)
          make [] [] m = m
          make _ _ _ = error "makeLexicons"

(|=) :: [Formula] -> Formula -> (Bool, Maybe (Map String Bool))
(|=) ps c = if Set.null preds then (eval fused Map.empty, Nothing)
                              else ifNotAll (eval fused) (makeLexicons preds)
    where fused = fuse c ps
          preds = getPred fused
