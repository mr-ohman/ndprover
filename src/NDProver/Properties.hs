
module NDProver.Properties where

import NDProver.Datatypes
import NDProver.Rules
import NDProver.Semantics
import NDProver.Verify

import Data.Maybe

import Test.QuickCheck


simplify :: Formula -> Formula
simplify (Not p) = Not (simplify p)
simplify (And (And p q) r) = simplify (And p (And q r))
simplify (And p q) = And (simplify p) (simplify q)
simplify (Or (Or p q) r) = simplify (Or p (Or q r))
simplify (Or p q) = Or (simplify p) (simplify q)
simplify (Implies p q) = Implies (simplify p) (simplify q)
simplify p = p

makeElemName :: Int -> ElemName
makeElemName 0 = ElemName "a"
makeElemName n = ElemName (makeStr n)
  where makeStr n
          | n < 0     = []
          | otherwise = makeStr (n `div` lenSym - 1) ++ [symbols !! (n `mod` lenSym)]
        lenSym = length symbols

allMakeElemName = map makeElemName [0..]

arbElemName :: Int -> Gen ElemName
arbElemName n = oneof (take (n+1) (map return allMakeElemName))

arbPropFormula :: Int -> Gen Formula
arbPropFormula n = arbPropFrm False n' n'
    where n' = n `div` 5

arbPropFrm :: Bool -> Int -> Int -> Gen Formula
arbPropFrm a m n =
    frequency [ (4, if a then oneof [ do en <- arbElemName (m `div` 10 + 1)
                                         return (Predicate en)
                                    , return Absurdity
                                    ]
                         else do en <- arbElemName (m `div` 10 + 1)
                                 return (Predicate en))
              , (n, do f <- arbPropFrm False m (n `div` 2)
                       return (Not f))
              , (n, do f1 <- arbPropFrm False m reduce
                       f2 <- arbPropFrm False m reduce
                       return (And f1 f2))
              , (n, do f1 <- arbPropFrm False m reduce
                       f2 <- arbPropFrm False m reduce
                       return (Or f1 f2))
              , (n, do f1 <- arbPropFrm False m reduce
                       f2 <- arbPropFrm True m reduce
                       return (Implies f1 f2))

              ]
    where reduce = n `div` 4

instance Arbitrary Formula where
    arbitrary = sized arbPropFormula

prop_ShowReadFormula :: Formula -> Bool
prop_ShowReadFormula f = readFormula (showFormula f) == Just (simplify f)

prop_RulesSemantics :: Formula -> Bool
prop_RulesSemantics f = fst ([] |- f) == fst ([] |= f)

prop_RulesVerify :: Formula -> Property
prop_RulesVerify f = let prf = [] |- f
                     in fst prf ==> (verify . fromJust . snd) prf
