
module NDProver.Datatypes where

import NDProver.Parser

import Data.Char
import Data.Maybe
import Data.Monoid


-- Datatype for logic formulas.

data Formula = Predicate ElemName
             | Absurdity
             | Not Formula
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
     deriving (Eq, Ord)

newtype ElemName = ElemName String
     deriving (Eq, Ord)

data Sequent = Sequent [Formula] Formula
    deriving (Eq, Ord)

newtype Proof = Proof [Rule]
     deriving Eq

data Rule = Premise Formula
          | Assumption Formula
          | NotE Formula Formula
          | NotI Formula Formula
          | AndE1 Formula Formula
          | AndE2 Formula Formula
          | AndI Formula Formula Formula
          | OrE Formula Formula Proof Proof
          | OrI1 Formula Formula
          | OrI2 Formula Formula
          | ImpliesE Formula Formula Formula
          | ImpliesI Formula Proof
          | Copy Formula
          | AbsurdityE Formula
          | DoubleNegE Formula Formula
     deriving Eq

--------------------------------------------------------------------------------

symbolAbsurdity, symbolImplies, symbolAnd, symbolOr, symbolNot :: String
symbolAbsurdityC, symbolAndC, symbolOrC, symbolNotC :: Char
symbolAbsurdity = "_"
symbolAbsurdityC = '_'
symbolImplies = "->"
symbolAnd = "&"
symbolAndC = '&'
symbolOr = "|"
symbolOrC = '|'
symbolNot = "~"
symbolNotC = '~'

--------------------------------------------------------------------------------

showFormula :: Formula -> String
showFormula (Predicate (ElemName s)) = s
showFormula Absurdity = symbolAbsurdity
showFormula (And p q) = showAnd p +-+ symbolAnd +-+ showAnd q
showFormula (Or p q) =  showOr p +-+ symbolOr +-+ showOr q
showFormula (Implies p q) = showImplies p +-+ symbolImplies +-+ showImplies q
showFormula (Not p) = symbolNot ++ showNot p

showAnd :: Formula -> String
showAnd p@(Or _ _) = parenthesis $ showOr p
showAnd p@(Implies _ _) = showImplies p
showAnd p = showFormula p

showOr :: Formula -> String
showOr p@(And _ _) = parenthesis $ showAnd p
showOr p@(Implies _ _) = showImplies p
showOr p = showFormula p

showImplies :: Formula -> String
showImplies p@(And _ _) = showAnd p
showImplies p@(Or _ _) = showOr p
showImplies p@(Implies _ _) = parenthesis $ showFormula p
showImplies p = showFormula p

showNot :: Formula -> String
showNot p@(And _ _) = parenthesis $ showFormula p
showNot p@(Or _ _) = parenthesis $ showFormula p
showNot p@(Implies _ _) = parenthesis $ showFormula p
showNot p = showFormula p

showSequent :: Sequent -> String
showSequent (Sequent ps c) =
  psStr ++ space ++ "|- " ++ showFormula c
    where psStr = prettyShow ps
          space = if null psStr then "" else " "

prettyShow :: Show a => [a] -> String
prettyShow (x:y:xs) = show x ++ ", " ++ prettyShow (y:xs)
prettyShow (x:[]) = show x
prettyShow [] = ""

instance Show Formula where
    show = showFormula

instance Show ElemName where
    show (ElemName n) = n

instance Show Sequent where
    show = showSequent

--------------------------------------------------------------------------------

readFormula :: String -> Maybe Formula
readFormula s = case readImplies $ filter (not . isSpace) s of
                     Just (p, "") -> Just p
                     _            -> Nothing

readImplies :: Parser Formula
readImplies = chain readOr symbolImplies Implies

readAnd :: Parser Formula
readAnd = chainc readP symbolAndC And

readOr :: Parser Formula
readOr = chainc readAnd symbolOrC Or

readP :: Parser Formula
readP ('(':s) =
   case readImplies s of
     Just (a, ')':s1) -> Just (a, s1)
     _                -> Nothing
readP s@(c : cs)
  | c == symbolAbsurdityC = Just (Absurdity, cs)
  | c == symbolNotC       = case readP cs of
                                 Just (a, s1) -> Just (Not a, s1)
                                 Nothing      -> Nothing
  | otherwise             = Just (Predicate (ElemName prd), rst)
    where prd = takeWhile (`elem` symbols) s
          rst = dropWhile (`elem` symbols) s
readP [] = Nothing

splitOn :: Eq a => [a] -> [a] -> [[a]]
splitOn _ [] = []
splitOn separator string = splitOn' separator string [] []
  where splitOn' (s:ss) (c:cs) a a' =
          if s == c
             then splitOn' ss cs a (c:a')
             else splitOn' separator cs (c : reverse a' ++ a) []
        splitOn' [] cs a a' = reverse a : splitOn' separator cs [] []
        splitOn' ss [] a a' = [reverse (a' ++ a)]

readSequent :: String -> Maybe Sequent
readSequent cs =
  case splitOn "|-" cs of
    [psStr, cStr] -> do ps <- mapM readFormula (splitOn "," psStr)
                        c  <- readFormula cStr
                        return (Sequent ps c)
    _ -> Nothing

instance Read Formula where
    readsPrec _ = maybeToList . readImplies . (filter (not . isSpace))

instance Read Sequent where
  readsPrec _ = undefined

--------------------------------------------------------------------------------

showProof :: Int -> Proof -> String
showProof i (Proof (x:xs)) =
  replicate i ' ' ++ showRule i x ++ "\n" ++ showProof i (Proof xs)
showProof _ (Proof []) = ""

showRule :: Int -> Rule -> String
showRule _ (Premise f) = show f ++ " ::: Premise"
showRule _ (Assumption f) = show f ++ " ::: Assumption"
showRule _ (AndE1 f p) = show f ++ " ::: " ++ symbolAnd ++ "e1 " ++ show p
showRule _ (AndE2 f p) = show f ++ " ::: " ++ symbolAnd ++ "e2 " ++ show p
showRule _ (NotE f p) = show f ++ " ::: " ++ symbolNot ++ "e " ++ show p
showRule _ (NotI f p) = show f ++ " ::: " ++ symbolNot ++ "i " ++ show p
showRule _ (AndI f p q) =
  show f ++ " ::: " ++ symbolAnd ++ "i " ++ show p ++ ", " ++ show q
showRule i (OrE f p prf1 prf2) =
  seperatorOpen ++ showProof (i+2) prf1 ++ spaces ++
  seperatorClose ++ spaces ++
  seperatorOpen ++ showProof (i+2) prf2 ++ spaces ++
  seperatorClose ++ spaces ++ show f ++ " ::: |e " ++ show p
    where spaces = replicate i ' '
showRule _ (OrI1 f p) = show f ++ " ::: " ++ symbolOr ++ "i1 " ++ show p
showRule _ (OrI2 f p) = show f ++ " ::: " ++ symbolOr ++ "i2 " ++ show p
showRule _ (ImpliesE f p q) =
  show f ++ " ::: " ++ symbolImplies ++ "e " ++ show p ++ ", " ++ show q
showRule i (ImpliesI f prf) =
  seperatorOpen ++ showProof (i+2) prf ++ spaces ++
  seperatorClose ++ spaces ++ show f ++ " ::: ->i"
    where spaces = replicate i ' '
showRule _ (Copy f) = show f ++ " ::: Copy " ++ show f
showRule _ (AbsurdityE f) = show f ++ " ::: " ++ symbolAbsurdity ++ "e"
showRule _ (DoubleNegE f p) = show f ++ " ::: ~~e " ++ show p

instance Show Proof where
    show = showProof 0

instance Show Rule where
    show = showRule 0

--------------------------------------------------------------------------------

instance Monoid Proof where
    mempty = Proof []
    mappend (Proof p1) (Proof p2) = Proof (p1 ++ p2)

--------------------------------------------------------------------------------

seperatorOpen :: String
seperatorOpen  = "------OPENING-----------------------------\n"

seperatorClose :: String
seperatorClose = "------CLOSING-----------------------------\n"

(+-+) :: String -> String -> String
a +-+ b = a ++ (' ' : b)

parenthesis :: String -> String
parenthesis s = '(' : (s ++ ")")

symbols :: [Char]
symbols = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']

pNot :: Formula -> Formula
pNot p = Implies p Absurdity

implAnd :: Formula -> Formula -> Formula
implAnd p q = pNot (Implies p (pNot q))

implOr :: Formula -> Formula -> Formula
implOr p q = Implies (pNot p) q

toImpl :: Formula -> Formula
toImpl (And p q) = implAnd (toImpl p) (toImpl q)
toImpl (Or p q) = implOr (toImpl p) (toImpl q)
toImpl (Implies p q) = Implies (toImpl p) (toImpl q)
toImpl p = p
