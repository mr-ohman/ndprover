
module NDProver.Parser where

type Parser a = String -> Maybe (a, String)

-- Chain parser

chain :: Parser a -> String -> (a -> a -> a) -> Parser a
chain p op f s1 =
   case p s1 of
     Just (a,s2) -> case s2 of
                   s3 | take len s3 == op -> case chain p op f (drop len s3) of
                                       Just (b,s4) -> Just (f a b,s4)
                                       Nothing     -> Just (a, s2)
                   _              -> Just (a,s2)
     Nothing     -> Nothing
   where len = length op

chainc :: Parser a -> Char -> (a -> a -> a) -> Parser a
chainc p op f s1 =
   case p s1 of
     Just (a,s2) -> case s2 of
                   c:s3 | c == op -> case chainc p op f s3 of
                                       Just (b,s4) -> Just (f a b,s4)
                                       Nothing     -> Just (a, s2)
                   _              -> Just (a,s2)
     Nothing     -> Nothing
