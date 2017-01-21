
module Util.Maybe where

ifNotAll :: (a -> Bool) -> [a] -> (Bool, Maybe a)
ifNotAll f (x:xs) = if f x then ifNotAll f xs else (False, Just x)
ifNotAll _ [] = (True, Nothing)
