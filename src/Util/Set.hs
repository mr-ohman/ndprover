
module Util.Set where

import Data.Set (Set)
import qualified Data.Set as Set

multiInsert :: (Ord a) => [a] -> Set a -> Set a
multiInsert (x:xs) set = multiInsert xs (x `Set.insert` set)
multiInsert [] set = set
