module Common.SetOps
  ( subsets
  , strictSubsets
  , nonEmptySubsets
  ) where

import Data.List

-- powerset of a list
subsets :: (Eq x) => [x] -> [[x]]
subsets [] = [[]]
subsets (x:xs) = (map (\ys -> x:ys) xss) ++ xss 
  where xss = (subsets xs)

-- powerset of a list minus original list
-- (i.e. all the strict subsets)
strictSubsets :: (Eq x) => [x] -> [[x]]
strictSubsets xs = delete xs (subsets xs)

-- powerset of a list minus the empty list
-- (i.e. all the strict subsets)
nonEmptySubsets :: (Eq x) => [x] -> [[x]]
nonEmptySubsets xs = delete [] (subsets xs)
