module Types.Base
  ( BaseTy(..)
  , Base(..)
  , emptyBase
  , anyBase
  , baseOr
  , baseAnd
  , baseDiff
  , baseNot
  ) where

import Data.Set

data BaseTy = T | F | Z
  deriving (Eq, Show, Ord)

data Base = Base Bool (Set BaseTy)
  deriving (Eq, Show, Ord)

emptyBase = Base True empty
anyBase   = Base False empty


baseOr :: Base -> Base -> Base
baseOr (Base True pos1)  (Base True pos2)
  = Base True (union pos1 pos2)
baseOr (Base True pos)  (Base False neg)
  = Base False (neg \\ pos)
baseOr (Base False neg) (Base True pos)
  = Base False (neg \\ pos)
baseOr (Base False neg1) (Base False neg2)
  = Base False (intersection neg1 neg2)

baseAnd :: Base -> Base -> Base
baseAnd (Base True pos1)  (Base True pos2)
  = Base True (intersection pos1 pos2)
baseAnd (Base True pos)  (Base False neg)
  = Base True (pos \\ neg)
baseAnd (Base False neg) (Base True pos)
  = Base True (pos \\ neg)
baseAnd (Base False neg1) (Base False neg2)
  = Base False (union neg1 neg2)


baseDiff :: Base -> Base -> Base
baseDiff (Base True pos1)  (Base True pos2)
  = Base True (pos1 \\ pos2)
baseDiff (Base True pos)  (Base False neg)
  = Base True (intersection pos neg)
baseDiff (Base False neg) (Base True pos)
  = Base False (union pos neg)
baseDiff (Base False neg1) (Base False neg2)
  = Base True (neg2 \\ neg1)

baseNot :: Base -> Base
baseNot (Base sign bs) = Base (not sign) bs
