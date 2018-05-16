module Types.NSubtype
  ( overlap
  , subtype
  , equiv
  , isEmpty
  , flattenProds
  , flattenBDD
  ) where

-- A naive (i.e. inefficient) implementation of subtyping for set
-- theoretic types... and a potentially useful oracle for more
-- efficient implementation experimentation!

import Types.Base
import Types.LazyBDD
import Data.List
import Common.SetOps

-- Is this type equivalent to ∅?
isEmpty :: Ty -> Bool
isEmpty (Ty b ps as) =
  (b == emptyBase)
  && (isEmptyProd ps)
  && (isEmptyArrow as)



-- given a BDD of Prods, return the flattened
-- list representations of the positive
-- and negative components, e.g.:
-- (⋃((S×S) ∩ (⋂ ¬(T×T) ...))) 
flattenProds :: (BDD Prod) -> [(Prod , [Prod])]
flattenProds prods = flattenAux anyTy anyTy [] prods
  where flattenAux :: Ty -> Ty -> [Prod] -> (BDD Prod) -> [(Prod , [Prod])]
        flattenAux t1 t2 negAtoms Top = [((Prod t1 t2) , negAtoms)]
        flattenAux t1 t2 negAtoms Bot = []
        flattenAux t1 t2 negAtoms (Node p@(Prod t3 t4) l m r) =
          ((flattenAux (tyAnd t1 t3) (tyAnd t2 t4) negAtoms l)
           ++ (flattenAux t1 t2 negAtoms m)
           ++ (flattenAux t1 t2 (p:negAtoms) r))


-- Is a BDD of prods equivalent to ∅?
-- For each clause in the DNF of the product type,
-- let the positive info P be (S₁, S₂) and negative info
-- N be (¬(T₁,T₂),...), check that for all N' ⊆ N,
-- (s1 <: (⋃(T₁,T₂) ∈ N' T₁)) or (s2 <: (⋃(T₁,T₂) ∈ N\N' T₂))
-- i.e. that all possible combinations of the negative info
-- would produce an empty type in either the first or second
-- field of the product type.
isEmptyProd :: (BDD Prod) -> Bool
isEmptyProd ps = all emptyClause (flattenProds ps)
  where emptyClause :: (Prod , [Prod]) -> Bool
        emptyClause ((Prod s1 s2) , negs) =
          all (emptyProd s1 s2 negs) (subsets negs)
        emptyProd :: Ty -> Ty -> [Prod] -> [Prod] -> Bool
        emptyProd s1 s2 negs negs'
          | subtype s1 (orFsts negs') = True
          | subtype s2 (orSnds (negs \\ negs')) = True
          | otherwise = False
        orFsts :: [Prod] -> Ty
        orFsts ps = foldl (\t (Prod t1 _) -> tyOr t t1) emptyTy ps
        orSnds :: [Prod] -> Ty
        orSnds ps = foldl (\t (Prod _ t2) -> tyOr t t2) emptyTy ps



-- given a BDD of x, return the flattened
-- list representations of the positive
-- and negative components, e.g.:
-- (⋃(⋂ x ...) ∩ (⋂ ¬x ...))) 
flattenBDD :: (BDD x) -> [([x] , [x])]
flattenBDD as = flattenAux [] [] as
  where flattenAux :: [x] -> [x] -> (BDD x)
          -> [([x] , [x])]
        flattenAux pos neg Bot = []
        flattenAux pos neg Top = [(pos,neg)]
        flattenAux pos neg (Node a l m r) =
          ((flattenAux (a:pos) neg l)
           ++ (flattenAux pos neg m)
           ++ (flattenAux pos (a:neg) r))




-- Is a BDD of arrows equivalent to ∅?
-- For each clause in the DNF of the arrow type,
-- let the positive info be P be (¬(T₁ → T₂),...) and the
-- negative info N be (¬(T₁ → T₂),...), check that for some
-- (T₁ → T₂) ∈ N, T₁ <: ⋃(S₁ ...) and for all non-empty P' ⊆ P
-- (T₁ <: ⋃(S₁→S₂ ∈ P\P') S₁) or (⋂(S₁→S₂ ∈ P') S₂ <: T₂)
isEmptyArrow :: (BDD Arrow) -> Bool
isEmptyArrow as = all emptyClause (flattenBDD as)
  where emptyClause :: ([Arrow] , [Arrow]) -> Bool
        emptyClause (pos,neg) = any (emptyArrow dom pos) neg
          where dom = foldl (\t (Arrow s1 _) -> tyOr t s1) emptyTy pos
        emptyArrow :: Ty -> [Arrow] -> Arrow -> Bool
        emptyArrow dom pos (Arrow t1 t2) =
          (subtype t1 dom) && (all
                               (emptyHelper t1 t2 pos)
                               (nonEmptySubsets pos))
        emptyHelper :: Ty -> Ty -> [Arrow] -> [Arrow] -> Bool
        emptyHelper t1 t2 pos pos' =
          (subtype t1 dom) || (subtype rng t2)
          where dom = (foldl (\t (Arrow s1 _) -> tyOr t s1)
                       emptyTy
                       (pos \\ pos'))
                rng = (foldl (\t (Arrow _ s2) -> tyAnd t s2)
                        anyTy
                        pos')

-- is [[t1]] ∩ [[t2]] ≠ ∅
overlap :: Ty -> Ty -> Bool
overlap t1 t2 = not (isEmpty (tyAnd t1 t2))


-- Is t1 a subtype of t2
-- i.e. [[t1]] ⊆ [[t2]]
subtype :: Ty -> Ty -> Bool
subtype t1 t2 = isEmpty (tyDiff t1 t2)


-- Is t1 equivalent to t2
-- i.e. [[t1]] ⊆ [[t2]] and [[t1]] ⊇ [[t2]]
equiv :: Ty -> Ty -> Bool
equiv t1 t2 = subtype t1 t2 && subtype t2 t1
