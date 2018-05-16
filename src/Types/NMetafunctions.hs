module Types.NMetafunctions
  ( isPred
  , isFun
  , isProd
  , fstProj
  , sndProj
  , domTy
  , rngTy
  ) where

import Types.Base
import Types.LazyBDD
import Types.NSubtype (flattenProds, flattenBDD)
import Types.Subtype
import Data.List
import Common.SetOps

-- Is this a function type?
isFun :: Ty -> Bool
isFun t = subtype t anyArrow

-- Is this a function type?
isProd :: Ty -> Bool
isProd t = subtype t anyProd


-- Calculates the projection type for a given type
-- i.e. given (\(Prod t _) -> t) (prodTy T F)
--      it should produce T, also
--      given (\(Prod _ t) -> t) (prodTy T F)
--      it should produce F.
-- Works on complex types that are <: Any × Any.
-- Equivalent to ⋃i∈I(⋃N'⊆Nᵢ(⋂p∈Pᵢ Sₚ & ⋂n∈N' ¬Sₙ))
-- where the original product type is
-- ⋃i∈I(̱ ⋂p∈Pᵢ (Sₚ , Tₚ)  &  ⋂n∈Nᵢ  ¬(Sₙ , Tₙ) )
calcProj :: (Ty -> Ty -> Ty) -> Ty -> Maybe Ty
calcProj select t@(Ty _ ps _)
  | not (isProd t) = Nothing
  | otherwise = Just (foldl tyOr emptyTy (map clauseProj clauses))
    where clauses :: [(Prod, [Prod])]
          clauses = flattenProds ps
          clauseProj :: (Prod, [Prod]) -> Ty
          clauseProj ((Prod t1 t2), negs) =
            (foldl (\t negs' -> tyOr t (proj t1 t2 negs negs'))
             emptyTy
             (subsets negs))
          proj :: Ty -> Ty -> [Prod] -> [Prod] -> Ty
          proj t1 t2 negs negs'
            | isEmpty t1' = emptyTy
            | isEmpty t2' = emptyTy
            | otherwise   = select t1' t2'
            where t1' = tyAnd t1 (andNFsts negs')
                  t2' = tyAnd t2 (andNSnds (negs \\ negs'))
          andNFsts :: [Prod] -> Ty
          andNFsts ps = foldl (\t (Prod t1 _) -> tyAnd t (tyNot t1)) anyTy ps
          andNSnds :: [Prod] -> Ty
          andNSnds ps = foldl (\t (Prod _ t2) -> tyAnd t (tyNot t2)) anyTy ps

            

-- if t is a product, what type is returned
-- from it's first projection? If it is not
-- a product, return Nothing.
fstProj :: Ty -> Maybe Ty
fstProj t = calcProj (\t1 t2 -> t1) t

-- If t is a product, what type is returned
-- from it's second projection. If it is not
-- a product, return Nothing.
sndProj :: Ty -> Maybe Ty
sndProj t = calcProj (\t1 t2 -> t2) t


-- Is this a function for a predicate?  If so, return `Just t` where
-- `t` is the type it is a predicate for, otherwise return Nothing. A
-- sound... but obviously not complete implementation.
isPred :: Ty -> Maybe Ty
isPred (Ty b
         Bot
         (Node (Arrow t1 res1)
           (Node (Arrow t2 res2) Top Bot Bot)
           Bot
           Top))
  | not (b == emptyBase) = Nothing
  | not (equiv t1 (tyNot t2)) = Nothing
  | (subtype res1 trueTy) && (subtype res2 falseTy) = Just t1
  | (subtype res2 trueTy) && (subtype res1 falseTy) = Just t2
  | otherwise = Nothing
isPred _ = Nothing



-- given a type, if it is a function, return the collective
-- domain for the function type they represent, e.g.:
-- (⋂i∈I(⋃(Sₚ→Tₚ)∈Pᵢ Sₚ))
domTy :: Ty -> Maybe Ty
domTy t
  | not (isFun t) = Nothing
  | otherwise = Just dom
  where (Ty _ _ arrowsBDD) = t
        clauses :: [([Arrow] , [Arrow])]
        clauses = flattenBDD arrowsBDD
        clauseDoms :: [Ty]
        clauseDoms = map clauseDom clauses
        clauseDom :: ([Arrow] , [Arrow]) -> Ty
        clauseDom (pos, neg) = (foldl (\t (Arrow t' _) ->
                                         tyOr t t')
                                emptyTy
                                pos)
        dom = foldl tyAnd anyTy clauseDoms

-- If (1) fty is a function type and (2) argty is a subtype
-- of its domain, what is the return type for applying
-- an fty to an argty? If (1) and (2) are not both
-- satisfied, return Nothing.
rngTy :: Ty -> Ty -> Maybe Ty
rngTy fty@(Ty _ _ arrows) argty =
  case (domTy fty) of
    (Just dom) | (subtype argty dom) -> Just res
    _ -> Nothing
  where pss = map fst (flattenBDD arrows)
        res = foldl (\t ps -> tyOr t (calcRng ps argty)) emptyTy pss


calcRng :: [Arrow] -> Ty -> Ty
calcRng ps argty = foldl tyOr emptyTy ts
  where pss = nonEmptySubsets ps
        ts = map getTy pss
        getTy :: [Arrow] -> Ty
        getTy pos
          | subtype argty compDom = emptyTy
          | otherwise = rng
          where compDom = (foldl (\t (Arrow s1 _) -> tyOr t s1)
                           emptyTy
                           (ps \\ pos))
                rng = (foldl (\t (Arrow _ s2) -> tyAnd t s2)
                           anyTy
                           pos)
          
  
