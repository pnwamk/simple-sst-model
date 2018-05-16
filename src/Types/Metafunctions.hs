module Types.Metafunctions
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
import Types.Subtype

-- Is this a function type?
isFun :: Ty -> Bool
isFun t = subtype t anyArrow

-- Is this a function type?
isProd :: Ty -> Bool
isProd t = subtype t anyProd


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
calcProj select t
  | not (isProd t) = Nothing
  | otherwise = Just (prodProj select prods anyTy anyTy [])
    where (Ty _ prods _) = t

-- Is a BDD of prods equivalent to ∅?
prodProj :: (Ty -> Ty -> Ty) -> (BDD Prod) -> Ty -> Ty -> [Prod] -> Ty
prodProj select bdd s1 s2 neg
  | (isEmpty s1) = emptyTy
  | (isEmpty s2) = emptyTy
  | otherwise =
    case bdd of
      (Node p@(Prod t1 t2) l m r) ->
        (tyOr
         (prodProj select l (tyAnd s1 t1) (tyAnd s2 t2) neg)
         (tyOr
          (prodProj select m s1 s2 neg)
          (prodProj select r s1 s2 (p:neg))))
      Bot -> emptyTy
      Top -> aux select s1 s2 neg
  where aux :: (Ty -> Ty -> Ty) -> Ty -> Ty -> [Prod] -> Ty
        aux select s1 s2 neg
          | (isEmpty s1) = emptyTy
          | (isEmpty s2) = emptyTy
          | otherwise =
            case neg of
              [] -> select s1 s2
              (Prod t1 t2):neg' -> tyOr res1 res2
                where s1'  = tyDiff s1 t1
                      s2'  = tyDiff s2 t2
                      res1 = (aux select s1' s2  neg')
                      res2 = (aux select s1  s2' neg')


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




-- given a type, if it is a function, return the collective
-- domain for the function type they represent, e.g.:
-- (⋂i∈I(⋃(Sₚ→Tₚ)∈Pᵢ Sₚ))
domTy :: Ty -> Maybe Ty
domTy t
  | not (isFun t) = Nothing
  | otherwise = let (Ty _ _ arrows) = t in
      Just (aux anyTy emptyTy arrows)
      where aux ::  Ty -> Ty -> (BDD Arrow) -> Ty
            aux acc dom Top = tyAnd acc dom
            aux acc dom Bot = acc
            aux acc dom (Node (Arrow t _) l m r) = acc3
              where acc1 = aux acc (tyOr dom t) l
                    acc2 = aux acc1 dom m
                    acc3 = aux acc2 dom r


-- If (1) fty is a function type and (2) argty is a subtype
-- of its domain, what is the return type for applying
-- an fty to an argty? If (1) and (2) are not both
-- satisfied, return Nothing.
rngTy :: Ty -> Ty -> Maybe Ty
rngTy fty@(Ty _ _ arrows) argty =
  case (domTy fty) of
    (Just dom) | (subtype argty dom) -> Just res
    _ -> Nothing
  where res = aux arrows argty anyTy
        aux :: (BDD Arrow) -> Ty -> Ty -> Ty
        aux Bot arg rng = emptyTy
        aux Top arg rng
          | (isEmpty arg) = emptyTy
          | otherwise = rng
        aux (Node (Arrow s1 s2) l m r) arg rng
          | isEmpty arg = emptyTy
          | otherwise = tyOr lty1 $ tyOr lty2 $ tyOr mty rty
          where lty1 = aux l arg (tyAnd rng s2)
                lty2 = aux l (tyDiff arg s1) rng
                mty = aux m arg rng
                rty = aux r arg rng
