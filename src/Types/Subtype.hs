module Types.Subtype
  ( overlap
  , subtype
  , equiv
  , isEmpty
  ) where


import Types.Base
import Types.LazyBDD

-- Is this type equivalent to ∅?
isEmpty :: Ty -> Bool
isEmpty (Ty b ps as) =
  (b == emptyBase)
  && (isEmptyProd ps anyTy anyTy [])
  && (isEmptyArrow as emptyTy [] [])


-- Is a BDD of prods equivalent to ∅?
isEmptyProd :: (BDD Prod) -> Ty -> Ty -> [Prod] -> Bool
isEmptyProd (Node p@(Prod t1 t2) l m r) s1 s2 neg =
  (isEmptyProd l (tyAnd s1 t1) (tyAnd s2 t2) neg)
  && (isEmptyProd m s1 s2 neg)
  && (isEmptyProd r s1 s2 (p:neg))
isEmptyProd Bot _ _ _ = True
isEmptyProd Top s1 s2 neg =
  ((isEmpty s1)
  || (isEmpty s2)
  || (aux s1 s2 neg))
  where aux :: Ty -> Ty -> [Prod] -> Bool
        aux s1 s2 [] = False
        aux s1 s2 ((Prod t1 t2):neg) = lhsCheck && rhsCheck
          where lhsCheck = ((isEmpty diff1) || (aux diff1 s2 neg))
                diff1 = (tyDiff s1 t1)
                rhsCheck = ((isEmpty diff2) || (aux s1 diff2 neg))
                diff2 = (tyDiff s2 t2)

-- Is a BDD of arrows equivalent to ∅?
isEmptyArrow :: (BDD Arrow) -> Ty -> [Arrow] -> [Arrow] -> Bool
isEmptyArrow (Node a@(Arrow s1 s2) l m r) dom pos neg =
  (isEmptyArrow l (tyOr s1 dom) (a:pos) neg)
  && (isEmptyArrow m dom pos neg)
  && (isEmptyArrow r dom pos (a:neg))
isEmptyArrow Bot _ _ _ = True
isEmptyArrow Top dom pos neg = any (emptyArrow dom pos) neg
  where emptyArrow :: Ty -> [Arrow] -> Arrow -> Bool
        emptyArrow allDom allPos (Arrow t1 t2) =
          (subtype t1 allDom) && aux t1 (tyNot t2) allPos
          where aux :: Ty -> Ty -> [Arrow] -> Bool
                aux t1 nt2 [] = (isEmpty t1) || (isEmpty nt2)
                aux t1 nt2 ((Arrow s1 s2):pos) =
                  (((isEmpty nt2') || (aux t1 nt2' pos))
                   &&
                   ((isEmpty t1') || (aux t1' nt2 pos)))
                  where nt2' = (tyAnd nt2 s2)
                        t1'  = (tyDiff t1 s1)


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
