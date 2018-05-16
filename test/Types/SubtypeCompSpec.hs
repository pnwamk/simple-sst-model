module Types.SubtypeCompSpec (spec) where

import Test.Hspec
import Test.QuickCheck (property)
import qualified Types.Subtype as S
import qualified Types.NSubtype as N
import qualified Types.LazyBDD as BDD
import Types.Syntax


compIsEmpty :: Ty -> Bool
compIsEmpty rawt = resultN == resultS
  where t = BDD.parseTy rawt
        resultN = N.isEmpty t
        resultS = S.isEmpty t

compBinRel ::
  (BDD.Ty -> BDD.Ty -> Bool)
  -> (BDD.Ty -> BDD.Ty -> Bool)
  -> Ty
  -> Ty
  -> Bool
compBinRel binopN binopS rawt1 rawt2 = resultN == resultS
  where t1 = BDD.parseTy rawt1
        t2 = BDD.parseTy rawt2
        resultN = binopN t1 t2
        resultS = binopS t1 t2


compSubtype :: Ty -> Ty -> Bool
compSubtype = compBinRel N.subtype S.subtype

compEquiv :: Ty -> Ty -> Bool
compEquiv = compBinRel N.equiv S.equiv

compOverlap :: Ty -> Ty -> Bool
compOverlap = compBinRel N.equiv S.equiv


-- Note: a lot of these tests are checking the same
-- overall capability (i.e. is a type empty?) but
-- we thump on that question a few different ways by
-- asking it with each of these functions, and if any
-- subtle differences sneak in w.r.t how we implement
-- these checks hopefully we make sure to catch it
-- with all these (possibly redundant) checks.
spec :: Spec
spec = do
    describe "General Naive vs Efficient Subtype Comparisons" $ do
      it "Equivalent w.r.t. Emptiness" $ property $
        \t -> compIsEmpty t
      it "Equivalent w.r.t. Subtyping" $ property $
        \t1 t2 -> compSubtype t1 t2
      it "Equivalent w.r.t. Equiv" $ property $
        \t1 t2 -> compEquiv t1 t2
      it "Equivalent w.r.t. Overlap" $ property $
        \t1 t2 -> compOverlap t1 t2


    describe "Product Naive vs Efficient Subtype Comparisons" $ do
      it "Product Emptiness" $ property $
        \t1 t2 -> compIsEmpty (Prod t1 t2)
      it "Union of Products Emptiness" $ property $
        \t1 t2 t3 t4 -> compIsEmpty (Or [(Prod t1 t2), (Prod t3 t4)])
      it "Intersection of Products Emptiness" $ property $
        \t1 t2 t3 t4 -> compIsEmpty (And [(Prod t1 t2), (Prod t3 t4)])
      it "Union of Intersection of Products Emptiness" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          compIsEmpty (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
                           (And [(Prod t5 t6), (Prod t7 t8)])])
      it "Intersection of Union of Products Emptiness" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          compIsEmpty (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
                            (Or [(Prod t5 t6), (Prod t7 t8)])])

      it "Product Subtyping" $ property $
        \t1 t2 t3 t4 -> compSubtype (Prod t1 t2) (Prod t3 t4)
      it "Union of Products Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (Or [(Prod t1 t2), (Prod t3 t4)])
           (Prod t5 t6))
      it "Union of Products Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (Prod t5 t6)
           (Or [(Prod t1 t2), (Prod t3 t4)]))
      it "Intersection of Products Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (And [(Prod t1 t2), (Prod t3 t4)])
           (Prod t5 t6))
      it "Intersection of Products Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (Prod t5 t6)
           (And [(Prod t1 t2), (Prod t3 t4)]))
      it "Union of Intersection of Products Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
                (And [(Prod t5 t6), (Prod t7 t8)])])
          (Prod t9 t10))
      it "Union of Intersection of Products Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (Prod t9 t10)
           (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
                (And [(Prod t5 t6), (Prod t7 t8)])]))
      it "Union of Intersection of Products Subtyping 3" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 ->
          (compSubtype
           (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
                (And [(Prod t5 t6), (Prod t7 t8)])])
           (Or [(And [(Prod t9 t10), (Prod t11 t12)]),
                (And [(Prod t13 t14), (Prod t15 t16)])]))
      it "Intersection of Union of Products Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
                 (Or [(Prod t5 t6), (Prod t7 t8)])])
           (Prod t9 t10))
      it "Intersection of Union of Products Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (Prod t9 t10)
           (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
                 (Or [(Prod t5 t6), (Prod t7 t8)])]))
      it "Intersection of Union of Products Subtyping 3" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 ->
          (compSubtype
           (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
                 (Or [(Prod t5 t6), (Prod t7 t8)])])
           (And [(Or [(Prod t9 t10), (Prod t11 t12)]),
                 (Or [(Prod t13 t14), (Prod t15 t16)])]))



    describe "Arrow Naive vs Efficient Subtype Comparisons" $ do
      it "Arrow Emptiness" $ property $
        \t1 t2 -> compIsEmpty (Arrow t1 t2)
      it "Arrow Subtyping" $ property $
        \t1 t2 t3 t4 -> compSubtype (Arrow t1 t2) (Arrow t3 t4)
      it "Arrow Equiv" $ property $
        \t1 t2 t3 t4 -> compEquiv (Arrow t1 t2) (Arrow t3 t4)
      it "Equivalent w.r.t. Overlap" $ property $
        \t1 t2 t3 t4 -> compOverlap (Arrow t1 t2) (Arrow t3 t4)
      it "Union of Arrows Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (Or [(Arrow t1 t2), (Arrow t3 t4)])
           (Arrow t5 t6))
      it "Union of Arrows Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (Arrow t5 t6)
           (Or [(Arrow t1 t2), (Arrow t3 t4)]))
      it "Intersection of Arrows Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (And [(Arrow t1 t2), (Arrow t3 t4)])
           (Arrow t5 t6))
      it "Intersection of Arrows Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 ->
          (compSubtype
           (Arrow t5 t6)
           (And [(Arrow t1 t2), (Arrow t3 t4)]))
      it "Union of Intersection of Arrows Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (Or [(And [(Arrow t1 t2), (Arrow t3 t4)]),
                (And [(Arrow t5 t6), (Arrow t7 t8)])])
          (Arrow t9 t10))
      it "Union of Intersection of Arrows Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (Arrow t9 t10)
           (Or [(And [(Arrow t1 t2), (Arrow t3 t4)]),
                (And [(Arrow t5 t6), (Arrow t7 t8)])]))
      it "Union of Intersection of Arrows Subtyping 3" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 ->
          (compSubtype
           (Or [(And [(Arrow t1 t2), (Arrow t3 t4)]),
                (And [(Arrow t5 t6), (Arrow t7 t8)])])
           (Or [(And [(Arrow t9 t10), (Arrow t11 t12)]),
                (And [(Arrow t13 t14), (Arrow t15 t16)])]))

      it "Intersection of Union of Arrows Subtyping 1" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (And [(Or [(Arrow t1 t2), (Arrow t3 t4)]),
                 (Or [(Arrow t5 t6), (Arrow t7 t8)])])
           (Arrow t9 t10))
      it "Intersection of Union of Arrows Subtyping 2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ->
          (compSubtype
           (Arrow t9 t10)
           (And [(Or [(Arrow t1 t2), (Arrow t3 t4)]),
                 (Or [(Arrow t5 t6), (Arrow t7 t8)])]))
      it "Intersection of Union of Arrows Subtyping 3" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 ->
          (compSubtype
           (And [(Or [(Arrow t1 t2), (Arrow t3 t4)]),
                 (Or [(Arrow t5 t6), (Arrow t7 t8)])])
           (And [(Or [(Arrow t9 t10), (Arrow t11 t12)]),
                 (Or [(Arrow t13 t14), (Arrow t15 t16)])]))


