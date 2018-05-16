module Types.MetafunctionsCompSpec (spec) where

import Test.Hspec
import Test.QuickCheck (property)
import Types.Subtype
import qualified Types.LazyBDD as BDD
import qualified Types.NMetafunctions as N
import qualified Types.Metafunctions as M
import Types.Syntax

equivMaybeTy :: Maybe BDD.Ty -> Maybe BDD.Ty -> Bool
equivMaybeTy Nothing Nothing = True
equivMaybeTy (Just t1) (Just t2) = equiv t1 t2
equivMaybeTy _ _ = False

compUnMaybeOp ::
  (BDD.Ty -> Maybe BDD.Ty)
  -> (BDD.Ty -> Maybe BDD.Ty)
  -> Ty
  -> Bool
compUnMaybeOp op1 op2 rawt = equivMaybeTy res1 res2
  where t = BDD.parseTy rawt
        res1 = op1 t
        res2 = op2 t

compFstProj :: Ty -> Bool
compFstProj = compUnMaybeOp N.fstProj M.fstProj

compSndProj :: Ty -> Bool
compSndProj = compUnMaybeOp N.domTy M.domTy

compDomTy :: Ty -> Bool
compDomTy = compUnMaybeOp N.domTy M.domTy

compRngTy :: Ty -> Ty -> Bool
compRngTy rawfty rawargty = equivMaybeTy res1 res2
  where fty = BDD.parseTy rawfty
        argty = BDD.parseTy rawargty
        res1 = N.rngTy fty argty
        res2 = M.rngTy fty argty

spec :: Spec
spec = do
    describe "Naive vs Efficient First Projection Comparison" $ do
      it "Equivalent First Projections" $ property $
        \t -> compFstProj t
      it "Simple Pair" $ property $
        \t -> compFstProj (Prod t Any)
      it "Union of Pairs" $ property $
        \t1 t2 -> compFstProj (Or [(Prod t1 Any), (Prod t2 Any)])
      it "Intersection of Pairs" $ property $
        \t1 t2 -> compFstProj (And [(Prod t1 Any), (Prod t2 Any)])
      it "Intersection of Pairs with Negation" $ property $
        \t1 t2 t3 t4 -> compFstProj (And [(Prod t1 t2), (Not (Prod t3 t4))])
      it "Intersection of Union of Pairs1" $ property $
        \t1 t2 t3 t4 ->
          (compFstProj
           (And [(Or [(Prod t1 Any), (Prod t2 Any)]),
                 (Or [(Prod t3 Any), (Prod t4 Any)])]))
      it "Intersection of Union of Pairs2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          (compFstProj
           (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
                 (Or [(Prod t5 t6), (Prod t7 t8)])]))
      it "Union of Intersection of Pairs1" $ property $
        \t1 t2 t3 t4 ->
          (compFstProj
           (Or [(And [(Prod t1 Any), (Prod t2 Any)]),
                (And [(Prod t3 Any), (Prod t4 Any)])]))
      it "Union of Intersection of Pairs2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          (compFstProj
           (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
                (And [(Prod t5 t6), (Prod t7 t8)])]))
      it "Union of Intersection of Pairs3" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12->
          (compFstProj
           (Or [(And [(Prod t1 t2), (Prod t3 t4),  (Not (Prod t5 t6))]),
                (And [(Prod t7 t8), (Prod t9 t10), (Not (Prod t11 t12))])]))


    describe "Second Projection Tests" $ do
      it "Simple Pair" $ property $
        \t -> compSndProj (Prod Any t)
      it "Union of Pairs" $ property $
        \t1 t2 -> compSndProj (Or [(Prod Any t1), (Prod Any t2)])
      it "Intersection of Pairs" $ property $
        \t1 t2 -> compSndProj (And [(Prod Any t1), (Prod Any t2)])
      it "Intersection of Pairs with Negation" $ property $
        \t1 t2 t3 t4 -> compSndProj (And [(Prod t1 t2), (Not (Prod t3 t4))])
      it "Intersection of Union of Pairs1" $ property $
        \t1 t2 t3 t4 ->
          (compSndProj
           (And [(Or [(Prod Any t1), (Prod Any t2)]),
                 (Or [(Prod Any t3), (Prod Any t4)])]))
      it "Intersection of Union of Pairs2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          (compSndProj
           (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
                 (Or [(Prod t5 t6), (Prod t7 t8)])]))
      it "Union of Intersection of Pairs1" $ property $
        \t1 t2 t3 t4 ->
          (compSndProj
           (Or [(And [(Prod Any t1), (Prod Any t2)]),
                (And [(Prod Any t3), (Prod Any t4)])]))
      it "Union of Intersection of Pairs2" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          (compSndProj
           (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
                (And [(Prod t5 t6), (Prod t7 t8)])]))
      it "Union of Intersection of Pairs3" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12->
          (compSndProj
           (Or [(And [(Prod t1 t2), (Prod t3 t4),  (Not (Prod t5 t6))]),
                (And [(Prod t7 t8), (Prod t9 t10), (Not (Prod t11 t12))])]))


    describe "Function Domain Tests" $ do
      it "Random Type" $ property $
        \t -> compDomTy t
      it "Simple Arrow" $ property $
        \t1 t2 -> compDomTy (Arrow t1 t2)
      it "Arrow Intersection" $ property $
        \t1 t2 t3 t4 -> (compDomTy
                         (And [(Arrow t1 t2),
                               (Arrow t3 t4)]))
      it "Arrow Union" $ property $
        \t1 t2 t3 t4 -> (compDomTy
                         (Or [(Arrow t1 t2),
                              (Arrow t3 t4)]))
      it "Arrow Intersection of Union" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          (compDomTy
            (And [(Or [(Arrow t1 t2),
                       (Arrow t3 t4)]),
                  (Or [(Arrow t5 t6),
                       (Arrow t7 t8)])]))
      it "Arrow Union of Intersection" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 ->
          (compDomTy
            (Or [(And [(Arrow t1 t2),
                       (Arrow t3 t4)]),
                 (And [(Arrow t5 t6),
                       (Arrow t7 t8)])]))


    describe "Function Range Tests" $ do
      it "Random Type" $ property $
        \t1 t2 -> compRngTy t1 t2
      it "Simple Arrow" $ property $
        \t1 t2 t3 -> compRngTy (Arrow t1 t2) t3
      it "Arrow Intersection" $ property $
        \t1 t2 t3 t4 t5 -> (compRngTy
                            (And [(Arrow t1 t2),
                                  (Arrow t3 t4)])
                           t5)
      it "Arrow Union" $ property $
        \t1 t2 t3 t4 t5 -> (compRngTy
                            (Or [(Arrow t1 t2),
                                 (Arrow t3 t4)])
                           t5)
      it "Arrow Intersection of Unions" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 ->
          (compRngTy
            (And [(Or [(Arrow t1 t2),
                       (Arrow t3 t4)]),
                   (Or [(Arrow t5 t6),
                        (Arrow t7 t8)])])
            t9)
      it "Arrow Union of Intersections" $ property $
        \t1 t2 t3 t4 t5 t6 t7 t8 t9 ->
          (compRngTy
            (Or [(And [(Arrow t1 t2),
                       (Arrow t3 t4)]),
                 (And [(Arrow t5 t6),
                       (Arrow t7 t8)])])
            t9)
