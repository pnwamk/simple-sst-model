module Types.MetafunctionTests (genMetafunctionSpec) where


import Test.Hspec
import Test.QuickCheck
import Types.Syntax


genMetafunctionSpec ::
  (Ty -> a)
  -> (a -> a -> Bool)
  -> (a -> a -> Bool)
  -> (a -> a -> Bool)
  -> (a -> Maybe a)
  -> (a -> Maybe a)
  -> (a -> Maybe a)
  -> (a -> a -> Maybe a)
  -> Spec
genMetafunctionSpec
  parse
  rawSubtype
  rawOverlap
  rawEquiv
  rawFstProj
  rawSndProj
  rawDomTy
  rawRngTy = do
  describe "First Projection Tests" $ do
    it "Projection from Empty 1" $ do
      fstProjEquiv Empty Empty `shouldBe` True
    it "Projection from Empty 2" $ do
      fstProjEquiv (And [Prod (Or [T,Z]) F,Not (Prod Z Any)]) T `shouldBe` True
    it "Simple Pair" $ property $
      \t -> fstProjEquiv (Prod t Any) t
    it "Union of Pairs" $ property $
      \t1 t2 -> (fstProjEquiv
                 (Or [(Prod t1 Any), (Prod t2 Any)])
                 (Or [t1, t2]))
    it "Intersection of Pairs" $ property $
      \t1 t2 -> (fstProjEquiv
                 (And [(Prod t1 Any), (Prod t2 Any)])
                 (And [t1, t2]))
    it "Intersection of Union of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (fstProjEquiv
         (And [(Or [(Prod t1 Any), (Prod t2 Any)]),
               (Or [(Prod t3 Any), (Prod t4 Any)])])
          (And [(Or [t1, t2]),
                (Or [t3, t4])]))
    it "Intersection of Union of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (fstProjSubtype
         (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
               (Or [(Prod t5 t6), (Prod t7 t8)])])
         (And [(Or [t1, t3]),
               (Or [t5, t7])]))
    it "Union of Intersection of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (fstProjEquiv
         (Or [(And [(Prod t1 Any), (Prod t2 Any)]),
              (And [(Prod t3 Any), (Prod t4 Any)])])
          (Or [(And [t1, t2]),
               (And [t3, t4])]))
    it "Union of Intersection of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (fstProjSubtype
         (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
              (And [(Prod t5 t6), (Prod t7 t8)])])
          (Or [(And [t1, t3]),
               (And [t5, t7])]))

  describe "Second Projection Tests" $ do
    it "Projection from Empty 1" $ do
      (sndProjEquiv Empty Empty) `shouldBe` True
    it "Projection from Empty 2" $ do
      (sndProjEquiv (And [Prod F (Or [T,Z]),Not (Prod Any Z)]) T)
        `shouldBe`
        True
    it "Simple Pair" $ property $
      \t -> sndProjEquiv (Prod Any t) t
    it "Union of Pairs" $ property $
      \t1 t2 -> sndProjEquiv (Or [(Prod Any t1), (Prod Any t2)]) (Or [t1, t2])
    it "Intersection of Pairs" $ property $
      \t1 t2 -> sndProjEquiv (And [(Prod Any t1), (Prod Any t2)]) (And [t1, t2])
    it "Intersection of Union of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (sndProjEquiv
         (And [(Or [(Prod Any t1), (Prod Any t2)]),
               (Or [(Prod Any t3), (Prod Any t4)])])
          (And [(Or [t1, t2]),
                (Or [t3, t4])]))
    it "Intersection of Union of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (sndProjSubtype
         (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
               (Or [(Prod t5 t6), (Prod t7 t8)])])
         (And [(Or [t2, t4]),
               (Or [t6, t8])]))
    it "Union of Intersection of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (sndProjEquiv
         (Or [(And [(Prod Any t1), (Prod Any t2)]),
              (And [(Prod Any t3), (Prod Any t4)])])
          (Or [(And [t1, t2]),
               (And [t3, t4])]))
    it "Union of Intersection of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (sndProjSubtype
         (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
              (And [(Prod t5 t6), (Prod t7 t8)])])
          (Or [(And [t2, t4]),
               (And [t6, t8])]))

  describe "Function Domain Tests" $ do
    it "Simple Arrow" $ property $
      \t1 t2 -> domTyEquiv (Arrow t1 t2) t1
    it "Arrow Intersection" $ property $
      \t1 t2 t3 t4 -> (domTyEquiv
                       (And [(Arrow t1 t2),
                             (Arrow t3 t4)])
                        (Or [t1, t3]))
    it "Arrow Union" $ property $
      \t1 t2 t3 t4 -> (domTyEquiv
                       (Or [(Arrow t1 t2),
                            (Arrow t3 t4)])
                        (And [t1, t3]))

  describe "Function Range Tests" $ do
    it "Simple Arrow1" $ do
      (rngTyEquiv (Arrow T F) T F `shouldBe` True)
    it "Simple Arrow2" $ do
      (rngTyEquiv
       (And [(Arrow (Or [T, F]) F),
             (Arrow (Or [T, Z]) F)])
       T
       F
        `shouldBe`
        True)
    it "Simple Arrow3" $ do
      (rngTyEquiv
       (And [(Arrow (Or [T, F]) (Or [T, F])),
             (Arrow (Or [T, Z]) (Or [Z, F]))])
       T
       F
        `shouldBe`
        True)
    it "Simple Arrow4" $ do
      (rngTyEquiv
       (And [(Arrow (Or [T, F]) (Or [T, F])),
             (Arrow (Or [T, Z]) (Or [Z, F])),
             (Arrow (Or [F, Z]) T)])
       T
       F
        `shouldBe`
        True)
        -- TODO add more


    -- it "Simple Arrow" $ property $
    --   \t1 t2 -> rngTyEquiv (Arrow t1 t2) t1 t2
    -- it "Arrow Intersection1" $ property $
    --   \t1 t2 t3 t4 -> (rngTyEquiv
    --                    (And [(Arrow t1 t2),
    --                          (Arrow t3 t4)])
    --                     t1
    --                     (if subtype t1 t3
    --                      then And [t2, t4]
    --                      else t2))
    -- it "Arrow Intersection2" $ property $
    --   \t1 t2 t3 t4 -> (rngTyEquiv
    --                    (And [(Arrow t1 t2),
    --                          (Arrow t3 t4)])
    --                     t3
    --                     (if subtype t3 t1
    --                      then And [t2, t4]
    --                      else t4))
    -- it "Arrow Intersection3" $ property $
    --   \t1 t2 t3 t4 -> (rngTyEquiv
    --                    (And [(Arrow t1 t2),
    --                          (Arrow t3 t4)])
    --                     (Or [t1, t3])
    --                     (Or [t2, t4]))
    -- it "Arrow Union" $ property $
    --   \t1 t2 -> (rngTyEquiv
    --               (Or [(Arrow (Or [T, Z]) t1),
    --                    (Arrow (Or [T, F]) t2)])
    --               T
    --             (Or [t1, t2]))


    where fstProjEquiv :: Ty -> Ty -> Bool
          fstProjEquiv rawt1 rawt2 =
            case (rawFstProj t1) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          fstProjSubtype :: Ty -> Ty -> Bool
          fstProjSubtype rawt1 rawt2 =
            case (rawFstProj t1) of
              Nothing  -> False
              Just t1' -> rawSubtype t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          sndProjEquiv :: Ty -> Ty -> Bool
          sndProjEquiv rawt1 rawt2 =
            case (rawSndProj t1) of
              Nothing -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          sndProjSubtype :: Ty -> Ty -> Bool
          sndProjSubtype rawt1 rawt2 =
            case (rawSndProj t1) of
              Nothing  -> False
              (Just t1') -> rawSubtype t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          domTyEquiv :: Ty -> Ty -> Bool
          domTyEquiv rawt1 rawt2 =
            case (rawDomTy t1) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          rngTyEquiv :: Ty -> Ty -> Ty -> Bool
          rngTyEquiv rawt1 rawargty rawt2 =
            case (rawRngTy t1 argty) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  argty = (parse rawargty)
                  t2 = (parse rawt2)
