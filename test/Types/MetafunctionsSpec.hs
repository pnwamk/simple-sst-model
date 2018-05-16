module Types.MetafunctionsSpec (spec) where


import Test.Hspec
import Types.Syntax
import qualified Types.LazyBDD as BDD
import qualified Types.Subtype as S
import qualified Types.Metafunctions as M
import Types.MetafunctionTests

  
spec :: Spec
spec = (genMetafunctionSpec
         BDD.parseTy
         S.subtype
         S.overlap
         S.equiv
         M.fstProj
         M.sndProj
         M.domTy
         M.rngTy)
