module Types.SubtypeSpec (spec) where


import Test.Hspec
import qualified Types.Subtype as S
import qualified Types.LazyBDD as BDD
import Types.Syntax
import Types.SubtypeTests


spec :: Spec
spec = genSubtypeSpec BDD.parseTy S.subtype S.overlap S.equiv
