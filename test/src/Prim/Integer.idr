module Prim.Integer

import Algebra.Ring
import Control.Relation.Trichotomy
import Data.Maybe0
import Data.Prim.Integer
import Data.SOP
import Hedgehog
import Prim.RingLaws

anyInteger : Gen Integer
anyInteger = integer (linear (-0x8000_0000_0000_0000) 0xffff_ffff_ffff_ffff)

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyInteger, anyInteger]
  toOrdering (comp m n) === compare m n

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [anyInteger, anyInteger]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [anyInteger, anyInteger]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "Int16" $
  [ ("prop_comp",   prop_comp)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ] ++ ringProps ring_integer anyInteger
