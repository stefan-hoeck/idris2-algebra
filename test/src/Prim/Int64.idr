module Prim.Int64

import Algebra.Ring
import Control.Relation.Trichotomy
import Data.Maybe0
import Data.Prim.Int64
import Data.SOP
import Hedgehog
import Prim.RingLaws

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll anyInt64
  (b8 <= MaxInt64) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll anyInt64
  (b8 >= MinInt64) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyInt64, anyInt64]
  toOrdering (comp m n) === compare m n

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [anyInt64, anyInt64]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [anyInt64, anyInt64]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "Int64" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ] ++ ringProps ring_int64 anyInt64
