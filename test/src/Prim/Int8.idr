module Prim.Int8

import Data.Prim.Int8
import Data.SOP
import Hedgehog
import Prim.RingLaws

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll anyInt8
  (b8 <= MaxInt8) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll anyInt8
  (b8 >= MinInt8) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyInt8, anyInt8]
  toOrdering (comp m n) === compare m n

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [anyInt8, anyInt8]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [anyInt8, anyInt8]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "Int8" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ] ++ ringProps ring_int8 anyInt8
