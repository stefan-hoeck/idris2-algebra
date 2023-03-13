module Prim.Int16

import Data.Prim.Int16
import Data.SOP
import Hedgehog
import Prim.RingLaws

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll anyInt16
  (b8 <= MaxInt16) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll anyInt16
  (b8 >= MinInt16) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyInt16, anyInt16]
  toOrdering (comp m n) === compare m n

export
props : Group
props = MkGroup "Int16" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  ] ++ ringProps ring_int16 anyInt16
