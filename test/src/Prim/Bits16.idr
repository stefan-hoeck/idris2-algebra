module Prim.Bits16

import Algebra.Ring
import Control.Relation.Trichotomy
import Data.Maybe0
import Data.Prim.Bits16
import Data.SOP
import Hedgehog
import Prim.RingLaws

gt0 : Gen Bits16
gt0 = bits16 (linear 1 MaxBits16)

gt1 : Gen Bits16
gt1 = bits16 (linear 2 MaxBits16)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll anyBits16
  (b8 <= MaxBits16) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll anyBits16
  (b8 >= MinBits16) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyBits16, anyBits16]
  toOrdering (comp m n) === compare m n

prop_mod : Property
prop_mod = property $ do
  [n,d] <- forAll $ np [anyBits16, gt0]
  compare (n `mod` d) d === LT

prop_div : Property
prop_div = property $ do
  [n,d] <- forAll $ np [gt0, gt1]
  compare (n `div` d) n === LT

prop_divMod : Property
prop_divMod = property $ do
  [n,d] <- forAll $ np [anyBits16, gt0]
  let x = n `div` d
      r = n `mod` d
  n === x * d + r

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [anyBits16, anyBits16]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [anyBits16, anyBits16]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "Bits16" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_mod",    prop_mod)
  , ("prop_div",    prop_div)
  , ("prop_divMod", prop_divMod)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ] ++ ringProps ring_bits16 anyBits16
