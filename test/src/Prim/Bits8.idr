module Prim.Bits8

import Data.Prim.Bits8
import Data.SOP
import Hedgehog
import Prim.RingLaws

gt0 : Gen Bits8
gt0 = bits8 (linear 1 MaxBits8)

gt1 : Gen Bits8
gt1 = bits8 (linear 2 MaxBits8)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll anyBits8
  (b8 <= MaxBits8) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll anyBits8
  (b8 >= MinBits8) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyBits8, anyBits8]
  toOrdering (comp m n) === compare m n

prop_mod : Property
prop_mod = property $ do
  [n,d] <- forAll $ np [anyBits8, gt0]
  compare (n `mod` d) d === LT

prop_div : Property
prop_div = property $ do
  [n,d] <- forAll $ np [gt0, gt1]
  compare (n `div` d) n === LT

prop_divMod : Property
prop_divMod = property $ do
  [n,d] <- forAll $ np [anyBits8, gt0]
  let x = n `div` d
      r = n `mod` d
  n === x * d + r

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [anyBits8, anyBits8]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [anyBits8, anyBits8]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "Bits8" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_mod",    prop_mod)
  , ("prop_div",    prop_div)
  , ("prop_divMod", prop_divMod)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ] ++ ringProps ring_bits8 anyBits8
