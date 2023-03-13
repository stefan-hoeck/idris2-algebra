module Prim.Bits16

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

export
props : Group
props = MkGroup "Bits16" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_mod",    prop_mod)
  , ("prop_div",    prop_div)
  , ("prop_divMod", prop_divMod)
  ] ++ ringProps ring_bits16 anyBits16
