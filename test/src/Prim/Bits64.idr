module Prim.Bits64

import Algebra.Ring
import Control.Relation.Trichotomy
import Data.Maybe0
import Data.Prim.Bits64
import Data.SOP
import Hedgehog
import Prim.RingLaws

gt0 : Gen Bits64
gt0 = bits64 (linear 1 MaxBits64)

gt1 : Gen Bits64
gt1 = bits64 (linear 2 MaxBits64)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll anyBits64
  (b8 <= MaxBits64) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll anyBits64
  (b8 >= MinBits64) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyBits64, anyBits64]
  toOrdering (comp m n) === compare m n

prop_mod : Property
prop_mod = property $ do
  [n,d] <- forAll $ np [anyBits64, gt0]
  compare (n `mod` d) d === LT

prop_div : Property
prop_div = property $ do
  [n,d] <- forAll $ np [gt0, gt1]
  compare (n `div` d) n === LT

prop_divMod : Property
prop_divMod = property $ do
  [n,d] <- forAll $ np [anyBits64, gt0]
  let x = n `div` d
      r = n `mod` d
  n === x * d + r

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [anyBits64, anyBits64]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [anyBits64, anyBits64]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "Bits64" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_mod",    prop_mod)
  , ("prop_div",    prop_div)
  , ("prop_divMod", prop_divMod)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ] ++ ringProps ring_bits64 anyBits64
