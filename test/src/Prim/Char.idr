module Prim.Char

import Data.Prim.Char
import Data.SOP
import Hedgehog

prop_ltMin : Property
prop_ltMin = property $ do
  ch <- forAll unicode
  (ch >= MinChar) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [unicode, unicode]
  toOrdering (comp m n) === compare m n

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [unicode, unicode]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [unicode, unicode]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "Char" $
  [ ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ]
