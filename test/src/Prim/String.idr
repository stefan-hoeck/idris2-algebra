module Prim.String

import Control.Relation.Trichotomy
import Data.Maybe0
import Data.Prim.String
import Data.SOP
import Hedgehog

anyString : Gen String
anyString = string (linear 0 30) unicodeAll

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll anyString
  (b8 >= MinString) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [anyString, anyString]
  toOrdering (comp m n) === compare m n

prop_lt : Property
prop_lt = property $ do
  [m,n] <- forAll $ np [anyString, anyString]
  isJust (lt m n) === (m < n)

prop_lte : Property
prop_lte = property $ do
  [m,n] <- forAll $ np [anyString, anyString]
  isJust (lte m n) === (m <= n)

export
props : Group
props = MkGroup "String"
  [ ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  , ("prop_lt",     prop_lt)
  , ("prop_lte",    prop_lte)
  ]

