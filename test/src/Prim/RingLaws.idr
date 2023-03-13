module Prim.RingLaws

import Algebra.Group
import Algebra.Ring
import Data.SOP
import Hedgehog

parameters {0 a : Type}
           {z,o : a}
           {p,m,sub : Op2 a}
           (0 r : Ring a z o p m sub)
           {auto _ : Show a}
           {auto _ : Eq a}

  prop_plusCommutative : Gen a -> Property
  prop_plusCommutative g = property $ do
    [x,y] <- forAll $ np [g,g]
    p x y === p y x

  prop_plusAssociative : Gen a -> Property
  prop_plusAssociative g = property $ do
    [k,x,y] <- forAll $ np [g,g,g]
    p k (p x y) === p (p k x) y

  prop_plusZeroLeftNeutral : Gen a -> Property
  prop_plusZeroLeftNeutral g = property $ do
    y <- forAll g
    p z y === y

  prop_plusNegateLeftZero : Gen a -> Property
  prop_plusNegateLeftZero g = property $ do
    y <- forAll g
    p (sub z y) y === z

  prop_multCommutative : Gen a -> Property
  prop_multCommutative g = property $ do
    [x,y] <- forAll $ np [g,g]
    m x y === m y x

  prop_multAssociative : Gen a -> Property
  prop_multAssociative g = property $ do
    [k,x,y] <- forAll $ np [g,g,g]
    m k (m x y) === m (m k x) y

  prop_multOneLeftNeutral : Gen a -> Property
  prop_multOneLeftNeutral g = property $ do
    y <- forAll g
    m o y === y

  prop_distributive : Gen a -> Property
  prop_distributive g = property $ do
    [k,x,y] <- forAll $ np [g,g,g]
    m k (p x y) === p (m k x) (m k y)

  prop_minusAssociative : Gen a -> Property
  prop_minusAssociative g = property $ do
    [k,x,y] <- forAll $ np [g,g,g]
    p k (sub x y) === sub (p k x) y

  export
  ringProps : Gen a -> List (PropertyName,Property)
  ringProps g =
    [ ("prop_plusCommutative",     prop_plusCommutative g)
    , ("prop_plusAssociative",     prop_plusAssociative g)
    , ("prop_plusZeroLeftNeutral", prop_plusZeroLeftNeutral g)
    , ("prop_plusNegateLeftZero",  prop_plusNegateLeftZero g)
    , ("prop_multCommutative",     prop_multCommutative g)
    , ("prop_multAssociative",     prop_multAssociative g)
    , ("prop_multOneLeftNeutral",  prop_multOneLeftNeutral g)
    , ("prop_distributive",        prop_distributive g)
    , ("prop_minusAssociative",    prop_minusAssociative g)
  ]
