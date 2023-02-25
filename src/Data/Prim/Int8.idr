module Data.Prim.Int8

import public Algebra.Ring
import public Control.Order
import public Control.Relation
import public Control.Relation.ReflexiveClosure
import public Control.Relation.Trichotomy
import public Control.WellFounded
import public Data.Maybe0

%default total

unsafeRefl : a === b
unsafeRefl = believe_me (Builtin.Refl {x = a})

||| Witness that `m < n === True`.
export
data (<) : (m,n : Int8) -> Type where
  LT : {0 m,n : Int8} -> (0 prf : (m < n) === True) -> m < n

||| Makes a compile-time proof of `x < y` available at runtime.
|||
||| Heads up: `(<)` is not supposed to be used or even needed at runtime,
||| as it will be erased anymay. However, this function is sometimes
||| required, for instance when implementing interface `Connex`.
export
unerase : (0 p : m < n) -> m < n
unerase (LT p) = LT p

||| Contructor for `(<)`.
|||
||| This can only be used in an erased context.
export %hint
0 mkLT : (0 prf : (m < n) === True) -> m < n
mkLT = LT

||| Extractor for `(<)`.
|||
||| This can only be used in an erased context.
export
0 runLT : m < n -> (m < n) === True
runLT (LT prf) = prf

||| We don't trust values of type `(<)` too much,
||| so we use this when creating magical results.
export
strictLT : (0 p : m < n) -> Lazy c -> c
strictLT (LT prf) x = x

--------------------------------------------------------------------------------
--          Aliases
--------------------------------------------------------------------------------

||| Flipped version of `(<)`.
public export
0 (>) : (m,n : Int8) -> Type
m > n = n < m

||| Alias for `ReflexiveClosure (<) m n`
public export
0 (<=) : (m,n : Int8) -> Type
(<=) = ReflexiveClosure (<)

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

0 ltNotEQ : m < n -> Not (m === n)
ltNotEQ x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and EQ")

0 ltNotGT : m < n -> Not (n < m)
ltNotGT x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and GT")

0 eqNotLT : m === n -> Not (m < n)
eqNotLT = flip ltNotEQ

public export %inline
lt : (x,y : Int8) -> Maybe0 (x < y)
lt x y = case prim__lt_Int8 x y of
  0 => Nothing0
  _ => Just0 (mkLT unsafeRefl)

public export %inline
lte : (x,y : Int8) -> Maybe0 (x <= y)
lte x y = case prim__lte_Int8 x y of
  0 => Nothing0
  _ => Just0 (if x < y then (Rel $ mkLT unsafeRefl) else (fromEq unsafeRefl))

export
comp : (m,n : Int8) -> Trichotomy (<) m n
comp m n = case prim__lt_Int8 m n of
  0 => case prim__eq_Int8 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Transitive Int8 (<) where
  transitive _ _ = LT unsafeRefl

export %inline
Trichotomous Int8 (<) where
  trichotomy m n = comp m n

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Int8`
public export
MinInt8 : Int8
MinInt8 = -0x80

||| Upper bound of `Int8`
public export
MaxInt8 : Int8
MaxInt8 = 0x7f

||| `m >= 0` for all `m` of type `Int8`.
export
0 GTE_MinInt8 : (m : Int8) -> MinInt8 <= m
GTE_MinInt8 m = case comp MinInt8 m of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Int8 smaller than 0"

||| Not value of type `Int8` is less than zero.
export
0 Not_LT_MinInt8 : m < 0 -> Void

||| `m <= MaxInt8` for all `m` of type `Int8`.
export
0 LTE_MaxInt8 : (m : Int8) -> m <= MaxInt8
LTE_MaxInt8 m = case comp m MaxInt8 of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int8 greater than \{show MaxInt8}"

||| Not value of type `Int8` is greater than `MaxInt8`.
export
0 Not_GT_MaxInt8 : m > MaxInt8 -> Void

||| Every value of type `Int8` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Int8) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

namespace WellFounded
  ||| `(<)` is well founded.
  export %inline
  [LT] WellFounded Int8 (<) where
    wellFounded = accessLT

  ||| Every value of type `Int8` is accessible with relation
  ||| to `(>)`.
  export
  accessGT : (m : Int8) -> Accessible (>) m
  accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

  ||| `(>)` is well founded.
  export %inline
  [GT] WellFounded Int8 (>) where
    wellFounded = accessGT
