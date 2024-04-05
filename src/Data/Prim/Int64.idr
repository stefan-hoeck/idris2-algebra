module Data.Prim.Int64

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
data (<) : (m,n : Int64) -> Type where
  LT : {0 m,n : Int64} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Int64) -> Type
m > n = n < m

||| Alias for `ReflexiveClosure (<) m n`
public export
0 (<=) : (m,n : Int64) -> Type
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
lt : (x,y : Int64) -> Maybe0 (x < y)
lt x y = case prim__lt_Int64 x y of
  0 => Nothing0
  _ => Just0 (mkLT unsafeRefl)

public export %inline
lte : (x,y : Int64) -> Maybe0 (x <= y)
lte x y = case prim__lte_Int64 x y of
  0 => Nothing0
  _ => Just0 (if x < y then (Rel $ mkLT unsafeRefl) else (fromEq unsafeRefl))

export
comp : (m,n : Int64) -> Trichotomy (<) m n
comp m n = case prim__lt_Int64 m n of
  0 => case prim__eq_Int64 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Transitive Int64 (<) where
  transitive _ _ = LT unsafeRefl

export %inline
Trichotomous Int64 (<) where
  trichotomy m n = comp m n

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Int64`
public export
MinInt64 : Int64
MinInt64 = -0x8000_0000_0000_0000

||| Upper bound of `Int64`
public export
MaxInt64 : Int64
MaxInt64 = 0x7fff_ffff_ffff_ffff

||| `m >= 0` for all `m` of type `Int64`.
export
0 GTE_MinInt64 : (m : Int64) -> MinInt64 <= m
GTE_MinInt64 m = case comp MinInt64 m of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Int64 smaller than 0"

||| Not value of type `Int64` is less than zero.
export
0 Not_LT_MinInt64 : m < MinInt64 -> Void
Not_LT_MinInt64 p = Not_LT_and_GTE p (GTE_MinInt64 m)

||| `m <= MaxInt64` for all `m` of type `Int64`.
export
0 LTE_MaxInt64 : (m : Int64) -> m <= MaxInt64
LTE_MaxInt64 m = case comp m MaxInt64 of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int64 greater than \{show MaxInt64}"

||| Not value of type `Int64` is greater than `MaxInt64`.
export
0 Not_GT_MaxInt64 : m > MaxInt64 -> Void
Not_GT_MaxInt64 p = Not_LT_and_GTE p (LTE_MaxInt64 m)

||| Every value of type `Int64` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Int64) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

namespace WellFounded
  ||| `(<)` is well founded.
  export %inline
  [LT] WellFounded Int64 (<) where
    wellFounded = accessLT

  ||| Every value of type `Int64` is accessible with relation
  ||| to `(>)`.
  export
  accessGT : (m : Int64) -> Accessible (>) m
  accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

  ||| `(>)` is well founded.
  export %inline
  [GT] WellFounded Int64 (>) where
    wellFounded = accessGT
