module Data.Prim.Bits8

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
data (<) : (m,n : Bits8) -> Type where
  LT : {0 m,n : Bits8} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Bits8) -> Type
m > n = n < m

||| Alias for `ReflexiveClosure (<) m n`
public export
0 (<=) : (m,n : Bits8) -> Type
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
lt : (x,y : Bits8) -> Maybe0 (x < y)
lt x y = case prim__lt_Bits8 x y of
  0 => Nothing0
  _ => Just0 (mkLT unsafeRefl)

public export %inline
lte : (x,y : Bits8) -> Maybe0 (x <= y)
lte x y = case prim__lte_Bits8 x y of
  0 => Nothing0
  _ => Just0 (if x < y then (Rel $ mkLT unsafeRefl) else (fromEq unsafeRefl))

export
comp : (m,n : Bits8) -> Trichotomy (<) m n
comp m n = case prim__lt_Bits8 m n of
  0 => case prim__eq_Bits8 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Transitive Bits8 (<) where
  transitive _ _ = LT unsafeRefl

export %inline
Trichotomous Bits8 (===) (<) where
  trichotomy m n = comp m n
  eqLeft Refl lt = lt
  eqRight lt Refl = lt

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Bits8`
public export
MinBits8 : Bits8
MinBits8 = 0

||| Upper bound of `Bits8`
public export
MaxBits8 : Bits8
MaxBits8 = 0xff

||| `m >= 0` for all `m` of type `Bits8`.
export
0 GTE_MinBits8 : (m : Bits8) -> MinBits8 <= m
GTE_MinBits8 m = case comp MinBits8 m of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Bits8 smaller than 0"

||| Not value of type `Bits8` is less than zero.
export
0 Not_LT_MinBits8 : m < 0 -> Void
Not_LT_MinBits8 p = Not_LT_and_GTE p (GTE_MinBits8 m)

||| `m <= MaxBits8` for all `m` of type `Bits8`.
export
0 LTE_MaxBits8 : (m : Bits8) -> m <= MaxBits8
LTE_MaxBits8 m = case comp m MaxBits8 of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Bits8 greater than \{show MaxBits8}"

||| Not value of type `Bits8` is greater than `MaxBits8`.
export
0 Not_GT_MaxBits8 : m > MaxBits8 -> Void
Not_GT_MaxBits8 p = Not_LT_and_GTE p (LTE_MaxBits8 m)

||| Every value of type `Bits8` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Bits8) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

namespace WellFounded
  ||| `(<)` is well founded.
  export %inline
  [LT] WellFounded Bits8 (<) where
    wellFounded = accessLT

  ||| Every value of type `Bits8` is accessible with relation
  ||| to `(>)`.
  export
  accessGT : (m : Bits8) -> Accessible (>) m
  accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

  ||| `(>)` is well founded.
  export %inline
  [GT] WellFounded Bits8 (>) where
    wellFounded = accessGT
