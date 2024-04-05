module Data.Prim.Bits32

import Algebra.Ring
import Control.Relation
import Control.Relation.ReflexiveClosure
import Control.Relation.Trichotomy
import Control.WellFounded
import Data.Maybe0

%default total

unsafeRefl : a === b
unsafeRefl = believe_me (Builtin.Refl {x = a})

||| Witness that `m < n === True`.
export
data (<) : (m,n : Bits32) -> Type where
  LT : {0 m,n : Bits32} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Bits32) -> Type
m > n = n < m

||| Alias for `ReflexiveClosure (<) m n`
public export
0 (<=) : (m,n : Bits32) -> Type
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
lt : (x,y : Bits32) -> Maybe0 (x < y)
lt x y = case prim__lt_Bits32 x y of
  0 => Nothing0
  _ => Just0 (mkLT unsafeRefl)

public export %inline
lte : (x,y : Bits32) -> Maybe0 (x <= y)
lte x y = case prim__lte_Bits32 x y of
  0 => Nothing0
  _ => Just0 (if x < y then (Rel $ mkLT unsafeRefl) else (fromEq unsafeRefl))

export
comp : (m,n : Bits32) -> Trichotomy (<) m n
comp m n = case prim__lt_Bits32 m n of
  0 => case prim__eq_Bits32 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Transitive Bits32 (<) where
  transitive _ _ = LT unsafeRefl

export %inline
Trichotomous Bits32 (<) where
  trichotomy m n = comp m n

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Bits32`
public export
MinBits32 : Bits32
MinBits32 = 0

||| Upper bound of `Bits32`
public export
MaxBits32 : Bits32
MaxBits32 = 0xffff_ffff

||| `m >= 0` for all `m` of type `Bits32`.
export
0 GTE_MinBits32 : (m : Bits32) -> MinBits32 <= m
GTE_MinBits32 m = case comp MinBits32 m of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Bits32 smaller than 0"

||| Not value of type `Bits32` is less than zero.
export
0 Not_LT_MinBits32 : m < 0 -> Void
Not_LT_MinBits32 p = Not_LT_and_GTE p (GTE_MinBits32 m)

||| `m <= MaxBits32` for all `m` of type `Bits32`.
export
0 LTE_MaxBits32 : (m : Bits32) -> m <= MaxBits32
LTE_MaxBits32 m = case comp m MaxBits32 of
  LT x f g => Rel x
  EQ f x g => fromEq x
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Bits32 greater than \{show MaxBits32}"

||| Not value of type `Bits32` is greater than `MaxBits32`.
export
0 Not_GT_MaxBits32 : m > MaxBits32 -> Void
Not_GT_MaxBits32 p = Not_LT_and_GTE p (LTE_MaxBits32 m)

||| Every value of type `Bits32` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Bits32) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

namespace WellFounded
  ||| `(<)` is well founded.
  export %inline
  [LT] WellFounded Bits32 (<) where
    wellFounded = accessLT

  ||| Every value of type `Bits32` is accessible with relation
  ||| to `(>)`.
  export
  accessGT : (m : Bits32) -> Accessible (>) m
  accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

  ||| `(>)` is well founded.
  export %inline
  [GT] WellFounded Bits32 (>) where
    wellFounded = accessGT
