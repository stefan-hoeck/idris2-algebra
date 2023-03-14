module Data.Prim.String

import public Control.Order
import public Control.Relation
import public Control.Relation.ReflexiveClosure
import public Control.Relation.Trichotomy
import public Data.Maybe0

%default total

unsafeRefl : a === b
unsafeRefl = believe_me (Builtin.Refl {x = a})

--------------------------------------------------------------------------------
--          (<)
--------------------------------------------------------------------------------

||| Witness that `m < n === True`.
export
data (<) : (m,n : String) -> Type where
  LT : {0 m,n : String} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : String) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : String) -> Type
(<=) = ReflexiveClosure (<)

--------------------------------------------------------------------------------
--          Order
--------------------------------------------------------------------------------

0 ltNotEQ : m < n -> Not (m === n)
ltNotEQ x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and EQ")

0 ltNotGT : m < n -> Not (n < m)
ltNotGT x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and GT")

0 eqNotLT : m === n -> Not (m < n)
eqNotLT = flip ltNotEQ

public export %inline
lt : (x,y : String) -> Maybe0 (x < y)
lt x y = case prim__lt_String x y of
  0 => Nothing0
  _ => Just0 (mkLT unsafeRefl)

public export %inline
lte : (x,y : String) -> Maybe0 (x <= y)
lte x y = case prim__lte_String x y of
  0 => Nothing0
  _ => Just0 (if x < y then (Rel $ mkLT unsafeRefl) else (fromEq unsafeRefl))

export
comp : (m,n : String) -> Trichotomy (<) m n
comp m n = case prim__lt_String m n of
  0 => case prim__eq_String m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Transitive String (<) where
  transitive _ _ = LT unsafeRefl

export %inline
Trichotomous String (<) where
  trichotomy m n = comp m n

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `String`
public export
MinString : String
MinString = ""

||| `m >= MinString` for all `m` of type `String`.
export
0 GTE_MinString : (m : String) -> MinString <= m
GTE_MinString m = case comp MinString m of
  LT x f g => %search
  EQ f x g => fromEq x
  GT f g x => assert_total $ idris_crash #"IMPOSSIBLE: String smaller than """#

||| Not value of type `String` is less than `MinString`.
export
0 Not_LT_MinString : m < MinString -> Void
Not_LT_MinString p = Not_LT_and_GTE p (GTE_MinString m)
