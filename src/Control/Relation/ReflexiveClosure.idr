||| Utility for describing chains of values linked via
||| a transitive relation.
module Control.Relation.ReflexiveClosure

import public Control.Order
import public Control.Relation

%default total

||| The reflexive closure of a (typically transitive) relation.
|||
||| This converts a transitive relation into a preorder.
||| For instance, if `(<)` is a transitive relation over the integers,
||| `ReflexiveClosure (<)` (corresponding to `(<=)` is a transitive,
||| reflexive relation over the integers.
public export
data ReflexiveClosure : (rel : a -> a -> Type) -> (x,y : a) -> Type where
  Rel  : {0 rel : _} -> (0 prf : rel x y) -> ReflexiveClosure rel x y
  Refl : {0 rel : _} -> ReflexiveClosure rel x x

public export
Reflexive a (ReflexiveClosure rel) where
  reflexive = Refl

public export
Transitive a rel => Transitive a (ReflexiveClosure rel) where
  transitive (Rel x) (Rel y) = Rel $ transitive x y
  transitive (Rel x) Refl    = Rel x
  transitive Refl    y       = y

public export
fromEq : {0 rel : _} -> (0 p : x === y) -> ReflexiveClosure rel x y
fromEq Refl = Refl

--------------------------------------------------------------------------------
--          Transitive Chain
--------------------------------------------------------------------------------

||| A chain of values, linke by relation `ReflexiveClosure rel`.
public export
data Chain : (rel : a -> a -> Type) -> (x,y : a) -> Type where
  Nil  : {0 rel : a -> a -> Type} -> Chain rel x x
  (::) :
       {0 rel : a -> a -> Type}
    -> (0 x : a)
    -> (c : Chain rel y z)
    -> {auto 0 p : ReflexiveClosure rel x y}
    -> Chain rel x z

||| Witness that at least one link in a chain of values
||| linked via `ReflexiveClosure rel` is string, and
||| therefore (if `rel` is transitive), `rel x y` holds.
|||
||| For instance, assume `rel` is `(<)` over the integers.
||| Then `ReflexiveClosure rel` corresponds to `(<=)`.
||| If we have the chain `w <= x <= y <= z` and we can
||| show that one of the inequalities is strict (for instance,
||| that `y < z`), then we can not only show that `w <= z` but
||| that `w < z`.
public export
data IsStrict : {rel : _} -> Chain rel x y -> Type where
  Here  : IsStrict ((::) x c @{Rel p})
  There : IsStrict c -> IsStrict ((::) x c @{p})

||| If `x` and `y` are linked via a preorder `rel` over a chain
||| of values, then `rel x y` holds.
public export
0 chain : Preorder a rel => Chain rel x y -> rel x y
chain []                  = reflexive
chain ((::) _ c @{Rel x}) = transitive x (chain c)
chain ((::) _ c @{Refl})  = chain c

||| If `x` and `y` are linked via `ReflexiveClosure rel` for a transitive
||| relation `rel` over a chain of values, then `ReflexiveClosure rel x y` holds.
public export
0 weak : Transitive a rel => Chain rel x y -> ReflexiveClosure rel x y
weak []              = Refl
weak ((::) _ c @{p}) = transitive p $ weak c

||| If `x` and `y` are linked via `ReflexiveClosure rel` for a transitive
||| relation `rel` over a chain of values, and at least one link ist
||| strict, the `rel x y` holds.
public export
0 strict :
     Transitive a rel
  => (c : Chain rel x y)
  -> {auto p : IsStrict c}
  -> rel x y
strict ((::) _ c @{Rel q}) {p = Here} = case weak c of
  Rel z  => transitive q z
  Refl   => q
strict ((::) _ c @{Rel q}) {p = There _} = transitive q $ strict c
strict ((::) _ c @{Refl})  {p = There _} = strict c
