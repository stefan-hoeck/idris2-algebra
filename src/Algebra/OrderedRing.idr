module Algebra.OrderedRing

import Algebra.Solver.Ring
import Control.Relation.ReflexiveClosure
import Control.Relation.Trichotomy
import Syntax.PreorderReasoning.Generic

%default total

public export
record OrderedRing (a : Type) (lt : a -> a -> Type) (z,o : a) (p,m,sub : Op2 a) where
  constructor MkOR
  ring   : Ring a z o p m sub
  strict : Strict a lt
  add    : {u,v,w : a} -> lt u v -> lt (p u w) (p v w)
  mult   : {u,v,w : a} -> lt u v -> lt z w -> lt (m u w) (m v w)

parameters {0 a : Type}
           {0 lt : a -> a -> Type}
           {0 z,o : a}
           {0 p,m,sub : Op2 a}
           (0 r : OrderedRing a lt z o p m sub)

  ||| Adding a value on the right does not affect an inequality.
  export
  0 plusRight :  {u,v,w : a} -> lt u v -> lt (p u w) (p v w)
  plusRight prf = r.add prf

  ||| Adding a value on the left does not affect an inequality.
  export
  0 plusLeft : {u,v,w : a} -> lt u v -> lt (p w u) (p w v)
  plusLeft {u} {v} {w} prf = CalcSmart {leq = lt} $
    |~ p w u
    ~~ p u w ... r.ring.plus.commutative
    <~ p v w ..> plusRight prf
    ~~ p w v ... r.ring.plus.commutative

  ||| The result of adding a positive value is greater than
  ||| the original.
  export
  0 plusPosRight : {u,v : a} -> lt z v -> lt u (p u v)
  plusPosRight {u} {v} prf = CalcSmart {leq = lt} $
    |~ u
    ~~ p u z ..< r.ring.plus.rightNeutral
    <~ p u v ..> plusLeft prf

  ||| The result of adding a positive value is greater than
  ||| the original.
  export
  0 plusPosLeft : {u,v : a} -> lt z v -> lt u (p v u)
  plusPosLeft {u} {v} prf = CalcSmart {leq = lt} $
    |~ u
    ~~ p z u ..< r.ring.plus.leftNeutral
    <~ p v u ..> plusRight prf

  ||| The result of adding a non-negative value is not less than
  ||| the original.
  export
  0 plusNonNegRight :
       {u,v : a}
    -> ReflexiveClosure lt z u
    -> ReflexiveClosure lt v (p v u)
  plusNonNegRight (Rel l) = Rel $ plusPosRight l
  plusNonNegRight Refl    = fromEq (sym r.ring.plus.rightNeutral)

  ||| The result of adding a non-negative value is not less than
  ||| the original.
  export
  0 plusNonNegLeft :
       {u,v : a}
    -> ReflexiveClosure lt z u
    -> ReflexiveClosure lt v (p u v)
  plusNonNegLeft (Rel l) = Rel $ plusPosLeft l
  plusNonNegLeft Refl    = fromEq (sym r.ring.plus.leftNeutral)

  ||| The result of adding a negative value is less than
  ||| the original.
  export
  0 plusNegRight : {u,v : a} -> lt v z -> lt (p u v) u
  plusNegRight {u} {v} prf = CalcSmart {leq = lt} $
    |~ p u v
    <~ p u z ..> plusLeft prf
    ~~ u     ... r.ring.plus.rightNeutral

  ||| The result of adding a negative value is less than
  ||| the original.
  export
  0 plusNegLeft : {u,v : a} -> lt v z -> lt (p v u) u
  plusNegLeft {u} {v} prf = CalcSmart {leq = lt} $
    |~ p v u
    <~ p z u ..> plusRight prf
    ~~ u     ... r.ring.plus.leftNeutral

  ||| The result of adding a non-positive value is not greater than
  ||| the original.
  export
  0 plusNonPosRight :
       {u,v : a}
    -> ReflexiveClosure lt u z
    -> ReflexiveClosure lt (p v u) v
  plusNonPosRight (Rel l) = Rel $ plusNegRight l
  plusNonPosRight Refl    = fromEq r.ring.plus.rightNeutral

  ||| The result of adding a non-positive value is not greater than
  ||| the original.
  export
  0 plusNonPosLeft :
       {u,v : a}
    -> ReflexiveClosure lt u z
    -> ReflexiveClosure lt (p u v) v
  plusNonPosLeft (Rel l) = Rel $ plusNegLeft l
  plusNonPosLeft Refl    = fromEq r.ring.plus.leftNeutral

  ||| We can solve (in)equalities, where the same value has
  ||| been added on both sides.
  export
  0 solvePlusRight : {u,v,w : a} -> lt (p u w) (p v w) -> lt u v
  solvePlusRight {u} {v} {w} prf = CalcSmart {leq = lt} $
    |~ u
    ~~ p u z               ..< r.ring.plus.rightNeutral
    ~~ p u (sub w w)       ..< cong (p u) r.ring.minusSelf
    ~~ p u (p w (sub z w)) ... cong (p u) r.ring.minusIsPlusRight
    ~~ p (p u w) (sub z w) ... r.ring.plus.associative
    <~ p (p v w) (sub z w) ..> plusRight prf
    ~~ p v (p w (sub z w)) ..< r.ring.plus.associative
    ~~ p v (sub w w)       ..< cong (p v) r.ring.minusIsPlusRight
    ~~ p v z               ... cong (p v) r.ring.minusSelf
    ~~ v                   ... r.ring.plus.rightNeutral
