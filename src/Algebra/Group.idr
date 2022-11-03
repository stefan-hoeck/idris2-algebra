module Algebra.Group

import Data.List
import Data.List1
import Data.List1.Properties
import Syntax.PreorderReasoning

%default total

--------------------------------------------------------------------------------
--          "Operators"
--------------------------------------------------------------------------------

infixl 8 `p`

infixl 9 `m`

--------------------------------------------------------------------------------
--          Laws
--------------------------------------------------------------------------------

||| A unary operation on a type, for instance `negate`.
public export
0 Op1 : Type -> Type
Op1 a = a -> a

||| A binary operation on a type, for instance `(+)`.
public export
0 Op2 : Type -> Type
Op2 a = a -> a -> a

||| Proposition that the given binary operation is associative.
public export
0 Associative : Op2 a -> Type
Associative p = {u,v,w : a} -> u `p` (v `p` w) === (u `p` v) `p` w

||| Proposition that the given binary operation is commutative.
public export
0 Commutative : Op2 a -> Type
Commutative p = {u,v : a} -> u `p` v === v `p` u

||| Proposition that `z` is a left neutral element for the
||| given binary operation.
public export
0 LeftNeutral : (z : a) -> Op2 a -> Type
LeftNeutral z p = {u : a} -> z `p` u === u

||| Proposition that `z` is a right neutral element for the
||| given binary operation.
public export
0 RightNeutral : (z : a) -> Op2 a -> Type
RightNeutral z p = {u : a} -> u `p` z === u

||| Proposition that `i` is the left inverse of the given binary operation.
public export
0 LeftInverse : (z : a) -> (i : Op1 a) -> Op2 a -> Type
LeftInverse z i p = {u : a} -> i u `p` u === z

||| Proposition that `i` is the right inverse of the given binary operation.
public export
0 RightInverse : (z : a) -> (i : Op1 a) -> Op2 a -> Type
RightInverse z i p = {u : a} -> u `p` i u === z

--------------------------------------------------------------------------------
--          Lemmata
--------------------------------------------------------------------------------

||| For a commutative operation, the left neutral element is also a
||| right neutral element
export
rightNeutral : LeftNeutral z p -> Commutative p -> RightNeutral z p
rightNeutral ln com = Calc $
  |~ p u z
  ~~ p z u ... com
  ~~ u     ... ln

||| For a commutative operation, the right neutral element is also a
||| left neutral element
export
leftNeutral : RightNeutral z p -> Commutative p -> LeftNeutral z p
leftNeutral rn com = Calc $
  |~ z `p` u
  ~~ u `p` z ... com
  ~~ u       ... rn

||| For a commutative operation, the left inverse is also a right inverse.
export
rightInverse : LeftInverse z i p -> Commutative p -> RightInverse z i p
rightInverse li com = Calc $
  |~ u `p` (i u)
  ~~ (i u) `p` u ... com
  ~~ z           ... li

||| For a commutative operation, the right inverse is also a left inverse.
export
leftInverse : RightInverse z i p -> Commutative p -> LeftInverse z i p
leftInverse ri com = Calc $
  |~ (i u) `p` u
  ~~ u `p` (i u) ... com
  ~~ z           ... ri

--------------------------------------------------------------------------------
--          Semigroup
--------------------------------------------------------------------------------

||| A `Semigroup` is a set with a binary associative operation.
public export
record Semigroup (a : Type) (p : Op2 a) where
  constructor MkSemigroup
  associative : Associative p

||| Like a semigroup but the binary operation is also commutative.
public export
record CommutativeSemigroup (a : Type) (p : Op2 a) where
  constructor MkCommutativeSemigroup
  associative : Associative p
  commutative : Commutative p

namespace CommutativeSemigroup

  ||| A commutative semigroup is also a semigroup.
  export
  (.sgrp) : CommutativeSemigroup a p -> Semigroup a p
  c.sgrp = MkSemigroup c.associative

--------------------------------------------------------------------------------
--          Monoid
--------------------------------------------------------------------------------

||| A `Monoid` is a set with a binary associative operation and a
||| neutral element `z` for that operation.
public export
record Monoid (a : Type) (z : a) (p : Op2 a) where
  constructor MkMonoid
  associative  : Associative p
  rightNeutral : RightNeutral z p
  leftNeutral  : LeftNeutral z p

namespace Monoid

  ||| A monoid is also a semigroup
  export
  (.sgrp) : Monoid a z p -> Semigroup a p
  m.sgrp = MkSemigroup m.associative

||| Like `Monoid` but with a binary operation that is also commutative.
public export
record CommutativeMonoid (a : Type) (z : a) (p : Op2 a) where
  constructor MkCommutativeMonoid
  associative : Associative p
  commutative : Commutative p
  leftNeutral : LeftNeutral z p

namespace CommutativeMonoid

  ||| A commutative monoid is also a semigroup
  export
  (.sgrp) : CommutativeMonoid a z p -> Semigroup a p
  m.sgrp = MkSemigroup m.associative

  ||| A commutative monoid is also a semigroup
  export
  (.csgrp) : CommutativeMonoid a z p -> CommutativeSemigroup a p
  m.csgrp = MkCommutativeSemigroup m.associative m.commutative

  ||| For a commutative monoid, `z` is a right neutral element.
  export
  (.rightNeutral) : CommutativeMonoid a z p -> RightNeutral z p
  m.rightNeutral = rightNeutral {p} m.leftNeutral m.commutative

  ||| A commutative monoid is also a monoid
  export
  (.mon) : CommutativeMonoid a z p -> Monoid a z p
  m.mon = MkMonoid m.associative m.rightNeutral m.leftNeutral

--------------------------------------------------------------------------------
--          Group
--------------------------------------------------------------------------------

||| A `Group` is a monoid with an inverse operation.
public export
record Group (a : Type) (z : a) (i : Op1 a) (p : Op2 a) where
  constructor MkGroup
  associative  : Associative p
  leftNeutral  : LeftNeutral z p
  rightNeutral : RightNeutral z p
  leftInverse  : LeftInverse z i p
  rightInverse : RightInverse z i p

||| In a group, the binary operation is injective when applied
||| from the left.
export
0 leftInjective :
     Group a z i p
  -> {u,v,w : a}
  -> u `p` v === u `p` w
  -> v === w
leftInjective g prf = Calc $
  |~ v
  ~~ z `p` v           ..< g.leftNeutral
  ~~ (i u `p` u) `p` v ..< cong (`p` v) g.leftInverse
  ~~ i u `p` (u `p` v) ..< g.associative
  ~~ i u `p` (u `p` w) ... cong (i u `p`) prf
  ~~ (i u `p` u) `p` w ... g.associative
  ~~ z `p` w           ... cong (`p` w) g.leftInverse
  ~~ w                 ... g.leftNeutral

||| In a group, from `p v u === z` follows `u === i v`.
export
0 solveInverseLeft :
     Group a z i p
  -> {u,v : a}
  -> v `p` u === z
  -> u === i v
solveInverseLeft g prf = leftInjective g $ Calc $
  |~ v `p` u
  ~~ z         ... prf
  ~~ v `p` i v ..< g.rightInverse

||| In a group, the inverse of a product is the product of inverses
||| (in reverse order).
export
0 invertProduct :
     Group a z i p
  -> {u,v : a}
  -> i (u `p` v) === i v `p` i u
invertProduct g = sym $ solveInverseLeft g $ Calc $
  |~ (u `p` v) `p` (i v `p` i u)
  ~~ u `p` (v `p` (i v `p` i u)) ..< g.associative
  ~~ u `p` ((v `p` i v) `p` i u) ... cong (u `p`) g.associative
  ~~ u `p` (z `p` i u)           ... cong (\q => u `p` (q `p` i u)) g.rightInverse
  ~~ u `p` i u                   ... cong (u `p`) g.leftNeutral
  ~~ z                           ... g.rightInverse

||| In a group, the binary operation is injective when applied
||| from the right.
export
0 rightInjective :
     Group a z i p
  -> {u,v,w : a}
  -> v `p` u === w `p` u
  -> v === w
rightInjective g prf = Calc $
  |~ v
  ~~ v `p` z           ..< g.rightNeutral
  ~~ v `p` (u `p` i u) ..< cong (p v) g.rightInverse
  ~~ (v `p` u) `p` i u ... g.associative
  ~~ (w `p` u) `p` i u ... cong (`p` i u) prf
  ~~ w `p` (u `p` i u) ..< g.associative
  ~~ w `p` z           ... cong (w `p`) g.rightInverse
  ~~ w                 ... g.rightNeutral

||| In a group, from `p u v === z` follows `u === i v`.
export
0 solveInverseRight :
     Group a z i p
  -> {u,v : a}
  -> u `p` v === z
  -> u === i v
solveInverseRight g prf = rightInjective g $ Calc $
  |~ u `p` v
  ~~ z         ... prf
  ~~ i v `p` v ..< g.leftInverse

||| In a group, the inverse of the neutral element is
||| the neutral element itself.
export
0 inverseZero : Group a z i p -> i z === z
inverseZero g = sym $ solveInverseRight g $ g.rightNeutral

||| In a group, inverting an value twice yields the original value.
export
0 inverseInverse : Group a z i p -> {u : a} -> i (i u) === u
inverseInverse g = sym $ solveInverseRight g g.rightInverse

namespace Group

  ||| A group is also a semigroup
  export
  (.sgrp) : Group a z i p -> Semigroup a p
  g.sgrp = MkSemigroup g.associative

  ||| A group is also a monoid
  export
  (.mon) : Group a z i p -> Monoid a z p
  g.mon = MkMonoid g.associative g.rightNeutral g.leftNeutral

||| An abelian group is a group with a commutative binary operation.
public export
record AbelianGroup (a : Type) (z : a) (i : Op1 a) (p : Op2 a) where
  constructor MkAbelianGroup
  associative  : Associative p
  commutative  : Commutative p
  leftNeutral  : LeftNeutral z p
  leftInverse  : LeftInverse z i p

namespace AbelianGroup

  ||| An abelian group is also a semigroup
  export
  (.sgrp) : AbelianGroup a z i p -> Semigroup a p
  g.sgrp = MkSemigroup g.associative

  ||| An abelian group is also a commutative monoid
  export
  (.cmon) : AbelianGroup a z i p -> CommutativeMonoid a z p
  g.cmon = MkCommutativeMonoid g.associative g.commutative g.leftNeutral

  ||| An abelian group is also a commutative semigroup
  export
  (.csgrp) : AbelianGroup a z i p -> CommutativeSemigroup a p
  g.csgrp = g.cmon.csgrp

  ||| For an abelian group, `z` is a right neutral element.
  export
  (.rightNeutral) : AbelianGroup a z i p -> RightNeutral z p
  g.rightNeutral = g.cmon.rightNeutral

  ||| For an abelian group, `i` is a right inverse.
  export
  (.rightInverse) : AbelianGroup a z i p -> RightInverse z i p
  g.rightInverse = rightInverse {p} g.leftInverse g.commutative

  ||| An abelian group is also a monoid
  export
  (.mon) : AbelianGroup a z i p -> Monoid a z p
  g.mon = g.cmon.mon

  ||| An abelian group is also a group
  export
  (.grp) : AbelianGroup a z i p -> Group a z i p
  g.grp =
    MkGroup
      g.associative
      g.leftNeutral
      g.rightNeutral
      g.leftInverse
      g.rightInverse

--------------------------------------------------------------------------------
--          List1
--------------------------------------------------------------------------------

export
0 sgrp_list1 : Semigroup (List1 a) (++)
sgrp_list1 = MkSemigroup (appendAssociative _ _ _)

--------------------------------------------------------------------------------
--          List
--------------------------------------------------------------------------------

export
0 mon_list : Monoid (List a) [] (++)
mon_list = MkMonoid (appendAssociative _ _ _) (appendNilRightNeutral _) Refl

--------------------------------------------------------------------------------
--          Maybe
--------------------------------------------------------------------------------

namespace Maybe
  export
  0 appendAssoc : Associative ((<+>) {ty = Maybe a})
  appendAssoc {u = Just vx} = Refl
  appendAssoc {u = Nothing} = Refl

  export
  0 appendRightNeutral : RightNeutral Nothing ((<+>) {ty = Maybe a})
  appendRightNeutral {u = Just _}  = Refl
  appendRightNeutral {u = Nothing} = Refl

||| The default monoid for `Maybe` provided by the prelude:
||| Returns the first non-empty value (if any).
export
0 mon_maybe : Monoid (Maybe a) Nothing (<+>)
mon_maybe = MkMonoid appendAssoc appendRightNeutral Refl

||| Use a binary function to combine two `Maybe`s in case both
||| are `Just`s.
|||
||| This is an associative function, if `p` is associative. It is
||| commutative if `p` is commutative.
public export
union : (p : a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
union p Nothing  m        = m
union p (Just u) Nothing  = Just u
union p (Just u) (Just v) = Just $ p u v

namespace Union
  export
  0 unionAssoc : Associative p -> Associative (union p)
  unionAssoc {u=Nothing}                         s = Refl
  unionAssoc {u=Just u}  {v=Nothing}             s = Refl
  unionAssoc {u=Just u}  {v=Just v}  {w=Nothing} s = Refl
  unionAssoc {u=Just u}  {v=Just v}  {w=Just w}  s = cong Just s

  export
  0 unionCommutative : Commutative p -> Commutative (union p)
  unionCommutative {u=Nothing} {v=Nothing} _ = Refl
  unionCommutative {u=Nothing} {v=Just v}  _ = Refl
  unionCommutative {u=Just u}  {v=Nothing} _ = Refl
  unionCommutative {u=Just u}  {v=Just v}  s = cong Just s

  export
  0 unionRightNeutral : RightNeutral Nothing (union p)
  unionRightNeutral {u = Just _}  = Refl
  unionRightNeutral {u = Nothing} = Refl

export
0 mon_union : Associative p -> Monoid (Maybe a) Nothing (union p)
mon_union ap = MkMonoid (unionAssoc ap) unionRightNeutral Refl

export
0 cmon_union :
     CommutativeSemigroup a p
  -> CommutativeMonoid (Maybe a) Nothing (union p)
cmon_union s =
  MkCommutativeMonoid
    (mon_union s.associative).associative
    (unionCommutative s.commutative)
    Refl

--------------------------------------------------------------------------------
--          Ordering
--------------------------------------------------------------------------------

namespace Ordering
  export
  0 appendAssoc : Associative ((<+>) {ty = Ordering})
  appendAssoc {u = EQ} = Refl
  appendAssoc {u = LT} = Refl
  appendAssoc {u = GT} = Refl

  export
  0 appendRightNeutral : RightNeutral EQ ((<+>) {ty = Ordering})
  appendRightNeutral {u = EQ} = Refl
  appendRightNeutral {u = LT} = Refl
  appendRightNeutral {u = GT} = Refl

||| The default monoid for `Ordering` provided by the prelude:
||| Returns the first non-`EQ` value (if any).
export
0 mon_ordering : Monoid Ordering EQ (<+>)
mon_ordering = MkMonoid appendAssoc appendRightNeutral Refl

--------------------------------------------------------------------------------
--          Unit
--------------------------------------------------------------------------------

namespace Unit
  export
  neg : () -> ()
  neg _ = ()

  export
  0 appendLeftNeutral : LeftNeutral MkUnit ((<+>) {ty = Unit})
  appendLeftNeutral {u = ()} = Refl

||| The default group for `Unit` provided by the prelude.
export
0 agrp_unit : AbelianGroup Unit MkUnit Unit.neg (<+>)
agrp_unit = MkAbelianGroup Refl Refl appendLeftNeutral Refl
