module Algebra.Group

import Data.List
import Data.List1
import Data.List1.Properties
import Syntax.PreorderReasoning

%default total

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
Associative p = {x,y,z : a} -> (x `p` (y `p` z)) === ((x `p` y) `p` z)

||| Proposition that the given binary operation is commutative.
public export
0 Commutative : Op2 a -> Type
Commutative p = {x,y : a} -> (x `p` y) === (y `p` x)

||| Proposition that `n` is a left neutral element for the
||| given binary operation.
public export
0 LeftNeutral : (n : a) -> Op2 a -> Type
LeftNeutral n p = {x : a} -> (n `p` x) === x

||| Proposition that `n` is a right neutral element for the
||| given binary operation.
public export
0 RightNeutral : (n : a) -> Op2 a -> Type
RightNeutral n p = {x : a} -> (x `p` n) === x

||| Proposition that `i` is the left inverse of the given binary operation.
public export
0 LeftInverse : (n : a) -> (i : Op1 a) -> Op2 a -> Type
LeftInverse n i p = {x : a} -> (i x `p` x) === n

||| Proposition that `i` is the right inverse of the given binary operation.
public export
0 RightInverse : (n : a) -> (i : Op1 a) -> Op2 a -> Type
RightInverse n i p = {x : a} -> (x `p` i x) === n

--------------------------------------------------------------------------------
--          Lemmata
--------------------------------------------------------------------------------

||| For a commutative operation, the left neutral element is also a
||| right neutral element
export
rightNeutral : LeftNeutral n p -> Commutative p -> RightNeutral n p
rightNeutral ln com = Calc $
  |~ p x n
  ~~ p n x ... com
  ~~ x     ... ln

||| For a commutative operation, the right neutral element is also a
||| left neutral element
export
leftNeutral : RightNeutral n p -> Commutative p -> LeftNeutral n p
leftNeutral rn com = Calc $
  |~ p n x
  ~~ p x n ... com
  ~~ x     ... rn

||| For a commutative operation, the left inverse is also a right inverse.
export
rightInverse : LeftInverse n i p -> Commutative p -> RightInverse n i p
rightInverse li com = Calc $
  |~ p x (i x)
  ~~ p (i x) x ... com
  ~~ n         ... li

||| For a commutative operation, the right inverse is also a left inverse.
export
leftInverse : RightInverse n i p -> Commutative p -> LeftInverse n i p
leftInverse ri com = Calc $
  |~ p (i x) x
  ~~ p x (i x) ... com
  ~~ n         ... ri

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
||| neutral element `n` for that operation.
public export
record Monoid (a : Type) (n : a) (p : Op2 a) where
  constructor MkMonoid
  associative  : Associative p
  rightNeutral : RightNeutral n p
  leftNeutral  : LeftNeutral n p

namespace Monoid

  ||| A monoid is also a semigroup
  export
  (.sgrp) : Monoid a n p -> Semigroup a p
  m.sgrp = MkSemigroup m.associative

||| Like `Monoid` but with a binary operation that is also commutative.
public export
record CommutativeMonoid (a : Type) (n : a) (p : Op2 a) where
  constructor MkCommutativeMonoid
  associative : Associative p
  commutative : Commutative p
  leftNeutral : LeftNeutral n p

namespace CommutativeMonoid

  ||| A commutative monoid is also a semigroup
  export
  (.sgrp) : CommutativeMonoid a n p -> Semigroup a p
  m.sgrp = MkSemigroup m.associative

  ||| A commutative monoid is also a semigroup
  export
  (.csgrp) : CommutativeMonoid a n p -> CommutativeSemigroup a p
  m.csgrp = MkCommutativeSemigroup m.associative m.commutative

  ||| For a commutative monoid, `n` is a right neutral element.
  export
  (.rightNeutral) : CommutativeMonoid a n p -> RightNeutral n p
  m.rightNeutral = rightNeutral {p} m.leftNeutral m.commutative

  ||| A commutative monoid is also a monoid
  export
  (.mon) : CommutativeMonoid a n p -> Monoid a n p
  m.mon = MkMonoid m.associative m.rightNeutral m.leftNeutral

--------------------------------------------------------------------------------
--          Group
--------------------------------------------------------------------------------

||| A `Group` is a monoid with an inverse operation.
public export
record Group (a : Type) (n : a) (i : Op1 a) (p : Op2 a) where
  constructor MkGroup
  associative  : Associative p
  leftNeutral  : LeftNeutral n p
  rightNeutral : RightNeutral n p
  leftInverse  : LeftInverse n i p
  rightInverse : RightInverse n i p

namespace Group

  ||| A group is also a semigroup
  export
  (.sgrp) : Group a n i p -> Semigroup a p
  g.sgrp = MkSemigroup g.associative

  ||| A group is also a monoid
  export
  (.mon) : Group a n i p -> Monoid a n p
  g.mon = MkMonoid g.associative g.rightNeutral g.leftNeutral

||| An abelian group is a group with a commutative binary operation.
public export
record AbelianGroup (a : Type) (n : a) (i : Op1 a) (p : Op2 a) where
  constructor MkAbelianGroup
  associative  : Associative p
  commutative  : Commutative p
  leftNeutral  : LeftNeutral n p
  leftInverse  : LeftInverse n i p

namespace AbelianGroup

  ||| An abelian group is also a semigroup
  export
  (.sgrp) : AbelianGroup a n i p -> Semigroup a p
  g.sgrp = MkSemigroup g.associative

  ||| An abelian group is also a commutative monoid
  export
  (.cmon) : AbelianGroup a n i p -> CommutativeMonoid a n p
  g.cmon = MkCommutativeMonoid g.associative g.commutative g.leftNeutral

  ||| An abelian group is also a commutative semigroup
  export
  (.csgrp) : AbelianGroup a n i p -> CommutativeSemigroup a p
  g.csgrp = g.cmon.csgrp

  ||| For an abelian group, `n` is a right neutral element.
  export
  (.rightNeutral) : AbelianGroup a n i p -> RightNeutral n p
  g.rightNeutral = g.cmon.rightNeutral

  ||| For an abelian group, `i` is a right inverse.
  export
  (.rightInverse) : AbelianGroup a n i p -> RightInverse n i p
  g.rightInverse = rightInverse {p} g.leftInverse g.commutative

  ||| An abelian group is also a monoid
  export
  (.mon) : AbelianGroup a n i p -> Monoid a n p
  g.mon = g.cmon.mon

  ||| An abelian group is also a group
  export
  (.grp) : AbelianGroup a n i p -> Group a n i p
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
  appendAssoc {x = Just vx} = Refl
  appendAssoc {x = Nothing} = Refl

  export
  0 appendRightNeutral : RightNeutral Nothing ((<+>) {ty = Maybe a})
  appendRightNeutral {x = Just _}  = Refl
  appendRightNeutral {x = Nothing} = Refl

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
union p (Just x) Nothing  = Just x
union p (Just x) (Just y) = Just $ p x y

namespace Union
  export
  0 unionAssoc : Associative p -> Associative (union p)
  unionAssoc {x=Nothing}                         s = Refl
  unionAssoc {x=Just u}  {y=Nothing}             s = Refl
  unionAssoc {x=Just u}  {y=Just v}  {z=Nothing} s = Refl
  unionAssoc {x=Just u}  {y=Just v}  {z=Just w}  s = cong Just s

  export
  0 unionCommutative : Commutative p -> Commutative (union p)
  unionCommutative {x=Nothing} {y=Nothing} _ = Refl
  unionCommutative {x=Nothing} {y=Just v}  _ = Refl
  unionCommutative {x=Just u}  {y=Nothing} _ = Refl
  unionCommutative {x=Just u}  {y=Just v}  s = cong Just s

  export
  0 unionRightNeutral : RightNeutral Nothing (union p)
  unionRightNeutral {x = Just _}  = Refl
  unionRightNeutral {x = Nothing} = Refl

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
  appendAssoc {x = EQ} = Refl
  appendAssoc {x = LT} = Refl
  appendAssoc {x = GT} = Refl

  export
  0 appendRightNeutral : RightNeutral EQ ((<+>) {ty = Ordering})
  appendRightNeutral {x = EQ} = Refl
  appendRightNeutral {x = LT} = Refl
  appendRightNeutral {x = GT} = Refl

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
  appendLeftNeutral {x = ()} = Refl

||| The default group for `Unit` provided by the prelude.
export
0 agrp_unit : AbelianGroup Unit MkUnit Unit.neg (<+>)
agrp_unit = MkAbelianGroup Refl Refl appendLeftNeutral Refl
