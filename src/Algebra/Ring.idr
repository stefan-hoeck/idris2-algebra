module Algebra.Ring

import Algebra.Group
import Data.Nat
import Syntax.PreorderReasoning

||| Proposition that multiplication distributes over addition
public export
0 LeftDistributive : (p,m : Op2 a) -> Type
LeftDistributive p m = {u,v,w : a} -> u `m` (v `p` w) === (u `m` v) `p` (u `m` w)

||| Proposition that multiplication by zero returns zero
public export
0 MultZeroLeftAbsorbs : (z : a) -> (m : Op2 a) -> Type
MultZeroLeftAbsorbs z m = {n : a} -> z `m` n === z

||| Proposition that subtraction is associative with addition.
public export
0 MinusAssociative : (p,sub : Op2 a) -> Type
MinusAssociative p sub = {u,v,w : a} -> u `p` (v `sub` w) === (u `p` v) `sub` w

||| Proposition that subtraction from zero is a left inverse.
public export
0 ZeroMinus : (z : a) -> (p,sub : Op2 a) -> Type
ZeroMinus z p sub = {u : a} -> (z `sub` u) `p` u === z

--------------------------------------------------------------------------------
--          Rig
--------------------------------------------------------------------------------

public export
record Rig (a : Type) (z,o : a) (p,m : Op2 a) where
  constructor MkRig
  plus                : CommutativeMonoid a z p
  mult                : CommutativeMonoid a o m
  leftDistributive    : LeftDistributive p m
  multZeroLeftAbsorbs : MultZeroLeftAbsorbs z m

namespace Rig
  ||| Zero is an absorbing element of multiplication.
  export
  0 (.multZeroRightAbsorbs) : Rig a z o p m -> {x : a} -> x `m` z === z
  r.multZeroRightAbsorbs =
    Calc $
      |~ x `m` z
      ~~ z `m` x ... r.mult.commutative
      ~~ z       ... r.multZeroLeftAbsorbs

  ||| Multiplication is distributive with respect to addition.
  export
  0 (.rightDistributive) :
       Rig a z o p m
    -> {x,y,v : a}
    -> (y `p` v) `m` x === y `m` x `p` v `m` x
  r.rightDistributive =
    Calc $
      |~ (y `p` v) `m` x
      ~~ x `m` (y `p` v)         ... r.mult.commutative
      ~~ (x `m` y) `p` (x `m` v) ... r.leftDistributive
      ~~ y `m` x `p` x `m` v     ... cong (`p` x `m` v) r.mult.commutative
      ~~ y `m` x `p` v `m` x     ... cong (y `m` x `p`) r.mult.commutative

||| Zero is an absorbing element of multiplication.
export
multZeroAbsorbs :
     Rig a z o p m
  -> {x,y : a}
  -> Either (x === z) (y === z)
  -> x `m` y === z
multZeroAbsorbs r (Left rfl) =
  Calc $
    |~ x `m` y
    ~~ z `m` y ... cong (`m` y) rfl
    ~~ z       ... r.multZeroLeftAbsorbs
multZeroAbsorbs r (Right rfl) =
  Calc $
    |~ x `m` y
    ~~ x `m` z ... cong (x `m`) rfl
    ~~ z       ... r.multZeroRightAbsorbs

export
0 NatRig : Rig Nat 0 1 (+) (*)
NatRig =
  MkRig cmon_nat_plus cmon_nat_mult (multDistributesOverPlusRight  _ _ _) Refl

--------------------------------------------------------------------------------
--          Ring
--------------------------------------------------------------------------------

public export
record Ring (a : Type) (z,o : a) (p,m,sub : Op2 a) where
  constructor MkRing
  plusMon          : CommutativeMonoid a z p
  mult             : CommutativeMonoid a o m
  leftDistributive : LeftDistributive p m
  minusAssociative : MinusAssociative p sub
  zeroMinus        : ZeroMinus z p sub


namespace Ring
  export
  0 (.plus) : Ring a z o p m sub -> AbelianGroup a z (z `sub`) p
  (.plus) (MkRing (MkCommutativeMonoid a c l) _ _ _ zm) =
    MkAbelianGroup a c l zm

  export
  0 (.multZeroRightAbsorbs) : Ring a z o p m sub -> {x : a} -> x `m` z === z
  r.multZeroRightAbsorbs =
    leftInjective r.plus.grp $ Calc $
      |~ (x `m` z) `p` (x `m` z)
      ~~ x `m` (z `p` z)         ..< r.leftDistributive {u = x, v = z, w = z}
      ~~ x `m` z                 ... cong (x `m`) r.plus.leftNeutral
      ~~ (x `m` z) `p` z         ..< r.plus.rightNeutral

  export
  0 (.multZeroLeftAbsorbs) : Ring a z o p m sub -> {x : a} -> z `m` x === z
  r.multZeroLeftAbsorbs = Calc $
    |~ z `m` x
    ~~ x `m` z ... r.mult.commutative
    ~~ z       ... r.multZeroRightAbsorbs

  export
  0 (.rig) : Ring a z o p m sub -> Rig a z o p m
  (.rig) r@(MkRing pm mult ld _ _) = MkRig pm mult ld r.multZeroLeftAbsorbs

  export
  0 (.minusSelf) : Ring a z o p m sub -> {x : a} -> x `sub` x === z
  r.minusSelf = Calc $
    |~ x `sub`x
    ~~ (x `p` z) `sub` x ..< cong (`sub` x) r.plus.rightNeutral
    ~~ x `p` (z `sub` x) ..< r.minusAssociative
    ~~ z                 ... r.plus.rightInverse

  export
  0 (.minusIsPlusRight) :
        Ring a z o p m sub
    -> {x,y : a}
    -> x `sub` y === x `p` (z `sub` y)
  r.minusIsPlusRight = Calc $
    |~ x `sub` y
    ~~ (x `p` z) `sub` y ..< cong (`sub` y) r.plus.rightNeutral
    ~~ x `p` (z `sub` y) ..< r.minusAssociative

  export
  0 (.minusIsPlusLeft) :
        Ring a z o p m sub
    -> {x,y : a}
    -> x `sub` y === (z `sub` y) `p` x
  r.minusIsPlusLeft = Calc $
    |~ x `sub` y
    ~~ x `p` (z `sub` y) ... r.minusIsPlusRight
    ~~ (z `sub` y) `p` x ... r.plus.commutative

  export
  0 (.multNegRight) :
       Ring a z o p m sub
    -> {x,y : a}
    -> x `m` (z `sub` y) === z `sub` (x `m` y)
  r.multNegRight =
    solveInverseLeft r.plus.grp $ Calc $
      |~ (x `m` y) `p` (x `m` (z `sub` y))
      ~~ x `m` ( y `p` (z `sub` y)) ..< r.leftDistributive
      ~~ x `m` z                    ... cong (x `m`) r.plus.rightInverse
      ~~ z                          ... r.multZeroRightAbsorbs

  export
  0 (.negMultNegRight) :
       Ring a z o p m sub
    -> {x,y : a}
    -> z `sub` (x `m` (z `sub` y)) === x `m` y
  r.negMultNegRight = Calc $
    |~ z `sub` (x `m` (z `sub` y))
    ~~ z `sub` (z `sub` (x `m` y))  ... cong (z `sub`) r.multNegRight
    ~~ x `m` y                      ... inverseInvolutory r.plus.grp

  export
  0 (.multNegLeft) :
       Ring a z o p m sub
    -> {x,y : a}
    -> (z `sub` x) `m` y === z `sub` (x `m` y)
  r.multNegLeft = Calc $
    |~ (z `sub` x) `m` y
    ~~ y `m` (z `sub` x) ... r.mult.commutative
    ~~ z `sub` (y `m` x) ... r.multNegRight
    ~~ z `sub` (x `m` y) ... cong (z `sub`) r.mult.commutative

  export
  0 (.negMultNegLeft) :
       Ring a z o p m sub
    -> {x,y : a}
    -> z `sub` ((z `sub` x) `m` y) === x `m` y
  r.negMultNegLeft = Calc $
    |~ z `sub` ((z `sub` x) `m` y)
    ~~ z `sub` (z `sub` (x `m` y))  ... cong (z `sub`) r.multNegLeft
    ~~ x `m` y                      ... inverseInvolutory r.plus.grp

  export
  0 (.multMinusOneRight) :
       Ring a z o p m sub
    -> {x : a}
    -> x `m` (z `sub` o) === z `sub` x
  r.multMinusOneRight = Calc $
    |~ x `m` (z `sub` o)
    ~~ z `sub` x `m` o  ... r.multNegRight
    ~~ z `sub` x        ... cong (z `sub`) r.mult.rightNeutral

  export
  0 (.multMinusOneLeft) :
       Ring a z o p m sub
    -> {x : a}
    -> (z `sub` o) `m` x === z `sub` x
  r.multMinusOneLeft = Calc $
    |~ (z `sub` o) `m` x
    ~~ x `m` (z `sub` o) ... r.mult.commutative
    ~~ z `sub` x         ... r.multMinusOneRight

  export
  0 (.negMultNeg) :
       Ring a z o p m sub
    -> {x,y : a}
    -> (z `sub` x) `m` (z `sub` y) === x `m` y
  r.negMultNeg = Calc $
    |~ (z `sub` x) `m` (z `sub` y)
    ~~ z `sub` (x `m` (z `sub` y)) ... r.multNegLeft
    ~~ z `sub` (z `sub` (x `m` y)) ... cong (z `sub`) r.multNegRight
    ~~ x `m` y                     ... inverseInvolutory r.plus.grp
