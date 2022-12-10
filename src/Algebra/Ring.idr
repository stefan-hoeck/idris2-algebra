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

||| Zero is an absorbing element of multiplication.
export
0 multZeroRightAbsorbs : Rig a z o p m -> {x : a} -> x `m` z === z
multZeroRightAbsorbs r =
  Calc $
    |~ x `m` z
    ~~ z `m` x ... r.mult.commutative
    ~~ z       ... r.multZeroLeftAbsorbs

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
    ~~ z       ... multZeroLeftAbsorbs r
multZeroAbsorbs r (Right rfl) =
  Calc $
    |~ x `m` y
    ~~ x `m` z ... cong (x `m`) rfl
    ~~ z       ... multZeroRightAbsorbs r

||| Multiplication is distributive with respect to addition.
export
0 rightDistributive :
     Rig a z o p m
  -> {x,y,v : a}
  -> (y `p` v) `m` x === y `m` x `p` v `m` x
rightDistributive r =
  Calc $
    |~ (y `p` v) `m` x
    ~~ x `m` (y `p` v)         ... r.mult.commutative
    ~~ (x `m` y) `p` (x `m` v) ... r.leftDistributive
    ~~ y `m` x `p` x `m` v     ... cong (`p` x `m` v) r.mult.commutative
    ~~ y `m` x `p` v `m` x     ... cong (y `m` x `p`) r.mult.commutative

export
0 rig_nat : Rig Nat 0 1 (+) (*)
rig_nat =
  MkRig cmon_nat_plus cmon_nat_mult (multDistributesOverPlusRight  _ _ _) Refl

--------------------------------------------------------------------------------
--          Ring
--------------------------------------------------------------------------------

public export
record Ring (a : Type) (o,z : a) (i : Op1 a) (p,m : Op2 a) where
  constructor MkRing
  plus                : AbelianGroup a o i p
  mult                : CommutativeMonoid a z m
  leftDistributive    : LeftDistributive p m

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

||| Zero is an absorbing element of multiplication.
0 rmultZeroRightAbsorbs : Ring a z o i p m -> {x : a} -> x `m` z === z
rmultZeroRightAbsorbs r =
  leftInjective r.plus.grp $ Calc $
    |~ (x `m` z) `p` (x `m` z)
    ~~ x `m` (z `p` z)         ..< r.leftDistributive {u = x, v = z, w = z}
    ~~ x `m` z                 ... cong (x `m`) r.plus.leftNeutral
    ~~ (x `m` z) `p` z         ..< r.plus.rightNeutral

0 rmultZeroLeftAbsorbs : Ring a z o i p m -> {x : a} -> z `m` x === z

namespace Ring
  export
  0 (.rig) : Ring a z o i p m -> Rig a z o p m
  (.rig) r@(MkRing pl mu ld) = MkRig pl.cmon mu ld (rmultZeroLeftAbsorbs r)

||| `m * (-n) = - (m * n)`.
export
0 multNegRight :
     Ring a z o i p m
  -> {x,y : a} -> x `m` i y === i (x `m` y)
multNegRight r =
  solveInverseLeft r.plus.grp $ Calc $
    |~ x `m` y `p` x `m` i y
    ~~ x `m` (y `p` i y)   ..< r.leftDistributive
    ~~ x `m` z             ... cong (x `m`) r.plus.grp.rightInverse
    ~~ z                   ... multZeroRightAbsorbs r.rig

-- ||| `- (m * (-n)) = m * n`.
-- export
-- 0 negMultNegRight : Ring a => {m,n : a} -> neg (m * neg n) === m * n
-- negMultNegRight =
--   Calc $
--     |~ neg (m * neg n)
--     ~~ neg (neg (m * n)) ... cong neg multNegRight
--     ~~ m * n             ... negInvolutory
--
-- ||| `(- m) * n = - (m * n)`.
-- export
-- 0 multNegLeft : Ring a => {m,n : a} -> neg m * n === neg (m * n)
-- multNegLeft =
--   Calc $
--     |~ neg m * n
--     ~~ n * neg m   ... multCommutative
--     ~~ neg (n * m) ... multNegRight
--     ~~ neg (m * n) ... cong neg multCommutative
--
-- ||| `- ((-m) * n) = m * n`.
-- export
-- 0 negMultNegLeft : Ring a => {m,n : a} -> neg (neg m * n) === m * n
-- negMultNegLeft =
--   Calc $
--     |~ neg (neg m * n)
--     ~~ neg (neg (m * n)) ... cong neg multNegLeft
--     ~~ m * n             ... negInvolutory
--
-- ||| Multiplication with `(-1)` is negation.
-- export
-- 0 multMinusOneRight : Ring a => {n : a} -> n * neg 1 === neg n
-- multMinusOneRight =
--   Calc $
--     |~ n * neg 1
--     ~~ neg (n * 1) ... multNegRight
--     ~~ neg n       ... cong neg multOneRightNeutral
--
-- ||| Multiplication with `(-1)` is negation.
-- export
-- 0 multMinusOneLeft : Ring a => {n : a} -> neg 1 * n === neg n
-- multMinusOneLeft =
--   Calc $
--     |~ neg 1 * n
--     ~~ neg (1 * n) ... multNegLeft
--     ~~ neg n       ... cong neg multOneLeftNeutral
--
-- ||| Multiplication of two negations removes negations.
-- export
-- 0 negMultNeg : Ring a => {m,n : a} -> neg m * neg n === m * n
-- negMultNeg =
--   Calc $
--     |~ neg m * neg n
--     ~~ neg (m * neg n)   ... multNegLeft
--     ~~ neg (neg (m * n)) ... cong neg multNegRight
--     ~~ m * n             ... negInvolutory
--
-- ||| Multiplication is distributive with respect to addition.
-- export
-- 0 rightDistributive :  Ring a
--                     => {k,m,n : a}
--                     -> (m + n) * k === m * k + n * k
-- rightDistributive =
--   Calc $
--     |~ (m + n) * k
--     ~~ k * (m + n)       ... multCommutative
--     ~~ (k * m) + (k * n) ... leftDistributive
--     ~~ m * k + k * n     ... cong (+ k * n) multCommutative
--     ~~ m * k + n * k     ... cong (m * k +) multCommutative
--
-- export
-- 0 multPlusSelf : Ring a => {m,n : a} -> m * n + m === m * (n + 1)
-- multPlusSelf =
--   Calc $
--     |~ m * n + m
--     ~~ m * n + m * 1 ..< cong (m*n +) multOneRightNeutral
--     ~~ m * (n + 1)   ..< leftDistributive
