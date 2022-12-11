module Algebra.Solver.Sum

import Algebra.Group
import Algebra.Ring
import Algebra.Solver.Product
import Syntax.PreorderReasoning

%default total

||| Normalized arithmetic expression in a commutative
||| ring (represented as an (ordered) sum of terms).
public export
data Sum : (a : Type) -> (as : List a) -> Type where
  Nil  : {0 as : List a} -> Sum a as
  (::) : {0 as : List a} -> Term a as -> Sum a as -> Sum a as

parameters {0 a : Type}
           {as : List a}
           {z,o : a}
           {p,m : a -> a -> a}
           (0 r : Rig a z o p m)
           (isZ : (v : a) -> Maybe (v === z))

  public export %inline
  (+) : a -> a -> a
  (+) = p

  public export %inline
  (*) : a -> a -> a
  (*) = m

  public export %inline
  eterm : Term a as -> a
  eterm = Product.eterm m o

  ||| Evaluate a sum of terms.
  public export
  esum : Sum a as -> a
  esum []        = z
  esum (x :: xs) = eterm x + esum xs

--------------------------------------------------------------------------------
--          Normalizer
--------------------------------------------------------------------------------

  ||| Add two sums of terms.
  |||
  ||| The order of terms will be kept. If two terms have identical
  ||| products of variables, they will be unified by adding their
  ||| factors.
  public export
  add : Sum a as -> Sum a as -> Sum a as
  add []        ys                = ys
  add xs        []                = xs
  add (T m x :: xs) (T n y :: ys) = case compProd x y of
    LT => T m x :: add xs (T n y :: ys)
    GT => T n y :: add (T m x :: xs) ys
    EQ => T (m + n) y :: add xs ys

  ||| Normalize a sum of terms by removing all terms with a
  ||| `zero` factor.
  public export
  normSum : Sum a as -> Sum a as
  normSum []           = []
  normSum (T f p :: y) = case isZ f of
    Just refl => normSum y
    Nothing   => T f p :: normSum y

  ||| Multiplies a single term with a sum of terms.
  public export
  mult1 :  Term a as -> Sum a as -> Sum a as
  mult1 (T f p) (T g q :: xs) = T (f * g) (mult p q) :: mult1 (T f p) xs
  mult1 _       []            = []

  ||| Multiplies two sums of terms.
  public export
  mult : Sum a as -> Sum a as -> Sum a as
  mult []        ys = []
  mult (x :: xs) ys = add (mult1 x ys) (mult xs ys)

  --------------------------------------------------------------------------------
  --          Proofs
  --------------------------------------------------------------------------------

  epr : Prod a as -> a
  epr = eprod m o

  -- Adding two sums via `add` preserves the evaluation result.
  export
  0 padd : (x, y : Sum a as) -> esum x + esum y === esum (add x y)
  padd []            xs = r.plus.leftNeutral
  padd (x :: xs)     [] = r.plus.rightNeutral
  padd (T f x :: xs) (T g y :: ys) with (compProd x y) proof eq
    _ | LT = Calc $
      |~ (f * epr x + esum xs) + (g * epr y + esum ys)
      ~~ (f * epr x) + (esum xs + (g * epr y + esum ys))
        ..< r.plus.associative
      ~~ f * epr x + esum (add xs (T g y :: ys))
        ... cong (f * epr x +) (padd xs (T g y :: ys))
    _ | GT = Calc $
      |~ (f * epr x + esum xs) + (g * epr y + esum ys)
      ~~ g * epr y + ((f * epr x + esum xs) + esum ys)
         ..< lemma213 r.plus.csgrp
      ~~ g * epr y + esum (add (T f x :: xs) ys)
         ... cong (g * epr y  +) (padd (T f x :: xs) ys)
    _ | EQ = case pcompProd x y eq of
         Refl => Calc $
           |~ (f * epr x + esum xs) + (g * epr x + esum ys)
           ~~ (f * epr x + g * epr x) + (esum xs + esum ys)
             ... lemma1324 r.plus.csgrp
           ~~ (f + g) * epr x + (esum xs + esum ys)
             ..< cong ( + (esum xs + esum ys)) (rightDistributive r)
           ~~ (f + g) * epr x + esum (add xs ys)
             ... cong ((f + g) * epr x +) (padd xs ys)

  -- Small utility lemma
  0 psum0 : {x,y,v : a} -> x === y -> x === z * v + y
  psum0 {x} {y} {v} prf = Calc $
    |~ x
    ~~ y         ... prf
    ~~ z + y     ..< r.plus.leftNeutral
    ~~ z * v + y ..< cong (+ y) r.multZeroLeftAbsorbs

  -- Multiplying a sum with a term preserves the evaluation result.
  0 pmult1 :
       (v : a)
    -> (q : Prod a as)
    -> (s : Sum a as)
    -> esum (mult1 (T v q) s) === (v * epr q) * esum s
  pmult1 v q []            = sym (multZeroRightAbsorbs r)
  pmult1 v q (T f x :: xs) = Calc $
    |~ (v * f) * epr (mult q x) + esum (mult1 (T v q) xs)
    ~~ (v * f) * (epr q * epr x) + esum (mult1 (T v q) xs)
      ..< cong (\x => ((v * f) * x) + esum (mult1 (T v q) xs)) (peprod r.mult q x)
    ~~ (v * epr q ) * (f * epr x) + esum (mult1 (T v q) xs)
      ..< cong ( + esum (mult1 (T v q) xs)) (lemma1324 r.mult.csgrp)
    ~~ (v * epr q ) * (f * epr x) + (v * epr q ) * esum xs
      ...  cong (((v * epr q ) * (f * epr x)) +) (pmult1 v q xs)
    ~~ (v * epr q) * (f * epr x + esum xs)
      ..< r.leftDistributive

  -- Multiplying two sums of terms preserves the evaluation result.
  export
  0 pmult : (x,y : Sum a as) -> esum x * esum y === esum (mult x y)
  pmult []            y = r.multZeroLeftAbsorbs
  pmult (T f x :: xs) y = Calc $
    |~ (f * epr x + esum xs) * esum y
    ~~ (f * epr x) * esum y + esum xs * esum y
      ... rightDistributive r
    ~~ (f * epr x) * esum y + esum (mult xs y)
      ... cong ((f * epr x) * esum y +) (pmult xs y)
    ~~ esum (mult1 (T f x) y) + esum (mult xs y)
      ..< cong ( + esum (mult xs y)) (pmult1 f x y)
    ~~ esum (add (mult1 (T f x) y) (mult xs y))
      ... padd (mult1 (T f x) y) (mult xs y)

  -- Removing zero values from a sum of terms does not
  -- affect the evaluation result.
  export
  0 pnormSum : (s : Sum a as) -> esum (normSum s) === esum s
  pnormSum []           = Refl
  pnormSum (T f y :: ys) with (isZ f)
    _ | Nothing   = Calc $
      |~ f * epr y + esum (normSum ys)
      ~~ f * epr y + esum ys ... cong ((f * epr y) +) (pnormSum ys)

    _ | Just refl = Calc $
      |~ esum (normSum ys)
      ~~ esum ys               ... pnormSum ys
      ~~ z + esum ys           ..< r.plus.leftNeutral
      ~~ z * epr y + esum ys ..< cong (+ esum ys) r.multZeroLeftAbsorbs
      ~~ f * epr y + esum ys ..< cong (\x => x * epr y + esum ys) refl
