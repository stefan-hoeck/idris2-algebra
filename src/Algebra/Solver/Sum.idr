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

||| Evaluate a sum of terms.
public export
esum :
     {as : List a}
  -> {z, o : a}
  -> {p,m : a -> a -> a}
  -> (0 r : Rig a z o p m)
  -> Sum a as
  -> a
esum r []        = z
esum r (x :: xs) = eterm m o x `p` esum r xs

--------------------------------------------------------------------------------
--          Normalizer
--------------------------------------------------------------------------------

||| Add two sums of terms.
|||
||| The order of terms will be kept. If two terms have identical
||| products of variables, they will be unified by adding their
||| factors.
public export
add : (p : a -> a -> a) ->  Sum a as -> Sum a as -> Sum a as
add p []        ys                = ys
add p xs        []                = xs
add p (T m x :: xs) (T n y :: ys) = case compProd x y of
  LT => T m x :: add p xs (T n y :: ys)
  GT => T n y :: add p (T m x :: xs) ys
  EQ => T (m `p` n) y :: add p xs ys

||| Normalize a sum of terms by removing all terms with a
||| `zero` factor.
public export
normSum :
     {z : a}
  -> (isZ : (v : a) -> Maybe (v === z))
  -> Sum a as -> Sum a as
normSum isZ []           = []
normSum isZ (T f p :: y) = case isZ f of
  Just refl => normSum isZ y
  Nothing   => T f p :: normSum isZ y

||| Multiplies a single term with a sum of terms.
public export
mult1 : (m : a -> a -> a) -> Term a as -> Sum a as -> Sum a as
mult1 m (T f p) (T g q :: xs) = T (f `m` g) (mult p q) :: mult1 m (T f p) xs
mult1 m _       []            = []

||| Multiplies two sums of terms.
public export
mult : (p,m : a -> a -> a) -> Sum a as -> Sum a as -> Sum a as
mult p m []        ys = []
mult p m (x :: xs) ys = add p (mult1 m x ys) (mult p m xs ys)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

-- Adding two sums via `add` preserves the evaluation result.
0 padd :
     {z,o : a}
  -> {p,m : a -> a -> a}
  -> (0 r : Rig a z o p m)
  -> (x, y : Sum a as)
  -> esum r x `p` esum r y === esum r (add p x y)
padd r []            xs = r.plus.leftNeutral
padd r (x :: xs)     [] = r.plus.rightNeutral
padd r (T f x :: xs) (T g y :: ys) with (compProd x y) proof eq
  _ | LT = Calc $
    |~ ((f `m` eprod m o x) `p` esum r xs) `p` ((g `m` eprod m o y) `p` esum r ys)
    ~~ (f `m` eprod m o x) `p` (esum r xs `p` ((g `m` eprod m o y) `p` esum r ys))
      ..< r.plus.associative
    ~~ (f `m` eprod m o x) `p` esum r (add p xs (T g y :: ys))
      ... cong (f `m` eprod m o x `p`) (padd r xs (T g y :: ys))
  _ | GT = Calc $
    |~ ((f `m` eprod m o x) `p` esum r xs) `p` ((g `m` eprod m o y) `p` esum r ys)
    ~~ ((g `m` eprod m o y) `p` (((f `m` eprod m o x) `p` esum r xs) `p` esum r ys))
      ..< lemma213 r.plus.csgrp
    ~~ (g `m` eprod m o y) `p` esum r (add p (T f x :: xs) ys)
      ... cong ((g `m` eprod m o y) `p`) (padd r (T f x :: xs) ys)
  _ | EQ = case pcompProd x y eq of
        Refl => Calc $
          |~ ((f `m` eprod m o x) `p` esum r xs) `p` ((g `m` eprod m o x) `p` esum r ys)
          ~~ ((f `m` eprod m o x) `p` (g `m` eprod m o x)) `p` (esum r xs `p` esum r ys)
            ... lemma1324 r.plus.csgrp
          ~~ ((f `p` g) `m` eprod m o x) `p` (esum r xs `p` esum r ys)
            ..< cong ( `p` (esum r xs `p` esum r ys)) (rightDistributive r)
          ~~ ((f `p` g) `m` eprod m o x) `p` esum r (add p xs ys)
            ... cong (((f `p` g) `m` eprod m o x) `p`) (padd r xs ys)

-- Small utility lemma
0 psum0 :
     Rig a z o p m
  -> {x,y,v : a}
  -> x === y
  -> x === z `m` v `p` y
psum0 r prf = Calc $
  |~ x
  ~~ y             ... prf
  ~~ z `p` y       ..< r.plus.leftNeutral
  ~~ z `m` v `p` y ..< cong (`p` y) r.multZeroLeftAbsorbs

-- Multiplying a sum with a term preserves the evaluation result.
0 pmult1 :
     {z,o : a}
  -> {p,m : a -> a -> a}
  -> (0 r : Rig a z o p m)
  -> (v : a)
  -> (q : Prod a as)
  -> (s : Sum a as)
  -> esum r (mult1 m (T v q) s) === (v `m` eprod m o q) `m` esum r s
pmult1 r v q []            = sym (multZeroRightAbsorbs r)
pmult1 r v q (T f x :: xs) = Calc $
  |~ ((v `m` f) `m` eprod m o (mult q x)) `p` esum r (mult1 m (T v q) xs)
  ~~ ((v `m` f) `m` (eprod m o q `m` eprod m o x)) `p` esum r (mult1 m (T v q) xs)
    ..< cong (\x => ((v `m` f) `m` x) `p` esum r (mult1 m (T v q) xs)) (peprod r.mult q x)
  ~~ ((v `m` eprod m o q ) `m` (f `m` eprod m o x)) `p` esum r (mult1 m (T v q) xs)
    ..< cong ( `p` esum r (mult1 m (T v q) xs)) (lemma1324 r.mult.csgrp)
  ~~ ((v `m` eprod m o q ) `m` (f `m` eprod m o x)) `p` ((v `m` eprod m o q ) `m` esum r xs)
    ...  cong (((v `m` eprod m o q ) `m` (f `m` eprod m o x)) `p`) (pmult1 r v q xs)
  ~~ (v `m` eprod m o q) `m` ((f `m` eprod m o x) `p` esum r xs)
    ..< r.leftDistributive

-- -- Multiplying two sums of terms preserves the evaluation result.
-- 0 pmult :  SolvableSemiring a
--         => (x,y : Sum a as)
--         -> esum x * esum y === esum (mult x y)
-- pmult []            y = multZeroLeftAbsorbs
-- pmult (T n x :: xs) y = Calc $
--   |~ (n * eprod x + esum xs) * esum y
--   ~~ (n * eprod x) * esum y + esum xs * esum y
--      ... rightDistributive
--   ~~ (n * eprod x) * esum y + esum (mult xs y)
--      ... cong ((n * eprod x) * esum y +) (pmult xs y)
--   ~~ esum (mult1 (T n x) y) + esum (mult xs y)
--      ..< cong (+ esum (mult xs y)) (pmult1 n x y)
--   ~~ esum (add (mult1 (T n x) y) (mult xs y))
--      ... padd (mult1 (T n x) y) (mult xs y)
--
-- -- Removing zero values from a sum of terms does not
-- -- affect the evaluation result.
-- 0 pnormSum :  SolvableSemiring a
--            => (s : Sum a as)
--            -> esum (normSum s) === esum s
-- pnormSum []           = Refl
-- pnormSum (T f p :: y) with (isZero f)
--   _ | Nothing   = Calc $
--     |~ f * eprod p + esum (normSum y)
--     ~~ f * eprod p + esum y ... cong ((f * eprod p) +) (pnormSum y)
--
--   _ | Just refl = Calc $
--     |~ esum (normSum y)
--     ~~ esum y               ... pnormSum y
--     ~~ 0 + esum y           ..< plusZeroLeftNeutral
--     ~~ 0 * eprod p + esum y ..< cong (+ esum y) multZeroLeftAbsorbs
--     ~~ f * eprod p + esum y ..< cong (\x => x * eprod p + esum y) refl
--
-- -- Evaluating an expression gives the same result as
-- -- evaluating its normalized form.
-- 0 pnorm :  SolvableSemiring a
--         => (e : Expr a as)
--         -> eval e === esum (norm e)
-- pnorm (Lit n)    = Calc $
--   |~ n
--   ~~ n * 1                    ..< multOneRightNeutral
--   ~~ n * eprod (one {as})     ..< cong (n *) (pone as)
--   ~~ n * eprod (one {as}) + 0 ..< plusZeroRightNeutral
--
-- pnorm (Var x y)  = Calc $
--   |~ x
--   ~~ eprod (fromVar y)          ..< pvar as y
--   ~~ 1 * eprod (fromVar y)      ..< multOneLeftNeutral
--   ~~ 1 * eprod (fromVar y) + 0  ..< plusZeroRightNeutral
--
-- pnorm (Plus x y) = Calc $
--   |~ eval x + eval y
--   ~~ esum (norm x) + eval y
--      ... cong (+ eval y) (pnorm x)
--   ~~ esum (norm x) + esum (norm y)
--      ... cong (esum (norm x) +) (pnorm y)
--   ~~ esum (add (norm x) (norm y))
--      ... padd _ _
--
-- pnorm (Mult x y) = Calc $
--   |~ eval x * eval y
--   ~~ esum (norm x) * eval y
--      ... cong (* eval y) (pnorm x)
--   ~~ esum (norm x) * esum (norm y)
--      ... cong (esum (norm x) *) (pnorm y)
--   ~~ esum (mult (norm x) (norm y))
--      ... Sum.pmult _ _
--
-- -- Evaluating an expression gives the same result as
-- -- evaluating its normalized form.
-- 0 pnormalize :  SolvableSemiring a
--              => (e : Expr a as)
--              -> eval e === esum (normalize e)
-- pnormalize e = Calc $
--   |~ eval e
--   ~~ esum (norm e)           ... pnorm e
--   ~~ esum (normSum (norm e)) ..< pnormSum (norm e)
--
-- --------------------------------------------------------------------------------
-- --          Solver
-- --------------------------------------------------------------------------------
--
-- ||| Given a list `as` of variables and two arithmetic expressions
-- ||| over these variables, if the expressions are converted
-- ||| to the same normal form, evaluating them gives the same
-- ||| result.
-- |||
-- ||| This simple fact allows us to conveniently and quickly
-- ||| proof arithmetic equalities required in other parts of
-- ||| our code. For instance:
-- |||
-- ||| ```idris example
-- ||| 0 binom1 : {x,y : Bits8}
-- |||          -> (x + y) * (x + y) === x * x + 2 * x * y + y * y
-- ||| binom1 = solve [x,y]
-- |||                ((x .+. y) * (x .+. y))
-- |||                (x .*. x + 2 *. x *. y + y .*. y)
-- ||| ```
-- export
-- 0 solve :  SolvableSemiring a
--         => (as : List a)
--         -> (e1,e2 : Expr a as)
--         -> (prf : normalize e1 === normalize e2)
--         => eval e1 === eval e2
-- solve _ e1 e2 = Calc $
--   |~ eval e1
--   ~~ esum (normalize e1) ...(pnormalize e1)
--   ~~ esum (normalize e2) ...(cong esum prf)
--   ~~ eval e2             ..<(pnormalize e2)
