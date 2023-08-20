module Algebra.Solver.Ring

import public Data.List.Elem
import public Algebra.Group
import public Algebra.Ring
import public Algebra.Solver.Ops
import public Algebra.Solver.Product
import public Algebra.Solver.Sum
import Algebra.Solver.Semiring as SR
import Syntax.PreorderReasoning

%hide SR.Expr

%default total

public export
data Expr : (a : Type) -> (as : List a) -> Type where
  ||| A literal. This should be a value known at compile time
  ||| so that it reduces during normalization.
  Lit  : (v : a) -> Expr a as

  ||| A variabl. This is is for values not known at compile
  ||| time. In order to compare and merge variables, we need an
  ||| `Elem x as` proof.
  Var  : (x : a) -> Elem x as -> Expr a as

  ||| Addition of two expressions.
  (+)  : (x,y : Expr a as) -> Expr a as

  ||| Multiplication of two expressions.
  (*)  : (x,y : Expr a as) -> Expr a as

  (-)  : Expr a as -> Expr a as -> Expr a as

--------------------------------------------------------------------------------
--          Syntax
--------------------------------------------------------------------------------

public export
fromInteger : Num a => Integer -> Expr a as
fromInteger = Lit . fromInteger

||| Like `Var` but takes the `Elem x as` as an auto implicit
||| argument.
public export
var : {0 as : List a} -> (x : a) -> Elem x as => Expr a as
var x = Var x %search

||| Addition of variables. This is an alias for
||| `var x + var y`.
public export
(.+.) :
     {0 as : List a}
  -> (x,y : a)
  -> {auto _ : Elem x as}
  -> {auto _ : Elem y as}
  -> Expr a as
(.+.) x y =var x + var y

||| Addition of variables. This is an alias for
||| `x + var y`.
public export
(+.) :
     {0 as : List a}
  -> (x : Expr a as)
  -> (y : a)
  -> {auto _ : Elem y as}
  -> Expr a as
(+.) x y = x + var y

||| Addition of variables. This is an alias for
||| `var x + y`.
public export
(.+) :
     {0 as : List a}
  -> (x : a)
  -> (y : Expr a as)
  -> {auto _ : Elem x as}
  -> Expr a as
(.+) x y = var x + y

||| Addition of variables. This is an alias for
||| `var x + var y`.
public export
(.-.) :
     {0 as : List a}
  -> (x,y : a)
  -> {auto _ : Elem x as}
  -> {auto _ : Elem y as}
  -> Expr a as
(.-.) x y =var x - var y

||| Addition of variables. This is an alias for
||| `x + var y`.
public export
(-.) :
     {0 as : List a}
  -> (x : Expr a as)
  -> (y : a)
  -> {auto _ : Elem y as}
  -> Expr a as
(-.) x y = x - var y

||| Addition of variables. This is an alias for
||| `var x + y`.
public export
(.-) :
     {0 as : List a}
  -> (x : a)
  -> (y : Expr a as)
  -> {auto _ : Elem x as}
  -> Expr a as
(.-) x y = var x - y

||| Multiplication of variables. This is an alias for
||| `var x * var y`.
public export
(.*.) :
     {0 as : List a}
  -> (x,y : a)
  -> {auto _ : Elem x as}
  -> {auto _ : Elem y as}
  -> Expr a as
(.*.) x y = var x * var y

||| Multiplication of variables. This is an alias for
||| `var x * y`.
public export
(*.) :
     {0 as : List a}
  -> (x : Expr a as)
  -> (y : a)
  -> {auto _ : Elem y as}
  -> Expr a as
(*.) x y = x * var y

||| Multiplication of variables. This is an alias for
||| `x * var y`.
public export
(.*) :
     {0 as : List a}
  -> (x : a)
  -> (y : Expr a as)
  -> {auto _ : Elem x as}
  -> Expr a as
(.*) x y = var x * y

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

namespace Eval
  parameters {0 a : Type}
             {as : List a}
             {z,o : a}
             {p,m,sub : a -> a -> a}
             (0 r : Ring a z o p m sub)
             (isZ : (v : a) -> Maybe (v === z))

    public export %inline
    (+) : a -> a -> a
    (+) = p

    public export %inline
    (*) : a -> a -> a
    (*) = m

    public export %inline
    (-) : a -> a -> a
    (-) = sub

    ||| Evaluation of expressions. This keeps the exact
    ||| structure of the expression tree. For instance
    ||| `eval $ x .*. (y .+. z)` evaluates to `x * (y + z)`.
    public export
    eval : Expr a as -> a
    eval (Lit v)   = v
    eval (Var x y) = x
    eval (x + y)   = eval x + eval y
    eval (x * y)   = eval x * eval y
    eval (x - y)   = eval x - eval y

    --------------------------------------------------------------------------------
    --          Normalize
    --------------------------------------------------------------------------------

    public export
    negate : Sum a as -> Sum a as
    negate []            = []
    negate (T f x :: xs) = T (z - f) x :: negate xs

    ||| Normalizes an arithmetic expression to a sum of products.
    public export
    norm : Expr a as -> Sum a as
    norm (Lit n)   = [T n one]
    norm (Var x y) = [T o $ fromVar y]
    norm (x + y)   = add r.rig isZ (norm x) (norm y)
    norm (x * y)   = mult r.rig isZ (norm x) (norm y)
    norm (x - y)   = add r.rig isZ (norm x) (negate $ norm y)

    ||| Like `norm` but removes all `zero` terms.
    public export
    normalize : Expr a as -> Sum a as
    normalize e = normSum r.rig isZ (norm e)

    0 pneg : (s : Sum a as) -> esum r.rig isZ (negate s) === z - esum r.rig isZ s
    pneg []            = sym r.minusSelf
    pneg (T f x :: xs) = Calc $
      |~ (z - f) * eprod m o x + esum (r .rig) isZ (negate xs)
      ~~ (z - f) * eprod m o x + (z - esum (r .rig) isZ xs)
        ... cong ((z - f) * eprod m o x +) (pneg xs)
      ~~ (z - f * eprod m o x) + (z - esum (r .rig) isZ xs)
        ... cong (+ (z - esum (r .rig) isZ xs)) r.multNegLeft
      ~~ z - (esum (r .rig) isZ xs + f * eprod m o x)
        ..< invertProduct r.plus.grp
      ~~ z - (f * eprod m o x + esum r.rig isZ xs)
        ... cong (z `sub`) r.plus.commutative

    -- Evaluating an expression gives the same result as
    -- evaluating its normalized form.
    0 pnorm : (e : Expr a as) -> eval e === esum r.rig isZ (norm e)
    pnorm (Lit n)   = Calc $
      |~ n
      ~~ n * o                        ..< r.mult.rightNeutral
      ~~ n * eprod m o (one {as})     ..< cong (n *) (pone r.mult as)
      ~~ n * eprod m o (one {as}) + z ..< r.plus.rightNeutral

    pnorm (Var x y) = Calc $
      |~ x
      ~~ eprod m o (fromVar y)          ..< pvar r.mult as y
      ~~ o * eprod m o (fromVar y)      ..< r.mult.leftNeutral
      ~~ o * eprod m o (fromVar y) + z  ..< r.plus.rightNeutral

    pnorm (x + y)   = Calc $
      |~ eval x + eval y
      ~~ esum r.rig isZ (norm x) + eval y
         ... cong (+ eval y) (pnorm x)
      ~~ esum r.rig isZ (norm x) + esum r.rig isZ (norm y)
         ... cong (esum r.rig isZ (norm x) +) (pnorm y)
      ~~ esum r.rig isZ (add r.rig isZ (norm x) (norm y))
         ... padd r.rig isZ _ _

    pnorm (x * y) = Calc $
      |~ eval x * eval y
      ~~ esum r.rig isZ (norm x) * eval y
         ... cong (* eval y) (pnorm x)
      ~~ esum r.rig isZ (norm x) * esum r.rig isZ (norm y)
         ... cong (esum r.rig isZ (norm x) *) (pnorm y)
      ~~ esum r.rig isZ (mult r.rig isZ (norm x) (norm y))
         ... pmult r.rig isZ _ _

    pnorm (x - y) = Calc $
      |~ eval x - eval y
      ~~ esum r.rig isZ (norm x) - eval y
        ... cong (\v => v - eval y) (pnorm x)
      ~~ esum r.rig isZ (norm x) - esum r.rig isZ (norm y)
        ... cong (esum r.rig isZ (norm x) -) (pnorm y)
      ~~ (esum r.rig isZ (norm x) + z) - esum r.rig isZ (norm y)
        ..< cong (\v => v - esum r.rig isZ (norm y)) r.plus.rightNeutral
      ~~ esum r.rig isZ (norm x) + (z - esum r.rig isZ (norm y))
        ..< r.minusAssociative
      ~~ esum r.rig isZ (norm x) + (esum r.rig isZ (negate $ norm y))
        ..< cong (esum r.rig isZ (norm x) +) (pneg $ norm y)
      ~~ esum r.rig isZ (add r.rig isZ (norm x) (negate (norm y)))
        ... padd r.rig isZ _ _

    -- Evaluating an expression gives the same result as
    -- evaluating its normalized form.
    0 pnormalize : (e : Expr a as) -> eval e === esum r.rig isZ (normalize e)
    pnormalize e = Calc $
      |~ eval e
      ~~ esum r.rig isZ (norm e)                     ... pnorm e
      ~~ esum r.rig isZ (normSum r.rig isZ (norm e)) ..< pnormSum r.rig isZ (norm e)

    --------------------------------------------------------------------------------
    --          Solver
    --------------------------------------------------------------------------------

    ||| Given a list `as` of variables and two arithmetic expressions
    ||| over these variables, if the expressions are converted
    ||| to the same normal form, evaluating them gives the same
    ||| result.
    |||
    ||| This simple fact allows us to conveniently and quickly
    ||| proof arithmetic equalities required in other parts of
    ||| our code. For instance:
    |||
    ||| ```idris example
    ||| 0 binom1 : {x,y : Bits8}
    |||          -> (x + y) * (x + y) === x * x + 2 * x * y + y * y
    ||| binom1 = solve [x,y]
    |||                ((x .+. y) * (x .+. y))
    |||                (x .*. x + 2 *. x *. y + y .*. y)
    ||| ```
    export
    0 solve :
         (e1,e2 : Expr a as)
      -> {auto prf : normalize e1 === normalize e2}
      -> eval e1 === eval e2
    solve e1 e2 @{prf} = Calc $
      |~ eval e1
      ~~ esum r.rig isZ (normalize e1) ...(pnormalize e1)
      ~~ esum r.rig isZ (normalize e2) ...(cong (esum r.rig isZ) prf)
      ~~ eval e2                       ..<(pnormalize e2)
