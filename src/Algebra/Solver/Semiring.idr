module Algebra.Solver.Semiring

import public Data.List.Elem
import public Algebra.Group
import public Algebra.Ring
import public Algebra.Solver.Ops
import public Algebra.Solver.Product
import public Algebra.Solver.Sum
import Syntax.PreorderReasoning

%default total

--------------------------------------------------------------------------------
--          Expression
--------------------------------------------------------------------------------

||| Data type representing expressions in a commutative semiring.
|||
||| This is used to at compile time compare different forms of
||| the same expression and proof that they evaluate to
||| the same result.
|||
||| An example:
|||
||| ```idris example
||| 0 binom1 : {x,y : Bits8} -> (x + y) * (x + y) === x * x + 2 * x * y + y * y
||| binom1 = solve [x,y]
|||                ((x .+. y) * (x .+. y))
|||                (x .*. x + 2 *. x *. y + y .*. y)
||| ```
|||
||| @ a  the type used in the arithmetic expression
||| @ as list of variables which don't reduce at compile time
|||
||| In the example above, `x` and `y` are variables, while `2`
||| is a literal known at compile time. To make working with
||| variables more convenient (the have to be wrapped in data
||| constructor `Var`, by using function `var` for instance),
||| additional operators for addition, multiplication, and
||| subtraction are provided.
|||
||| In order to proof that two expressions evaluate to the
||| same results, the following steps are taken at compile
||| time:
|||
||| 1. Both expressions are converted to a normal form via
|||    `Algebra.Solver.Semiring.Sum.normalize`.
||| 2. The normal forms are compared for being identical.
||| 3. Since in `Algebra.Solver.Semiring.Sum` there is a proof that
|||    converting an expression to its normal form does not
|||    affect the result when evaluating it, if the normal
|||    forms are identical, the two expressions must evaluate
|||    to the same result.
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

infixl 8 .+., .+, +.

infixl 9 .*., .*, *.

||| Addition of variables. This is an alias for
||| `var x + var y`.
public export
(.+.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.+.) x y =var x + var y

||| Addition of variables. This is an alias for
||| `x + var y`.
public export
(+.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(+.) x y = x + var y

||| Addition of variables. This is an alias for
||| `var x + y`.
public export
(.+) :  {0 as : List a}
     -> (x : a)
     -> (y : Expr a as)
     -> Elem x as
     => Expr a as
(.+) x y = var x + y

||| Multiplication of variables. This is an alias for
||| `var x * var y`.
public export
(.*.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.*.) x y = var x * var y

||| Multiplication of variables. This is an alias for
||| `var x * y`.
public export
(*.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(*.) x y = x * var y

||| Multiplication of variables. This is an alias for
||| `x * var y`.
public export
(.*) :  {0 as : List a}
     -> (x : a)
     -> (y : Expr a as)
     -> Elem x as
     => Expr a as
(.*) x y = var x * y

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

namespace Eval
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

    ||| Evaluation of expressions. This keeps the exact
    ||| structure of the expression tree. For instance
    ||| `eval $ x .*. (y .+. z)` evaluates to `x * (y + z)`.
    public export
    eval : Expr a as -> a
    eval (Lit v)   = v
    eval (Var x y) = x
    eval (x + y)   = eval x + eval y
    eval (x * y)   = eval x * eval y

    --------------------------------------------------------------------------------
    --          Normalize
    --------------------------------------------------------------------------------

    ||| Normalizes an arithmetic expression to a sum of products.
    public export
    norm : Expr a as -> Sum a as
    norm (Lit n)   = [T n one]
    norm (Var x y) = [T o $ fromVar y]
    norm (x + y)   = add r isZ (norm x) (norm y)
    norm (x * y)   = mult r isZ (norm x) (norm y)

    ||| Like `norm` but removes all `zero` terms.
    public export
    normalize : Expr a as -> Sum a as
    normalize e = normSum r isZ (norm e)

    -- Evaluating an expression gives the same result as
    -- evaluating its normalized form.
    0 pnorm : (e : Expr a as) -> eval e === esum r isZ (norm e)
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
      ~~ esum r isZ (norm x) + eval y
         ... cong (+ eval y) (pnorm x)
      ~~ esum r isZ (norm x) + esum r isZ (norm y)
         ... cong (esum r isZ (norm x) +) (pnorm y)
      ~~ esum r isZ (add r isZ (norm x) (norm y))
         ... padd r isZ _ _

    pnorm (x * y) = Calc $
      |~ eval x * eval y
      ~~ esum r isZ (norm x) * eval y
         ... cong (* eval y) (pnorm x)
      ~~ esum r isZ (norm x) * esum r isZ (norm y)
         ... cong (esum r isZ (norm x) *) (pnorm y)
      ~~ esum r isZ (mult r isZ (norm x) (norm y))
         ... pmult r isZ _ _

    -- Evaluating an expression gives the same result as
    -- evaluating its normalized form.
    0 pnormalize : (e : Expr a as) -> eval e === esum r isZ (normalize e)
    pnormalize e = Calc $
      |~ eval e
      ~~ esum r isZ (norm e)                 ... pnorm e
      ~~ esum r isZ (normSum r isZ (norm e)) ..< pnormSum r isZ (norm e)

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
      -> (prf : normalize e1 === normalize e2)
      => eval e1 === eval e2
    solve e1 e2 @{prf} = Calc $
      |~ eval e1
      ~~ esum r isZ (normalize e1) ...(pnormalize e1)
      ~~ esum r isZ (normalize e2) ...(cong (esum r isZ) prf)
      ~~ eval e2                   ..<(pnormalize e2)

public export
NatIsZero : (n : Nat) -> Maybe (n === 0)
NatIsZero 0 = Just Refl
NatIsZero _ = Nothing

export
0 solveNat :
     (as : List Nat)
  -> (e1,e2 : Expr Nat as)
  -> (prf : normalize NatRig NatIsZero e1 === normalize NatRig NatIsZero e2)
  => eval NatRig NatIsZero e1 === eval NatRig NatIsZero e2
solveNat _ = solve NatRig NatIsZero

--------------------------------------------------------------------------------
--          Examples
--------------------------------------------------------------------------------

0 ex1 : (m,n : Nat) -> m + n === n + m
ex1 m n = solveNat [m,n] (m .+. n) (n .+. m)

0 ex2 : (m,n : Nat) -> m + n + 3 === 1 + n + m + 2
ex2 m n = solveNat [m,n] (m .+. n + 3) (1 +. n +. m + 2)

%ambiguity_depth 4
0 ex3 : (k,m,n : Nat) -> (12 + k) * (m + n) === n * 12 + 3 * m + (n + m) * k + m * 9
ex3 k m n =
  solveNat [k,m,n]
    ((12 +. k) * (m .+. n))
    (n .* 12 + 3 *. m + (n .+. m) *. k + (m .* 9))
