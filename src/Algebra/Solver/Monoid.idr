module Algebra.Solver.Monoid

import public Algebra.Group
import Syntax.PreorderReasoning

%default total

--------------------------------------------------------------------------------
--          Expr
--------------------------------------------------------------------------------

||| Tree representing an algebraic expression consisting of  variables
||| and a single binary operation.
|||
||| Example: `x + (y + z)` is represented as
|||          `Var x <+> (Var y <+> Var z)`
public export
data Expr : (a : Type) -> Type where
  Var     : (x : a) -> Expr a
  Neutral : Expr a
  (<+>)   : Expr a -> Expr a -> Expr a

||| Evaluates an expression using the given binary operation.
public export
eval : (z : a) -> (p : a -> a -> a) -> Expr a -> a
eval z p (Var x)   = x
eval z p Neutral   = z
eval z p (x <+> y) = eval z p x `p` eval z p y

||| Evaluate a non-empty list of values over the given binary function.
public export
esum : (z : a) -> (p : a -> a -> a) -> List a -> a
esum z p []        = z
esum z p (v :: vs) = v `p` esum z p vs

||| Flatten a tree of expressions into a non-empty list of
||| values.
public export
normalize : Expr a -> List a
normalize (Var x)   = [x]
normalize Neutral   = []
normalize (x <+> y) = normalize x ++ normalize y

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 psum :
     Monoid a z p
  -> (xs,ys : List a)
  -> esum z p (xs ++ ys) === esum z p xs `p` esum z p ys
psum m []        ys = sym m.leftNeutral
psum m (x :: xs) ys = Calc $
  |~ x `p` esum z p (xs ++ ys) 
  ~~ x `p` (esum z p xs `p` esum z p ys) ... cong (p x) (psum m xs ys)
  ~~ (x `p` esum z p xs) `p` esum z p ys ... m.associative

0 pnorm :
     Monoid a z p
  -> (e : Expr a)
  -> eval z p e === esum z p (normalize e)
pnorm m (Var x)   = sym m.rightNeutral
pnorm m Neutral   = Refl
pnorm m (x <+> y) = Calc $
  |~ eval z p x `p` eval z p y
  ~~ esum z p (normalize x) `p` eval z p y
     ... cong (`p` eval z p y) (pnorm m x)
  ~~ esum z p (normalize x) `p` esum z p (normalize y)
     ... cong (esum z p (normalize x) `p`) (pnorm m y)
  ~~ esum z p (normalize x ++ normalize y)
     ..< psum m (normalize x) (normalize y)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

||| We can solve equalities over an associative operation `p`
||| by converting both sides to corresponding `Expr`s.
|||
||| ```idris example
||| 0 ex1 :
|||      {w,x,y,z : List a}
|||   -> (w ++ x) ++ ((y ++ []) ++ z) === w ++ x ++ y ++ z
||| ex1 =
|||   solve mon_list
|||     ((Var w <+> Var x) <+> ((Var y <+> Neutral) <+> Var z))
|||     (Var w <+> (Var x <+> (Var y <+> Var z)))
||| ```
export
0 solve :
     Monoid a z p
  -> (e1,e2 : Expr a)
  -> {auto prf : normalize e1 === normalize e2}
  -> eval z p e1 === eval z p e2
solve m e1 e2 = Calc $
  |~ eval z p e1
  ~~ esum z p (normalize e1) ... pnorm m e1
  ~~ esum z p (normalize e2) ... cong (esum z p) prf
  ~~ eval z p e2             ..< pnorm m e2

--------------------------------------------------------------------------------
--          Examples
--------------------------------------------------------------------------------

0 ex1 : {w,x,y,z : List a} -> (w ++ x) ++ ((y ++ []) ++ z) === w ++ x ++ y ++ z
ex1 =
  solve mon_list
    ((Var w <+> Var x) <+> ((Var y <+> Neutral) <+> Var z))
    (Var w <+> (Var x <+> (Var y <+> Var z)))
