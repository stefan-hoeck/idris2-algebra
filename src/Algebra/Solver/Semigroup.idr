module Algebra.Solver.Semigroup

import public Data.List1
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
  Var   : (x : a) -> Expr a
  (<+>) : Expr a -> Expr a -> Expr a

||| Evaluates an expression using the given binary operation.
public export
eval : (p : a -> a -> a) -> Expr a -> a
eval p (Var x)   = x
eval p (x <+> y) = eval p x `p` eval p y

||| Evaluate a list of values over the given binary function.
public export
esum' : (p : a -> a -> a) -> a -> List a -> a
esum' p v []       = v
esum' p v (h :: t) = v `p` esum' p h t

||| Evaluate a non-empty list of values over the given binary function.
public export
esum : (p : a -> a -> a) -> List1 a -> a
esum p (v ::: vs) = esum' p v vs

||| Flatten a tree of expressions into a non-empty list of
||| values.
public export
normalize : Expr a -> List1 a
normalize (Var x)   = x ::: []
normalize (x <+> y) = normalize x ++ normalize y

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 psum' :
     Semigroup a p
  -> (x,y   : a)
  -> (xs,ys : List a)
  -> esum' p x (xs ++ (y :: ys)) === esum' p x xs `p` esum' p y ys
psum' g x y []        ys = Refl
psum' g x y (v :: vs) ys = Calc $
  |~ x `p` esum' p v (vs ++ (y :: ys))
  ~~ x `p` (esum' p v vs `p` esum' p y ys) ... cong (p x) (psum' g v y vs ys)
  ~~ (x `p` esum' p v vs) `p` esum' p y ys ... g.associative

0 psum :
     Semigroup a p
  -> (xs,ys : List1 a)
  -> esum p (xs ++ ys) === esum p xs `p` esum p ys
psum g (x ::: xs) (y ::: ys) = psum' g x y xs ys

0 pnorm :
     Semigroup a p
  -> (e : Expr a)
  -> eval p e === esum p (normalize e)
pnorm g (Var x)      = Refl
pnorm g (x <+> y) = Calc $
  |~ eval p x `p` eval p y
  ~~ esum p (normalize x) `p` eval p y
     ... cong (`p` eval p y) (pnorm g x)
  ~~ esum p (normalize x) `p` esum p (normalize y)
     ... cong (esum p (normalize x) `p`) (pnorm g y)
  ~~ esum p (normalize x ++ normalize y)
     ..< psum g (normalize x) (normalize y)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

||| We can solve equalities over an associative operation `p`
||| by converting both sides to corresponding `Expr`s.
|||
||| ```idris example
||| 0 ex1 : {w,x,y,z : List1 a} -> (w ++ x) ++ (y ++ z) === w ++ x ++ y ++ z
||| ex1 =
|||   solve sgrp_list1
|||     ((Var w <+> Var x) <+> (Var y <+> Var z))
|||     (Var w <+> (Var x <+> (Var y <+> Var z)))
||| ```
export
0 solve :
     Semigroup a p
  -> (e1,e2 : Expr a)
  -> {auto prf : normalize e1 === normalize e2}
  -> eval p e1 === eval p e2
solve g e1 e2 = Calc $
  |~ eval p e1
  ~~ esum p (normalize e1) ... pnorm g e1
  ~~ esum p (normalize e2) ... cong (esum p) prf
  ~~ eval p e2             ..< pnorm g e2

--------------------------------------------------------------------------------
--          Examples
--------------------------------------------------------------------------------

0 ex1 : {w,x,y,z : List1 a} -> (w ++ x) ++ (y ++ z) === w ++ x ++ y ++ z
ex1 =
  solve sgrp_list1
    ((Var w <+> Var x) <+> (Var y <+> Var z))
    (Var w <+> (Var x <+> (Var y <+> Var z)))
