module Algebra.Solver.Semigroup

import Syntax.PreorderReasoning

import public Algebra.Group
import public Algebra.Solver.Ops
import public Data.List1

%default total

||| Tree representing an algebraic expression in a semigroup structure.
|||
||| The idea here is to represent algebraic expressions as an `Expr a as`,
||| where `a` is the type we operate on and `as` is a list of known
||| variables. Such an `Expr a as` can then be normalized using function
||| `normalize`. We proof in this module, that the result of evaluating an
||| expression is not affected by normalization. Hence, if two expressions
||| `e1` and `e2` have the same normalized representation, the results
||| of evaluating the two (`eval e1` and `eval e2`) are propositionally
||| equal. This is, what function `solve` is used for.
public export
data Expr : (a : Type) -> (as : List a) -> Type where
  ||| A literal value known at compile time. Use this if you want
  ||| values known at runtime to unify.
  Lit     : (lit : a) -> Expr a as

  ||| A variable from the given list of variables.
  Var     : (x : a) -> Elem x as -> Expr a as

  ||| Represents the binary operation of the monoid
  (<+>)   : Expr a as -> Expr a as -> Expr a as

||| An `Expr a as` is normalized to a sequence of terms of type
||| `List (Term a as)`.
public export
data Term : (a : Type) -> (as : List a) -> Type where
  TLit : (lit : a) -> Term a as
  TVar : (x : a) -> Elem x as -> Term a as

--------------------------------------------------------------------------------
--          Syntax
--------------------------------------------------------------------------------

||| Alias for `var` that uses an auto-implicit proof of `Elem x xs`.
public export %inline
var : (x : a) -> {auto p : Elem x xs} -> Expr a xs
var x = Var x p

||| Alias for `var x <+> y`
public export %inline
(.+>) : (x : a) -> Expr a xs -> {auto p : Elem x xs} -> Expr a xs
(.+>) x y = Var x p <+> y

||| Alias for `x <+> var y`
public export %inline
(<+.) : Expr a xs -> (x : a) -> {auto p : Elem x xs} -> Expr a xs
(<+.) x y = x <+> Var y p

||| Alias for `var x .+. var y`
public export %inline
(.+.) :
     (x,y : a)
  -> {auto p : Elem x xs}
  -> {auto q : Elem y xs}
  -> Expr a xs
(.+.) x y = Var x p <+> Var y q

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

||| Evaluates an expression over the given monoid.
||| Note: The idea is to use this function at compile-time to
|||       convert the expression we evaluate to the corresponding
|||       Idris expression.
public export
eval : {p : a -> a -> a} -> (0 s : Semigroup a p) -> Expr a as -> a
eval s (Lit lit) = lit
eval s (Var x _) = x
eval s (x <+> y) = eval s x `p` eval s y

||| Evaluates a single term.
public export
eterm : Term a as -> a
eterm (TLit lit) = lit
eterm (TVar x y) = x

||| Evaluates a list of terms over the given Semigroup.
public export
elist :
     {p : a -> a -> a}
  -> (0 s : Semigroup a p)
  -> (t : Term a as)
  -> List (Term a as)
  -> a
elist s v []        = eterm v
elist s v (x :: xs) = eterm v `p` elist s x xs

||| Evaluates a non-empty list of terms over the given Semigroup.
public export
elist1 : {p : a -> a -> a} -> (0 s : Semigroup a p) -> List1 (Term a as) -> a
elist1 s (h ::: t) = elist s h t

--------------------------------------------------------------------------------
--          Normalization
--------------------------------------------------------------------------------

||| Flattens an expression into a list of terms
public export
flatten : Expr a as -> List1 (Term a as)
flatten (Lit lit) = TLit lit ::: []
flatten (Var x y) = TVar x y ::: []
flatten (x <+> y) = flatten x ++ flatten y

||| Prepends a single term in front of a list of terms.
||| This will remove terms that evaluate to zero and
||| fuse neighbouring literals.
public export
prepend :
     {p   : a -> a -> a}
  -> (0 s : Semigroup a p)
  -> List1 (Term a as)
  -> Term a as
  -> List1 (Term a as)
prepend s (TLit x ::: xs) (TLit y) = TLit (y `p` x) ::: xs
prepend s (x      ::: xs) y        = y ::: x :: xs

public export
merge :
     {p : a -> a -> a}
  -> (0 s : Semigroup a p)
  -> (t : Term a as)
  -> List (Term a as)
  -> List1 (Term a as)
merge s t []        = t ::: []
merge s t (x :: xs) = prepend s (merge s x xs) t

public export
merge1 :
     {p : a -> a -> a}
  -> (0 s : Semigroup a p)
  -> List1 (Term a as)
  -> List1 (Term a as)
merge1 s (t ::: ts) = merge s t ts

public export
normalize : {p : _} -> (0 s : Semigroup a p) -> Expr a as -> List1 (Term a as)
normalize s e = merge1 s (flatten e)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 pelist :
     (s  : Semigroup a p)
  -> (v  : Term a as)
  -> (w  : Term a as)
  -> (vs : List (Term a as))
  -> (ws : List (Term a as))
  -> elist s v vs `p` elist s w ws === elist s v (vs ++ w :: ws)
pelist s v w []        ws = Refl
pelist s v w (x :: xs) ws = Calc $
  |~ (eterm v `p` elist s x xs) `p` elist s w ws
  ~~ eterm v `p` (elist s x xs `p` elist s w ws)
     ..< s.associative
  ~~ eterm v `p` elist s x (xs ++ (w :: ws))
     ... cong (eterm v `p`) (pelist s x w xs ws)

0 pelist1 :
     (s  : Semigroup a p)
  -> (vs : List1 (Term a as))
  -> (ws : List1 (Term a as))
  -> elist1 s vs `p` elist1 s ws === elist1 s (vs ++ ws)
pelist1 s (v ::: vs) (w ::: ws) = pelist s v w vs ws

0 pflatten :
     (s : Semigroup a p)
  -> (e : Expr a as)
  -> eval s e === elist1 s (flatten e)
pflatten s (Lit lit) = Refl
pflatten s (Var x y) = Refl
pflatten s (x <+> y) = Calc $
  |~ eval s x `p` eval s y
  ~~ elist1 s (flatten x) `p` eval s y
     ... cong (`p` eval s y) (pflatten s x)
  ~~ elist1 s (flatten x) `p` elist1 s (flatten y)
     ... cong (elist1 s (flatten x) `p`) (pflatten s y)
  ~~ elist1 s (flatten x ++ flatten y)
     ... pelist1 s (flatten x) (flatten y)

0 pprepend :
     (s   : Semigroup a p)
  -> (ts  : List1 (Term a as))
  -> (t   : Term a as)
  -> eterm t `p` elist1 s ts === elist1 s (prepend s ts t)
pprepend s (TLit lit ::: [])      (TLit x)   = Refl
pprepend s (TLit lit ::: t :: ts) (TLit x)   = s.associative
pprepend s (TLit lit ::: ts)      (TVar x y) = Refl
pprepend s (TVar x y ::: ts)      (TLit lit) = Refl
pprepend s (TVar x y ::: ts)      (TVar z w) = Refl

0 pmerge :
     (s   : Semigroup a p)
  -> (t   : Term a as)
  -> (ts  : List (Term a as))
  -> elist s t ts === elist1 s (merge s t ts)
pmerge s t []        = Refl
pmerge s t (x :: xs) = Calc $
  |~ eterm t `p` elist s x xs
  ~~ eterm t `p` elist1 s (merge s x xs)
     ... cong (eterm t `p`) (pmerge s x xs)
  ~~ elist1 s (prepend s (merge s x xs) t)
     ... pprepend s (merge s x xs) t

0 pmerge1 :
     (s   : Semigroup a p)
  -> (ts  : List1 (Term a as))
  -> elist1 s ts === elist1 s (merge1 s ts)
pmerge1 s (t ::: ts) = pmerge s t ts

0 pnormalize :
     (s   : Semigroup a p)
  -> (e   : Expr a as)
  -> eval s e === elist1 s (normalize s e)
pnormalize s e = Calc $
  |~ eval s e
  ~~ elist1 s (flatten e)            ... pflatten s e
  ~~ elist1 s (merge1 s $ flatten e) ... pmerge1 s (flatten e)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

export
0 solve :
     (s     : Semigroup a p)
  -> (e1,e2 : Expr a as)
  -> {auto prf : normalize s e1 === normalize s e2}
  -> eval s e1 === eval s e2
solve s e1 e2 = Calc $
  |~ eval s e1
  ~~ elist1 s (normalize s e1) ... pnormalize s e1
  ~~ elist1 s (normalize s e2) ... cong (elist1 s) prf
  ~~ eval s e2                 ..< pnormalize s e2
