module Algebra.Solver.Monoid

import Syntax.PreorderReasoning

import public Algebra.Group
import public Algebra.Solver.Ops
import public Data.List.Elem

%default total

||| Tree representing an algebraic expression in a monoid structure.
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

  ||| Represents the neutral element of the monoid
  Neutral : Expr a as

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
eval :
     {z : a}
  -> {p : a -> a -> a}
  -> (0 m : Monoid a z p)
  -> Expr a as
  -> a
eval m (Lit lit) = lit
eval m (Var x _) = x
eval m Neutral   = z
eval m (x <+> y) = eval m x `p` eval m y

||| Evaluates a single term.
public export
eterm : Term a as -> a
eterm (TLit lit) = lit
eterm (TVar x y) = x

||| Evaluates a list of terms over the given monoid.
public export
elist :
     {z : a}
  -> {p : a -> a -> a}
  -> (0 m : Monoid a z p)
  -> List (Term a as)
  -> a
elist m []        = z
elist m (x :: xs) = eterm x `p` elist m xs

--------------------------------------------------------------------------------
--          Normalization
--------------------------------------------------------------------------------

||| Flattens an expression into a list of terms
public export
flatten : Expr a as -> List (Term a as)
flatten (Lit lit) = [TLit lit]
flatten (Var x y) = [TVar x y]
flatten Neutral   = []
flatten (x <+> y) = flatten x ++ flatten y

||| Tries to fuse two neighbouring terms
public export
fuse :
     {z   : a}
  -> {p   : a -> a -> a}
  -> (0 m : Monoid a z p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> Term a as -> Term a as -> List (Term a as)
fuse m isZ (TLit lit) (TLit x) = case isZ (lit `p` x) of
  Just _  => []
  Nothing => [TLit $ lit `p` x]
fuse m isZ (TLit lit) t        = case isZ lit of
  Just _  => [t]
  Nothing => [TLit lit, t]
fuse m isZ x          y        = [x,y]

||| Prepends a single term in front of a list of terms.
||| This will remove terms that evaluate to zero and
||| fuse neighbouring literals.
public export
prepend :
     {z   : a}
  -> {p   : a -> a -> a}
  -> (0 m : Monoid a z p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> List (Term a as)
  -> Term a as
  -> List (Term a as)
prepend m isZ [] (TVar x p) = [TVar x p]
prepend m isZ [] (TLit x)   = case isZ x of
  Just p  => []
  Nothing => [TLit x]
prepend m isZ (x :: xs) t = fuse m isZ t x ++ xs

public export
merge :
     {z : a}
  -> {p : a -> a -> a}
  -> (0 m : Monoid a z p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> List (Term a as)
  -> List (Term a as)
merge m isZ []        = []
merge m isZ (x :: xs) = prepend m isZ (merge m isZ xs) x

public export
normalize :
     {z   : a}
  -> {p   : a -> a -> a}
  -> (0 m : Monoid a z p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> Expr a as
  -> List (Term a as)
normalize m isZ e = merge m isZ (flatten e)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 pelist :
     (m : Monoid a z p)
  -> (vs,ws : List (Term a as))
  -> elist m vs `p` elist m ws === elist m (vs ++ ws)
pelist m []        ws = m.leftNeutral
pelist m (v :: vs) ws = Calc $
  |~ (eterm v `p` elist m vs) `p` elist m ws
  ~~ eterm v `p` (elist m vs `p` elist m ws)
     ..< m.associative
  ~~ eterm v `p` elist m (vs ++ ws)
     ... cong (eterm v `p`) (pelist m vs ws)

0 pflatten :
     (m : Monoid a z p)
  -> (e : Expr a as)
  -> eval m e === elist m (flatten e)
pflatten m (Lit lit) = sym m.rightNeutral
pflatten m (Var x y) = sym m.rightNeutral
pflatten m Neutral   = Refl
pflatten m (x <+> y) = Calc $
  |~ eval m x `p` eval m y
  ~~ elist m (flatten x) `p` eval m y
     ... cong (`p` eval m y) (pflatten m x)
  ~~ elist m (flatten x) `p` elist m (flatten y)
     ... cong (elist m (flatten x) `p`) (pflatten m y)
  ~~ elist m (flatten x ++ flatten y)
     ... pelist m (flatten x) (flatten y)

0 pfuse :
     (m : Monoid a z p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> (t1,t2 : Term a as)
  -> eterm t1 `p` eterm t2 === elist m (fuse m isZ t1 t2)
pfuse m isZ (TLit lit) (TLit x) with (isZ $ lit `p` x)
  pfuse m isZ (TLit lit) (TLit x) | Just prf = prf
  pfuse m isZ (TLit lit) (TLit x) | Nothing  = sym $ m.rightNeutral

pfuse m isZ (TLit lit) (TVar x y) with (isZ lit)
  pfuse m isZ (TLit lit) (TVar x y) | Just prf = Calc $
    |~ lit `p` x
    ~~ z `p` x ... cong (`p` x) prf
    ~~ x       ... m.leftNeutral
    ~~ x `p` z ..< m.rightNeutral
  pfuse m isZ (TLit lit) (TVar x y) | Nothing  =
    cong (lit `p`) $ sym m.rightNeutral

pfuse m isZ (TVar x y) (TLit lit) = cong (x `p`) $ sym m.rightNeutral
pfuse m isZ (TVar x y) (TVar w v) = cong (x `p`) $ sym m.rightNeutral

0 pprepend :
     (m   : Monoid a z p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> (ts  : List (Term a as))
  -> (t   : Term a as)
  -> eterm t `p` elist m ts === elist m (prepend m isZ ts t)
pprepend m isZ [] (TVar x y) = Refl
pprepend m isZ [] (TLit lit) with (isZ lit)
  pprepend m isZ [] (TLit lit) | Nothing  = Refl
  pprepend m isZ [] (TLit lit) | Just prf = Calc $
    |~ lit `p` z
    ~~ z `p` z   ... cong (`p` z) prf
    ~~ z         ... m.leftNeutral
pprepend m isZ (x :: xs) t = Calc $
  |~ eterm t `p` (eterm x `p` elist m xs)
  ~~ (eterm t `p` eterm x) `p` elist m xs
     ... m.associative
  ~~ elist m (fuse m isZ t x) `p` elist m xs
     ... cong (`p` elist m xs) (pfuse m isZ t x)
  ~~ elist m (fuse m isZ t x ++ xs)
     ... pelist m (fuse m isZ t x) xs

0 pmerge :
     (m   : Monoid a z p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> (ts  : List (Term a as))
  -> elist m ts === elist m (merge m isZ ts)
pmerge m isZ []        = Refl
pmerge m isZ (x :: xs) = Calc $
   |~ eterm x `p` elist m xs
   ~~ eterm x `p` elist m (merge m isZ xs)
      ... cong (eterm x `p`) (pmerge m isZ xs)
   ~~ elist m (prepend m isZ (merge m isZ xs) x)
      ... pprepend m isZ (merge m isZ xs) x

0 pnormalize :
     (m   : Monoid a z p)
  -> (isZ : (x : a) -> Maybe (x === z))
  -> (e   : Expr a as)
  -> eval m e === elist m (normalize m isZ e)
pnormalize m isZ e = Calc $
  |~ eval m e
  ~~ elist m (flatten e)               ... pflatten m e
  ~~ elist m (merge m isZ $ flatten e) ... pmerge m isZ (flatten e)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

export
0 solve :
     (m     : Monoid a z p)
  -> (isZ   : (x : a) -> Maybe (x === z))
  -> (e1,e2 : Expr a as)
  -> {auto prf : normalize m isZ e1 === normalize m isZ e2}
  -> eval m e1 === eval m e2
solve m isZ e1 e2 = Calc $
  |~ eval m e1
  ~~ elist m (normalize m isZ e1) ... pnormalize m isZ e1
  ~~ elist m (normalize m isZ e2) ... cong (elist m) prf
  ~~ eval m e2                    ..< pnormalize m isZ e2
