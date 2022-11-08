module Algebra.Solver.Group

import Syntax.PreorderReasoning

import public Algebra.Group
import public Algebra.Solver.Ops
import public Data.List.Elem

%default total

public export
data Expr : (a : Type) -> (as : List a) -> Type where
  Lit     : (lit : a) -> Expr a as
  Var     : (x : a) -> Elem x as -> Expr a as
  Neutral : Expr a as
  Neg     : Expr a as -> Expr a as
  (<+>)   : Expr a as -> Expr a as -> Expr a as

public export
data Term : (a : Type) -> (as : List a) -> Type where
  TLit : (lit : a) -> Term a as
  TVar : (x : a) -> Elem x as -> Term a as
  TNeg : (x : a) -> Elem x as -> Term a as

--------------------------------------------------------------------------------
--          Syntax
--------------------------------------------------------------------------------

public export %inline
(.+>) : (x : a) -> Expr a xs -> {auto p : Elem x xs} -> Expr a xs
(.+>) x y = Var x p <+> y

public export %inline
(<+.) : Expr a xs -> (x : a) -> {auto p : Elem x xs} -> Expr a xs
(<+.) x y = x <+> Var y p

public export %inline
(.+.) :
     (x,y : a)
  -> {auto p : Elem x xs}
  -> {auto q : Elem y xs}
  -> Expr a xs
(.+.) x y = Var x p <+> Var y q

public export %inline
var : (x : a) -> {auto p : Elem x xs} -> Expr a xs
var x = Var x p

public export %inline
neg : (x : a) -> {auto p : Elem x xs} -> Expr a xs
neg x = Neg $ var x

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

||| Evaluates an expression over the given group.
||| Note: The idea is to use this function at compile-time to
|||       convert the expression we evaluate to the corresponding
|||       Idris expression.
public export
eval :
     {z : a}
  -> {i : a -> a}
  -> {p : a -> a -> a}
  -> (0 g : Group a z i p)
  -> Expr a as
  -> a
eval g (Lit lit) = lit
eval g (Var x _) = x
eval g Neutral   = z
eval g (Neg x)   = i (eval g x)
eval g (x <+> y) = eval g x `p` eval g y

||| Evaluates a single term.
public export
eterm : (i : a -> a) -> Term a as -> a
eterm i (TLit lit) = lit
eterm i (TVar x y) = x
eterm i (TNeg x y) = i x

||| Evaluates a list of terms over the given monoid.
public export
elist :
     {z : a}
  -> {i : a -> a}
  -> {p : a -> a -> a}
  -> (0 g : Group a z i p)
  -> List (Term a as)
  -> a
elist g []        = z
elist g (x :: xs) = eterm i x `p` elist g xs

--------------------------------------------------------------------------------
--          Normalize
--------------------------------------------------------------------------------

||| Negates a single term.
public export
negSng : (i : a -> a) -> Term a as -> Term a as
negSng i (TLit lit) = TLit $ i lit
negSng i (TVar x y) = TNeg x y
negSng i (TNeg x y) = TVar x y

||| Negates a list of terms using the given inverse function.
|||
||| This will - according to the usual group laws -
||| invert the order of elements.
public export
negate : (i : a -> a) -> List (Term a as) -> List (Term a as) -> List (Term a as)
negate i xs []        = xs
negate i xs (y :: ys) = negate i (negSng i y :: xs) ys

||| Flattens an expression into a list of terms, using the given inverse
||| function for negation.
public export
flatten : (i : a -> a) -> Expr a as -> List (Term a as)
flatten _ (Lit lit) = [TLit lit]
flatten _ (Var x y) = [TVar x y]
flatten _ Neutral   = []
flatten i (Neg x)   = negate i [] (flatten i x)
flatten i (x <+> y) = flatten i x ++ flatten i y

||| Tries to fuse two neighbouring terms
public export
fuse :
     {z   : a}
  -> {i   : a -> a}
  -> {p   : a -> a -> a}
  -> (0 g : Group a z i p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> Term a as
  -> Term a as
  -> List (Term a as)
fuse g isZ (TLit lit) (TLit x) = case isZ (lit `p` x) of
  Just _  => []
  Nothing => [TLit $ lit `p` x]
fuse g isZ (TLit lit) t        = case isZ lit of
  Just _  => [t]
  Nothing => [TLit lit, t]
fuse g isZ (TVar x w) (TNeg y v) = case eqElem w v of
  Just prf => []
  Nothing  => [TVar x w, TNeg y v]
fuse g isZ (TVar x w) t          = [TVar x w, t]
fuse g isZ (TNeg x w) (TVar y v) = case eqElem w v of
  Just prf => []
  Nothing  => [TNeg x w, TVar y v]
fuse g isZ (TNeg x w) t          = [TNeg x w, t]

||| Prepends a single term in front of a list of terms.
||| This will remove terms that evaluate to zero and
||| fuse neighbouring literals.
public export
prepend :
     {z   : a}
  -> {i   : a -> a}
  -> {p   : a -> a -> a}
  -> (0 g : Group a z i p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> List (Term a as)
  -> Term a as
  -> List (Term a as)
prepend g isZ []       (TLit x) = case isZ x of
  Just p  => []
  Nothing => [TLit x]
prepend g isZ []        t       = [t]
prepend g isZ (x :: xs) t       = fuse g isZ t x ++ xs

public export
merge :
     {z : a}
  -> {i : a -> a}
  -> {p : a -> a -> a}
  -> (0 g : Group a z i p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> List (Term a as)
  -> List (Term a as)
merge g isZ []        = []
merge g isZ (x :: xs) = prepend g isZ (merge g isZ xs) x

public export
normalize :
     {z   : a}
  -> {i   : a -> a}
  -> {p   : a -> a -> a}
  -> (0 g : Group a z i p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> Expr a as
  -> List (Term a as)
normalize g isZ e = merge g isZ (flatten i e)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 pnegSng :
     Group a z i p
  -> (s : Term a as)
  -> i (eterm i s) === eterm i (negSng i s)
pnegSng g (TLit lit) = Refl
pnegSng g (TVar x y) = Refl
pnegSng g (TNeg x y) = inverseInverse g

0 pnegate' :
     (g  : Group a z i p)
  -> (vs : List (Term a as))
  -> (ws : List (Term a as))
  -> i (elist g ws) `p` elist g vs === elist g (negate i vs ws)
pnegate' g vs []        = Calc $
  |~ p (i z) (elist g vs)
  ~~ p z     (elist g vs) ... cong (`p` elist g vs) (inverseZero g)
  ~~ elist g vs           ... g.leftNeutral
pnegate' g vs (w :: ws) = Calc $
  |~ i (eterm i w `p` elist g ws) `p` elist g vs
  ~~ (i (elist g ws) `p` (i (eterm i w)) `p` elist g vs)
     ... cong ( `p` elist g vs) (invertProduct g)
  ~~ i (elist g ws) `p` (i (eterm i w) `p` elist g vs)
     ..< g.associative
  ~~ i (elist g ws) `p` (eterm i (negSng i w) `p` elist g vs)
     ... cong (\v => i (elist g ws) `p` (v `p` elist g vs)) (pnegSng g w)
  ~~ i (elist g ws) `p` elist g (negSng i w :: vs)
     ... cong (i (elist g ws) `p`) Refl
  ~~ elist g (negate i (negSng i w :: vs) ws)
     ... pnegate' g (negSng i w :: vs) ws

0 pnegate :
     (g  : Group a z i p)
  -> (ws : List (Term a as))
  -> i (elist g ws) === elist g (negate i [] ws)
pnegate g ws = Calc $
  |~ i (elist g ws)
  ~~ i (elist g ws) `p` z               ..< g.rightNeutral
  ~~ i (elist g ws) `p` elist {as} g [] ... Refl
  ~~ elist g (negate i [] ws)           ... pnegate' g [] ws

0 pelist :
     (g : Group a z i p)
  -> (vs,ws : List (Term a as))
  -> elist g vs `p` elist g ws === elist g (vs ++ ws)
pelist g []        ws = g.leftNeutral
pelist g (v :: vs) ws = Calc $
  |~ (eterm i v `p` elist g vs) `p` elist g ws
  ~~ eterm i v `p` (elist g vs `p` elist g ws)
     ..< g.associative
  ~~ eterm i v `p` elist g (vs ++ ws)
     ... cong (eterm i v `p`) (pelist g vs ws)

0 pflatten :
     (g : Group a z i p)
  -> (e : Expr a as)
  -> eval g e === elist g (flatten i e)
pflatten g (Lit lit) = sym g.rightNeutral
pflatten g (Var x y) = sym g.rightNeutral
pflatten g Neutral   = Refl
pflatten g (Neg x)   = Calc $
  |~ i (eval g x)
  ~~ i (elist g (flatten i x))           ... cong i (pflatten g x)
  ~~ elist g (negate i [] (flatten i x)) ... pnegate g (flatten i x)
pflatten g (x <+> y) = Calc $
  |~ eval g x `p` eval g y
  ~~ elist g (flatten i x) `p` eval g y
     ... cong (`p` eval g y) (pflatten g x)
  ~~ elist g (flatten i x) `p` elist g (flatten i y)
     ... cong (elist g (flatten i x) `p`) (pflatten g y)
  ~~ elist g (flatten i x ++ flatten i y)
     ... pelist g (flatten i x) (flatten i y)

0 lemma : (g : Group a z i p) -> {x,y : a} -> x `p` y === x `p` (y `p` z)
lemma g = cong (x `p`) $ sym g.rightNeutral

0 pfuse :
     (g : Group a z i p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> (t1,t2 : Term a as)
  -> eterm i t1 `p` eterm i t2 === elist g (fuse g isZ t1 t2)
pfuse g isZ (TLit lit) (TLit x)   with (isZ $ lit `p` x)
  pfuse g isZ (TLit lit) (TLit x) | Just prf   = prf
  pfuse g isZ (TLit lit) (TLit x) | Nothing    = sym $ g.rightNeutral
pfuse g isZ (TLit lit) (TVar x y) with (isZ lit)
  pfuse g isZ (TLit lit) (TVar x y) | Just prf = Calc $
    |~ lit `p` x
    ~~ z `p` x ... cong (`p` x) prf
    ~~ x       ... g.leftNeutral
    ~~ x `p` z ..< g.rightNeutral
  pfuse g isZ (TLit lit) (TVar x y) | Nothing = lemma g
pfuse g isZ (TLit lit) (TNeg x y) with (isZ lit)
  pfuse g isZ (TLit lit) (TNeg x y) | Just prf = Calc $
    |~ lit `p` i x
    ~~ z `p` i x ... cong (`p` i x) prf
    ~~ i x       ... g.leftNeutral
    ~~ i x `p` z ..< g.rightNeutral
  pfuse g isZ (TLit lit) (TNeg x y) | Nothing = lemma g

pfuse g isZ (TVar x y) (TNeg w v) with (eqElem y v)
  pfuse g isZ (TVar x y) (TNeg x y) | Just Refl = g.rightInverse
  pfuse g isZ (TVar x y) (TNeg w v) | Nothing   = lemma g
pfuse g isZ (TVar x y) (TLit lit) = lemma g
pfuse g isZ (TVar x y) (TVar w v) = lemma g

pfuse g isZ (TNeg x y) (TVar w v) with (eqElem y v)
  pfuse g isZ (TNeg x y) (TVar x y) | Just Refl = g.leftInverse
  pfuse g isZ (TNeg x y) (TVar w v) | Nothing = lemma g
pfuse g isZ (TNeg x y) (TNeg w v) = lemma g
pfuse g isZ (TNeg x y) (TLit lit) = lemma g

0 pprepend :
     (g   : Group a z i p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> (ts  : List (Term a as))
  -> (t   : Term a as)
  -> eterm i t `p` elist g ts === elist g (prepend g isZ ts t)
pprepend g isZ [] (TVar x y) = Refl
pprepend g isZ [] (TNeg x y) = Refl
pprepend g isZ [] (TLit lit) with (isZ lit)
  pprepend g isZ [] (TLit lit) | Nothing  = Refl
  pprepend g isZ [] (TLit lit) | Just prf = Calc $
    |~ lit `p` z
    ~~ z `p` z   ... cong (`p` z) prf
    ~~ z         ... g.leftNeutral
pprepend g isZ (x :: xs) t = Calc $
  |~ eterm i t `p` (eterm i x `p` elist g xs)
  ~~ (eterm i t `p` eterm i x) `p` elist g xs
     ... g.associative
  ~~ elist g (fuse g isZ t x) `p` elist g xs
     ... cong (`p` elist g xs) (pfuse g isZ t x)
  ~~ elist g (fuse g isZ t x ++ xs)
     ... pelist g (fuse g isZ t x) xs

0 pmerge :
     (g   : Group a z i p)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> (ts  : List (Term a as))
  -> elist g ts === elist g (merge g isZ ts)
pmerge g isZ []        = Refl
pmerge g isZ (x :: xs) = Calc $
   |~ eterm i x `p` elist g xs
   ~~ eterm i x `p` elist g (merge g isZ xs)
      ... cong (eterm i x `p`) (pmerge g isZ xs)
   ~~ elist g (prepend g isZ (merge g isZ xs) x)
      ... pprepend g isZ (merge g isZ xs) x

0 pnormalize :
     (g   : Group a z i p)
  -> (isZ : (x : a) -> Maybe (x === z))
  -> (e   : Expr a as)
  -> eval g e === elist g (normalize g isZ e)
pnormalize g isZ e = Calc $
  |~ eval g e
  ~~ elist g (flatten i e)               ... pflatten g e
  ~~ elist g (merge g isZ $ flatten i e) ... pmerge g isZ (flatten i e)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

export
0 solve :
     (g     : Group a z i p)
  -> (isZ   : (x : a) -> Maybe (x === z))
  -> (e1,e2 : Expr a as)
  -> {auto prf : normalize g isZ e1 === normalize g isZ e2}
  -> eval g e1 === eval g e2
solve g isZ e1 e2 = Calc $
  |~ eval g e1
  ~~ elist g (normalize g isZ e1) ... pnormalize g isZ e1
  ~~ elist g (normalize g isZ e2) ... cong (elist g) prf
  ~~ eval g e2                    ..< pnormalize g isZ e2
