module Algebra.Solver.Product

import Algebra.Group
import public Data.List.Elem
import Syntax.PreorderReasoning

%default total

||| A product of variables each represented by the exponent,
||| to which it is raised.
|||
||| When normalizing commutative arithmetic expressions, they often
||| get converted to (sums of) products of variables
||| (listed in index `as`), each raised to a certain
||| exponent. This is the case for commutative monoids
||| (a single product) as well as commutative (semi)rings
||| (a sum of products).
|||
||| Example: Assume the monoid in question is `(Bits8,(+),0)` (addition
|||          of 8-bit numbers). Assume further, that we have variables
|||          `[x,y,z]`. The expression `(x + x) + y + (z + z + z + z)` would
|||          then be represented as `[2,1,4]`
public export
data Prod : (a : Type) -> (as : List a) -> Type where
  Nil  : Prod a []
  (::) : (exp : Nat) -> Prod a xs -> Prod a (x :: xs)

||| Multiplying two products means adding all
||| expontents pairwise.
public export
mult : Prod a as -> Prod a as -> Prod a as
mult []        []        = []
mult (x :: xs) (y :: ys) = (x + y) :: mult xs ys

||| We sort products by lexicographically comparing
||| the exponents.
public export
compProd : Prod a as -> Prod a as -> Ordering
compProd []        []        = EQ
compProd (x :: xs) (y :: ys) = case compare x y of
  LT => LT
  GT => GT
  EQ => compProd xs ys

||| The neutral product where all exponents are zero.
public export
one : {as : List a} -> Prod a as
one {as = []}      = []
one {as = x :: xs} = 0 :: one

||| Convert a single variable to a product of variables.
public export
fromVar : {as : List a} -> Elem x as -> Prod a as
fromVar {as = x :: xs} Here      = 1 :: one
fromVar {as = x :: xs} (There y) = 0 :: fromVar y
fromVar {as = []} Here impossible
fromVar {as = []} (There y) impossible

--------------------------------------------------------------------------------
--          Term
--------------------------------------------------------------------------------

||| A single term in a normalized arithmetic expressions.
|||
||| This is a product of all variables each raised to
||| a given power, multiplied with a constant factor (which is supposed
||| to reduce during elaboration).
|||
||| Example: Assume the monoid in question is `(Bits8,(+),0)` (addition
|||          of 8-bit numbers). Assume further, that we have variables
|||          `[x,y,z]`. The expression `3 + (x + x) + y + (z + z + z + z)` would
|||          then be represented as `T 3 [2,1,4]`
public export
record Term (a : Type) (as : List a) where
  constructor T
  factor : a
  prod   : Prod a as

||| Negates the constant factor in a term using the given negation function.
public export
negTerm : (neg : a -> a) -> Term a as -> Term a as
negTerm neg (T f p) = T (neg f) p

namespace Term

  ||| Multiplies two terms using the given function to multiply the
  ||| constant factors.
  public export
  mult : (p : a -> a -> a) -> Term a as -> Term a as -> Term a as
  mult p (T f1 p1) (T f2 p2) = T (p f1 f2) (mult p1 p2)

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

public export
times : (p : a -> a -> a) -> (n : a) -> Nat -> a -> a
times p n 0     x = n
times p n (S k) x = x `p` times p n k x

public export
eprod : {as : _} -> (p : a -> a -> a) -> (n : a) -> Prod a as -> a
eprod                p n []         = n
eprod {as = v :: vs} p n (exp :: x) = times p n exp v `p` eprod p n x

||| Evaluate a term using the given monoid.
public export
eterm : {as : List a} -> (p : a -> a -> a) -> (n : a) -> Term a as -> a
eterm p n (T f prod) = f `p` eprod p n prod

--------------------------------------------------------------------------------
--          Monoid Proofs
--------------------------------------------------------------------------------

||| A utility proof that is used several times internally
export
0 lemma1324 :
     CommutativeSemigroup a p
  -> {k,l,m,n : a}
  -> (k `p` l) `p` (m `p` n) === (k `p` m) `p` (l `p` n)
lemma1324 c = Calc $
  |~ (k `p` l) `p` (m `p` n)
  ~~ ((k `p` l) `p` m) `p` n ... c.associative
  ~~ (k `p` (l `p` m)) `p` n ..< cong (`p` n) c.associative
  ~~ (k `p` (m `p` l)) `p` n ... cong (\x => (k `p` x) `p` n) c.commutative
  ~~ ((k `p` m) `p` l) `p` n ... cong (`p` n) c.associative
  ~~ (k `p` m) `p` (l `p` n) ..< c.associative

||| A utility proof that is used several times internally
export
0 lemma213 :
     CommutativeSemigroup a p
  -> {k,m,n : a}
  -> k `p` (m `p` n) === m `p` (k `p` n)
lemma213 c = Calc $
  |~ k `p` (m `p` n)
  ~~ (k `p` m) `p` n ... c.associative
  ~~ (m `p` k) `p` n ... cong (`p` n) c.commutative
  ~~ m `p` (k `p` n) ..< c.associative

export
0 ptimes :
     CommutativeMonoid a z p
  -> (m,n : Nat)
  -> (x : a)
  -> times p z m x `p` times p z n x === times p z (m + n) x
ptimes c 0     n x = c.leftNeutral
ptimes c (S k) n x = Calc $
  |~ (x `p` times p z k x) `p` times p z n x
  ~~ x `p` (times p z k x `p` times p z n x) ..< c.associative
  ~~ x `p` (times p z (k + n) x)             ... cong (p x) (ptimes c k n x)

export
0 peprod :
     CommutativeMonoid a z p
  -> (e1,e2 : Prod a as)
  -> eprod p z e1 `p` eprod p z e2 === eprod p z (mult e1 e2)
peprod                c []        []        = c.rightNeutral
peprod {as = v :: vs} c (m :: xs) (n :: ys) = Calc $
  |~ (times p z m v `p` eprod p z xs) `p` (times p z n v `p` eprod p z ys)
  ~~ (times p z m v `p` times p z n v) `p` (eprod p z xs `p` eprod p z ys)
     ... lemma1324 c.csgrp
  ~~ (times p z m v `p` times p z n v) `p` (eprod p z (mult xs ys))
     ... cong (p (times p z m v `p` times p z n v)) (peprod c xs ys)
  ~~ times p z (m + n) v `p` eprod p z (mult xs ys)
     ... cong (`p` eprod p z (mult xs ys)) (ptimes c m n v)

export
0 pappend :
     CommutativeMonoid a z p
  -> (e1,e2 : Term a as)
  -> eterm p z e1 `p` eterm p z e2 === eterm p z (mult p e1 e2)
pappend c (T f v) (T g w) = Calc $
  |~ (f `p` eprod p z v) `p` (g `p` eprod p z w)
  ~~ (f `p` g) `p` (eprod p z v `p` eprod p z w)
     ... lemma1324 c.csgrp
  ~~ (f `p` g) `p` eprod p z (mult v w)
     ... cong ((f `p` g) `p`) (peprod c v w)

||| Proof that `Prod.one` evaluates to `neutral`
export
0 pone :
     CommutativeMonoid a z p
  -> (as : List a)
  -> eprod p z {as} Product.one === z
pone c []        = Refl
pone c (v :: vs) = Calc $
  |~ z `p` eprod p z {as = vs} one
  ~~ z `p` z                       ... cong (z `p`) (pone c vs)
  ~~ z                             ... c.leftNeutral

||| Proof that for `e : Elem x as`, `fromVar e` evaluates to `x`.
export
0 pvar :
     CommutativeMonoid a z p
  -> (as : List a)
  -> (e  : Elem x as)
  -> eprod p z (fromVar {as} e) === x
pvar c (x :: vs) Here      = Calc $
  |~ (x `p` z) `p` eprod p z {as = vs} one
  ~~ (x `p` z) `p` z                       ... cong ((x `p` z) `p`) (pone c vs)
  ~~ x `p` z                               ... c.rightNeutral
  ~~ x                                     ... c.rightNeutral

pvar c (v :: vs) (There y) = Calc $
  |~ z `p` eprod p z (fromVar y)
  ~~ eprod p z (fromVar y)                 ... c.leftNeutral
  ~~ x                                     ... pvar c vs y

pvar c [] Here impossible
pvar c [] (There y) impossible

--------------------------------------------------------------------------------
--          Ordering Proofs
--------------------------------------------------------------------------------

Uninhabited (LT = EQ) where
  uninhabited _ impossible

Uninhabited (GT = EQ) where
  uninhabited _ impossible

export
0 pcompNat : (x,y : Nat) -> (compare x y === EQ) -> x === y
pcompNat 0 0         prf = Refl
pcompNat (S k) (S j) prf = cong S $ pcompNat k j prf
pcompNat 0 (S k) Refl impossible
pcompNat (S k) 0 Refl impossible

export
0 pcompProd :
     (x,y : Prod a as)
  -> (compProd x y === EQ)
  -> x === y
pcompProd []        []        prf = Refl
pcompProd (x :: xs) (y :: ys) prf with (compare x y) proof eq
  _ | EQ = cong2 (::) (pcompNat x y eq) (pcompProd xs ys prf)
  _ | LT = absurd prf
  _ | GT = absurd prf
pcompProd []        (_ :: _)  Refl impossible
pcompProd (_ :: _)  []        Refl impossible

--------------------------------------------------------------------------------
--          Ring Proofs
--------------------------------------------------------------------------------
-- 
-- ||| Evaluating a negated term is equivalent to negate the
-- ||| result of evaluating the term.
-- export
-- 0 pnegTerm :
--      {neg : _}
--   -> Ring a neg
--   => (x : Term a as)
--   -> eterm (negTerm x) === negate (eterm x)
-- pnegTerm (T f p) = multNegLeft
