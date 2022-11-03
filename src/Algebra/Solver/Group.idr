module Algebra.Solver.Group

import public Data.List.Elem
import public Algebra.Group
import Syntax.PreorderReasoning

%default total

infixl 8 .+>, <+., .+.

public export
data Sng : (a : Type) -> (as : List a) -> Type where
  SLit : (lit : a) -> Sng a as
  SVar : (x : a) -> Elem x as -> Sng a as
  SNeg : (x : a) -> Elem x as -> Sng a as

public export
data Expr : (a : Type) -> (as : List a) -> Type where
  Lit     : (lit : a) -> Expr a as
  Var     : (x : a) -> Elem x as -> Expr a as
  Neutral : Expr a as
  Neg     : Expr a as -> Expr a as
  (<+>)   : Expr a as -> Expr a as -> Expr a as

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

public export
eval :
     (z   : a)
  -> (neg : a -> a)
  -> (app : a -> a -> a)
  -> Expr a as
  -> a
eval z neg app (Lit lit) = lit
eval z neg app (Var x _) = x
eval z neg app Neutral   = z
eval z neg app (Neg x)   = neg (eval z neg app x)
eval z neg app (x <+> y) = app (eval z neg app x) (eval z neg app y)

public export
esng : (neg : a -> a) -> Sng a as -> a
esng neg (SLit lit) = lit
esng neg (SVar x y) = x
esng neg (SNeg x y) = neg x

public export
elist :
     (z   : a)
  -> (neg : a -> a)
  -> (app : a -> a -> a)
  -> List (Sng a as)
  -> a
elist z neg app []        = z
elist z neg app (x :: xs) = esng neg x `app` elist z neg app xs

--------------------------------------------------------------------------------
--          Compare Elem
--------------------------------------------------------------------------------

public export
eqElem : (e1 : Elem x xs) -> (e2 : Elem y xs) -> Maybe (e1 ~=~ e2)
eqElem Here Here      = Just Refl
eqElem Here (There z) = Nothing
eqElem (There z) Here = Nothing
eqElem (There z) (There w) = case eqElem z w of
  Just Refl => Just Refl
  Nothing   => Nothing

--------------------------------------------------------------------------------
--          Normalize
--------------------------------------------------------------------------------

public export
negSng : (neg : a -> a) -> Sng a as -> Sng a as
negSng neg (SLit lit) = SLit $ neg lit
negSng neg (SVar x y) = SNeg x y
negSng neg (SNeg x y) = SVar x y

public export
negate : (neg : a -> a) -> List (Sng a as) -> List (Sng a as) -> List (Sng a as)
negate neg xs []        = xs
negate neg xs (y :: ys) = negate neg (negSng neg y :: xs) ys

public export
flatten : (neg : a -> a) -> Expr a as -> List (Sng a as)
flatten _   (Lit lit) = [SLit lit]
flatten _   (Var x y) = [SVar x y]
flatten _   Neutral   = []
flatten neg (Neg x)   = negate neg [] (flatten neg x)
flatten neg (x <+> y) = flatten neg x ++ flatten neg y

public export
merge :
     (z   : a)
  -> (neg : a -> a)
  -> (app : a -> a -> a)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> List (Sng a as)
  -> List (Sng a as)
merge z neg app isZ []        = []
merge z neg app isZ (SLit lit :: xs) = case isZ lit of
  Just prf => merge z neg app isZ xs
  Nothing  => case merge z neg app isZ xs of
    SLit v :: xs => case isZ $ app lit v of
      Just prf => xs
      Nothing  => SLit (app lit v) :: xs
    xs           => SLit lit :: xs
merge z neg app isZ (SVar x y :: xs) = case merge z neg app isZ xs of
  SNeg x2 y2 :: xs => case eqElem y y2 of
    Just Refl => xs
    Nothing   => SVar x y :: SNeg x2 y2 :: xs
  xs               => SVar x y :: xs
merge z neg app isZ (SNeg x y :: xs) = case merge z neg app isZ xs of
  SVar x2 y2 :: xs => case eqElem y y2 of
    Just Refl => xs
    Nothing   => SNeg x y :: SVar x2 y2 :: xs
  xs               => SNeg x y :: xs

public export
normalize :
     (z   : a)
  -> (neg : a -> a)
  -> (app : a -> a -> a)
  -> (isZ : (v : a) -> Maybe (v === z))
  -> Expr a as
  -> List (Sng a as)
normalize z neg app isZ e = merge z neg app isZ (flatten neg e)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 pnegSng :
     Group a z i p
  -> (s : Sng a as)
  -> i (esng i s) === esng i (negSng i s)
pnegSng g (SLit lit) = Refl
pnegSng g (SVar x y) = Refl
pnegSng g (SNeg x y) = inverseInverse g

0 pnegate' :
     Group a z i p
  -> (vs : List (Sng a as))
  -> (ws : List (Sng a as))
  -> i (elist z i p ws) `p` elist z i p vs === elist z i p (negate i vs ws)
pnegate' g vs []        = Calc $
  |~ p (i z) (elist z i p vs)
  ~~ p z     (elist z i p vs) ... cong (`p` elist z i p vs) (inverseZero g)
  ~~ elist z i p vs           ... g.leftNeutral
pnegate' g vs (w :: ws) = Calc $
  |~ i (esng i w `p` elist z i p ws) `p` elist z i p vs
  ~~ (i (elist z i p ws) `p` (i (esng i w)) `p` elist z i p vs)
     ... cong ( `p` elist z i p vs) (invertProduct g)
  ~~ i (elist z i p ws) `p` (i (esng i w) `p` elist z i p vs)
     ..< g.associative
  ~~ i (elist z i p ws) `p` (esng i (negSng i w) `p` elist z i p vs)
     ... cong (\v => i (elist z i p ws) `p` (v `p` elist z i p vs)) (pnegSng g w)
  ~~ i (elist z i p ws) `p` elist z i p (negSng i w :: vs)
     ... cong (i (elist z i p ws) `p`) Refl
  ~~ elist z i p (negate i (negSng i w :: vs) ws)
     ... pnegate' g (negSng i w :: vs) ws

0 pnegate :
     Group a z i p
  -> (ws : List (Sng a as))
  -> i (elist z i p ws) === elist z i p (negate i [] ws)
pnegate g ws = Calc $
  |~ i (elist z i p ws)
  ~~ i (elist z i p ws) `p` z                   ..< g.rightNeutral
  ~~ i (elist z i p ws) `p` elist {as} z i p [] ... Refl
  ~~ elist z i p (negate i [] ws)               ... pnegate' g [] ws

0 pelist :
     Group a z i p
  -> (vs,ws : List (Sng a as))
  -> elist z i p vs `p` elist z i p ws === elist z i p (vs ++ ws)
pelist g []        ws = g.leftNeutral
pelist g (v :: vs) ws = Calc $
  |~ (esng i v `p` elist z i p vs) `p` elist z i p ws
  ~~ esng i v `p` (elist z i p vs `p` elist z i p ws)
     ..< g.associative
  ~~ esng i v `p` elist z i p (vs ++ ws)
     ... cong (esng i v `p`) (pelist g vs ws)

0 pflatten :
     Group a z i p
  -> (e : Expr a as)
  -> eval z i p e === elist z i p (flatten i e)
pflatten g (Lit lit) = sym g.rightNeutral
pflatten g (Var x y) = sym g.rightNeutral
pflatten g Neutral   = Refl
pflatten g (Neg x)   = Calc $
  |~ i (eval z i p x)
  ~~ i (elist z i p (flatten i x))           ... cong i (pflatten g x)
  ~~ elist z i p (negate i [] (flatten i x)) ... pnegate g (flatten i x)
pflatten g (x <+> y) = Calc $
  |~ eval z i p x `p` eval z i p y
  ~~ elist z i p (flatten i x) `p` eval z i p y
     ... cong (`p` eval z i p y) (pflatten g x)
  ~~ elist z i p (flatten i x) `p` elist z i p (flatten i y)
     ... cong (elist z i p (flatten i x) `p`) (pflatten g y)
  ~~ elist z i p (flatten i x ++ flatten i y)
     ... pelist g (flatten i x) (flatten i y)

0 pmerge :
     Group a z i p
  -> (isZ : (x : a) -> Maybe (x === z))
  -> (vs : List (Sng a as))
  -> elist z i p vs === elist z i p (merge z i p isZ vs)
pmerge g isZ []        = Refl

pmerge g isZ (SLit lit :: xs) with (isZ lit)
  pmerge g isZ (SLit lit :: xs) | Just prf  = Calc $
    |~ lit `p` elist z i p xs
    ~~ z `p` elist z i p xs             ... cong (`p` elist z i p xs) prf
    ~~ elist z i p xs                   ... g.leftNeutral
    ~~ elist z i p (merge z i p isZ xs) ... pmerge g isZ xs

  pmerge g isZ (SLit lit :: xs) | Nothing   with (merge z i p isZ xs) proof mrg
    pmerge g isZ (SLit lit :: xs) | Nothing | [] = Calc $
      |~ lit `p` elist z i p xs
      ~~ lit `p` elist z i p (merge z i p isZ xs)
         ... cong (lit `p`) (pmerge g isZ xs)
      ~~ lit `p` elist {as} z i p []
         ... cong (\x => lit `p` elist z i p x) mrg
    pmerge g isZ (SLit lit :: xs) | Nothing | (SLit x   :: ys) with (isZ (lit `p` x))
      pmerge g isZ (SLit lit :: xs) | Nothing | (SLit x   :: ys) | Just prf = Calc $
        |~ lit `p` elist z i p xs
        ~~ lit `p` elist z i p (merge z i p isZ xs)
           ... cong (lit `p`) (pmerge g isZ xs)
        ~~ lit `p` elist z i p (SLit x :: ys)
           ... cong (\x => lit `p` elist z i p x) mrg
        ~~ (lit `p` x) `p` elist z i p ys
           ... g.associative
        ~~ z `p` elist z i p ys
           ... cong (`p` elist z i p ys) prf
        ~~ elist z i p ys ... g.leftNeutral
      pmerge g isZ (SLit lit :: xs) | Nothing | (SLit x   :: ys) | Nothing  = Calc $
        |~ lit `p` elist z i p xs
        ~~ lit `p` elist z i p (merge z i p isZ xs)
           ... cong (lit `p`) (pmerge g isZ xs)
        ~~ lit `p` elist z i p (SLit x :: ys)
           ... cong (\x => lit `p` elist z i p x) mrg
        ~~ (lit `p` x) `p` elist z i p ys
           ... g.associative
    pmerge g isZ (SLit lit :: xs) | Nothing | (SVar x y :: ys) = Calc $
      |~ lit `p` elist z i p xs
      ~~ lit `p` elist z i p (merge z i p isZ xs)
         ... cong (lit `p`) (pmerge g isZ xs)
      ~~ lit `p` elist z i p (SVar x y :: ys)
         ... cong (\x => lit `p` elist z i p x) mrg
    pmerge g isZ (SLit lit :: xs) | Nothing | (SNeg x y :: ys) = Calc $
      |~ lit `p` elist z i p xs
      ~~ lit `p` elist z i p (merge z i p isZ xs)
         ... cong (lit `p`) (pmerge g isZ xs)
      ~~ lit `p` elist z i p (SNeg x y :: ys)
         ... cong (\x => lit `p` elist z i p x) mrg

pmerge g isZ (SVar x y :: xs) with (merge z i p isZ xs) proof mrg
  pmerge g isZ (SVar x y :: xs) | [] = Calc $
    |~ x `p` elist z i p xs
    ~~ x `p` elist z i p (merge z i p isZ xs)
       ... cong (x `p`) (pmerge g isZ xs)
    ~~ x `p` elist {as} z i p []
       ... cong (\q => x `p` elist z i p q) mrg
  pmerge g isZ (SVar x y :: xs) | (SLit lit :: ys) = Calc $
    |~ x `p` elist z i p xs
    ~~ x `p` elist z i p (merge z i p isZ xs)
       ... cong (x `p`) (pmerge g isZ xs)
    ~~ x `p` elist z i p (SLit lit :: ys)
       ... cong (\q => x `p` elist z i p q) mrg
  pmerge g isZ (SVar x y :: xs) | (SVar w v :: ys) = Calc $
    |~ x `p` elist z i p xs
    ~~ x `p` elist z i p (merge z i p isZ xs)
       ... cong (x `p`) (pmerge g isZ xs)
    ~~ x `p` elist z i p (SVar w v :: ys)
       ... cong (\q => x `p` elist z i p q) mrg
  pmerge g isZ (SVar x y :: xs) | (SNeg w v :: ys) with (eqElem y v)
    pmerge g isZ (SVar x y :: xs) | (SNeg w v :: ys) | Nothing = Calc $
      |~ x `p` elist z i p xs
      ~~ x `p` elist z i p (merge z i p isZ xs)
         ... cong (x `p`) (pmerge g isZ xs)
      ~~ x `p` elist z i p (SNeg w v :: ys)
         ... cong (\q => x `p` elist z i p q) mrg
    pmerge g isZ (SVar x y :: xs) | (SNeg x y :: ys) | (Just Refl) = Calc $
      |~ x `p` elist z i p xs
      ~~ x `p` elist z i p (merge z i p isZ xs)
         ... cong (x `p`) (pmerge g isZ xs)
      ~~ x `p` elist z i p (SNeg x y :: ys)
         ... cong (\q => x `p` elist z i p q) mrg
      ~~ (x `p` i x) `p` elist z i p ys
         ... g.associative
      ~~ z `p` elist z i p ys
         ... cong (`p` elist z i p ys) g.rightInverse
      ~~ elist z i p ys
         ... g.leftNeutral

pmerge g isZ (SNeg x y :: xs) with (merge z i p isZ xs) proof mrg
  pmerge g isZ (SNeg x y :: xs) | [] = Calc $
    |~ i x `p` elist z i p xs
    ~~ i x `p` elist z i p (merge z i p isZ xs)
       ... cong (i x `p`) (pmerge g isZ xs)
    ~~ i x `p` elist {as} z i p []
       ... cong (\q => i x `p` elist z i p q) mrg
  pmerge g isZ (SNeg x y :: xs) | (SLit lit :: ys) = Calc $
    |~ i x `p` elist z i p xs
    ~~ i x `p` elist z i p (merge z i p isZ xs)
       ... cong (i x `p`) (pmerge g isZ xs)
    ~~ i x `p` elist z i p (SLit lit :: ys)
       ... cong (\q => i x `p` elist z i p q) mrg
  pmerge g isZ (SNeg x y :: xs) | (SVar w v :: ys) with (eqElem y v)
    pmerge g isZ (SNeg x y :: xs) | (SVar w v :: ys) | Nothing = Calc $
      |~ i x `p` elist z i p xs
      ~~ i x `p` elist z i p (merge z i p isZ xs)
         ... cong (i x `p`) (pmerge g isZ xs)
      ~~ i x `p` elist z i p (SVar w v :: ys)
         ... cong (\q => i x `p` elist z i p q) mrg
    pmerge g isZ (SNeg x y :: xs) | (SVar x y :: ys) | (Just Refl) = Calc $
      |~ i x `p` elist z i p xs
      ~~ i x `p` elist z i p (merge z i p isZ xs)
         ... cong (i x `p`) (pmerge g isZ xs)
      ~~ i x `p` elist z i p (SVar x y :: ys)
         ... cong (\q => i x `p` elist z i p q) mrg
      ~~ (i x `p` x) `p` elist z i p ys
         ... g.associative
      ~~ z `p` elist z i p ys
         ... cong (`p` elist z i p ys) g.leftInverse
      ~~ elist z i p ys
         ... g.leftNeutral
  pmerge g isZ (SNeg x y :: xs) | (SNeg w v :: ys) = Calc $
    |~ i x `p` elist z i p xs
    ~~ i x `p` elist z i p (merge z i p isZ xs)
       ... cong (i x `p`) (pmerge g isZ xs)
    ~~ i x `p` elist z i p (SNeg w v :: ys)
       ... cong (\q => i x `p` elist z i p q) mrg

0 pnormalize :
     Group a z i p
  -> (isZ : (x : a) -> Maybe (x === z))
  -> (e : Expr a as)
  -> eval z i p e === elist z i p (normalize z i p isZ e)
pnormalize g isZ e = Calc $
  |~ eval z i p e
  ~~ elist z i p (flatten i e)                   ... pflatten g e
  ~~ elist z i p (merge z i p isZ $ flatten i e) ... pmerge g isZ (flatten i e)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

export
0 solve :
     Group a z i p
  -> (isZ : (x : a) -> Maybe (x === z))
  -> (e1,e2 : Expr a as)
  -> {auto prf : normalize z i p isZ e1 === normalize z i p isZ e2}
  -> eval z i p e1 === eval z i p e2
solve g isZ e1 e2 = Calc $
  |~ eval z i p e1
  ~~ elist z i p (normalize z i p isZ e1) ... pnormalize g isZ e1
  ~~ elist z i p (normalize z i p isZ e2) ... cong (elist z i p) prf
  ~~ eval z i p e2                        ..< pnormalize g isZ e2
