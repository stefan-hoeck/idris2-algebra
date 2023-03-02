module Data.Pair.First

import public Control.Order
import public Control.Relation
import public Control.Relation.Trichotomy

%default total

||| Relations on the first projection of a pair.
public export
data First : (rel : a -> a -> Type) -> Pair a b -> Pair a b -> Type where
  Fst :
       {0 a,b : _}
    -> {0 x,y : a}
    -> {0 b1,b2 : b}
    -> {0 rel : a -> a -> Type}
    -> (0 prf : rel x y)
    -> First rel (x,b1) (y,b2)

public export
0 unFirst : First rel (x,b1) (y,b2) -> rel x y
unFirst (Fst r) = r

refl : Reflexive a rel => First rel p p
refl {p = (x,y)} = Fst reflexive

trans : Transitive a rel => First rel x y -> First rel y z -> First rel x z
trans (Fst p) (Fst q) = Fst (transitive p q)

public export
Reflexive a rel => Reflexive (Pair a b) (First rel) where
  reflexive = refl

public export
Transitive a rel => Transitive (Pair a b) (First rel) where
  transitive (Fst p) (Fst q) = Fst (transitive p q)

public export
Symmetric a rel => Symmetric (Pair a b) (First rel) where
  symmetric (Fst p) = Fst $ symmetric p

public export
Equivalence a rel => Equivalence (Pair a b) (First rel) where

public export
comp :
     Trichotomous a eq rel
  => (x,y : Pair a b)
  -> Trichotomy' (First eq) (First rel) x y
comp (x,b1) (y,b2) = case trichotomy {rel} x y of
  LT l e g => LT (Fst l) (e . unFirst) (g . unFirst)
  EQ l e g => EQ (l . unFirst) (Fst e) (g . unFirst)
  GT l e g => GT (l . unFirst) (e . unFirst) (Fst g)

public export %inline
Trichotomous a eq rel => Trichotomous (Pair a b) (First eq) (First rel) where
  trichotomy = comp
  eqLeft (Fst e) (Fst r) = Fst (eqLeft e r)
  eqRight (Fst r) (Fst e) = Fst (eqRight r e)
