module Data.Pair.Second

import public Control.Order
import public Control.Relation
import public Control.Relation.Trichotomy

%default total

||| Relations on the second projection of a pair.
public export
data Second : (rel : b -> b -> Type) -> Pair a b -> Pair a b -> Type where
  Snd :
       {0 a,b : _}
    -> {0 a1,a2 : a}
    -> {0 x,y : b}
    -> {0 rel : b -> b -> Type}
    -> (0 prf : rel x y)
    -> Second rel (a1,x) (a2,y)

public export
0 unSecond : Second rel (a1,x) (a2,y) -> rel x y
unSecond (Snd r) = r

refl : Reflexive a rel => Second rel p p
refl {p = (x,y)} = Snd reflexive

public export
Reflexive b rel => Reflexive (Pair a b) (Second rel) where
  reflexive = refl

public export
Transitive b rel => Transitive (Pair a b) (Second rel) where
  transitive (Snd p) (Snd q) = Snd (transitive p q)

public export
Symmetric b rel => Symmetric (Pair a b) (Second rel) where
  symmetric (Snd p) = Snd $ symmetric p

public export
Equivalence b rel => Equivalence (Pair a b) (Second rel) where

public export
comp :
     Trichotomous b eq rel
  => (x,y : Pair a b)
  -> Trichotomy' (Second eq) (Second rel) x y
comp (b1,x) (b2,y) = case trichotomy {rel} x y of
  LT l e g => LT (Snd l) (e . unSecond) (g . unSecond)
  EQ l e g => EQ (l . unSecond) (Snd e) (g . unSecond)
  GT l e g => GT (l . unSecond) (e . unSecond) (Snd g)

public export %inline
Trichotomous b eq rel => Trichotomous (Pair a b) (Second eq) (Second rel) where
  trichotomy = comp
  eqLeft (Snd e) (Snd r) = Snd (eqLeft e r)
  eqRight (Snd r) (Snd e) = Snd (eqRight r e)
