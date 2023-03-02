module Control.Relation.Trichotomy

import Control.Relation.ReflexiveClosure
import Data.Either0

%default total

||| Trichotomy formalises the fact that three relations are mutually
||| exclusive. A value of type `Trichotomy' eq lt m n` proofs, that
||| exactly one of the relations `lt m n`, `eq m n`, or `lt n m` holds
||| where `eq` is supposed to be an equivalence relation.
|||
||| All proofs held by a value of type `Trichotomous'` are erased, so
||| at runtime such values get optimized to numbers 0, 1, or 2
||| respectively.
|||
||| For the default case where `eq` is `(===)`, alias `Trichotomy` (without
||| the prime) is provided.
public export
data Trichotomy' : (eq, lt : a -> a -> Type) -> (a -> a -> Type) where
  LT :  {0 eq, lt : a -> a -> Type}
     -> (0 l : lt v w)
     -> (0 e : Not (eq v w))
     -> (0 g : Not (lt w v))
     -> Trichotomy' eq lt v w

  EQ :  {0 eq, lt : a -> a -> Type}
     -> (0 l : Not (lt v w))
     -> (0 e : eq v w)
     -> (0 g : Not (lt w v))
     -> Trichotomy' eq lt v w

  GT :  {0 eq, lt : a -> a -> Type}
     -> (0 l : Not (lt v w))
     -> (0 e : Not (eq v w))
     -> (0 g : lt w v)
     -> Trichotomy' eq lt v w

public export
0 Trichotomy : (lt : a -> a -> Type) -> a -> a -> Type
Trichotomy = Trichotomy' (===)

-- identity at runtim
public export
conIndex : Trichotomy' eq lt m n -> Bits8
conIndex (LT _ _ _) = 0
conIndex (EQ _ _ _) = 1
conIndex (GT _ _ _) = 2

public export %inline
Eq (Trichotomy' eq lt m n) where
  x == y = conIndex x == conIndex y

public export
Ord (Trichotomy' eq lt m n) where
  compare x y = compare (conIndex x) (conIndex y)

public export
Show (Trichotomy' eq lt m n) where
  show (LT _ _ _) = "LT"
  show (EQ _ _ _) = "EQ"
  show (GT _ _ _) = "GT"

public export
toOrdering : Trichotomy' eq lt m n -> Ordering
toOrdering (LT _ _ _) = LT
toOrdering (EQ _ _ _) = EQ
toOrdering (GT _ _ _) = GT

public export
swap : Symmetric a eq => Trichotomy' eq lt m n -> Trichotomy' eq lt n m
swap (LT l e g) = GT g (\x => e $ symmetric x) l
swap (EQ l e g) = EQ g (symmetric e) l
swap (GT l e g) = LT g (\x => e $ symmetric x) l

--------------------------------------------------------------------------------
--          Trichotomous
--------------------------------------------------------------------------------

public export
interface Equivalence a eq =>
  Trichotomous (0 a : Type) (0 eq,rel : a -> a -> Type) | rel where
  constructor MkTrichotomous
  trichotomy : (m,n : a) -> Trichotomy' eq rel m n

  eqLeft : {0 x,y,z : a} -> eq x y -> rel y z -> rel x z

  eqRight : {0 x,y,z : a} -> rel x y -> eq y z -> rel x z

public export
interface Transitive a rel => Trichotomous a eq rel => Strict a eq rel where
  constructor MkStrict

public export
Trichotomous a eq rel => Antisymmetric a rel where
  antisymmetric q p = case trichotomy x y of
    LT _ _ g   => void $ g p
    EQ f _ _   => void $ f q
    GT f _ _   => void $ f q

public export
0 irreflexive : {x : _} -> Trichotomous a eq rel => rel x x -> Void
irreflexive lt = case trichotomy x x of
  LT _ g _   => g reflexive
  EQ f _ _   => f lt
  GT f _ _   => f lt

public export
Trichotomous a (===) rel => Antisymmetric a (ReflexiveClosure rel) where
  antisymmetric _        Refl   = Refl
  antisymmetric Refl     _      = Refl
  antisymmetric (Rel q) (Rel p) = case trichotomy x y of
    LT _ _ g   => void $ g p
    EQ f _ _   => void $ f q
    GT f _ _   => void $ f q

--------------------------------------------------------------------------------
--          Corollaries
--------------------------------------------------------------------------------

parameters {0 eq : a -> a -> Type}
           {0 rel : a -> a -> Type}
           {auto tri : Trichotomous a eq rel}

  ||| `m < n` implies `Not (m > n)`.
  export
  0 Not_LT_and_GT : rel m n -> Not (rel n m)
  Not_LT_and_GT {m} {n} isLT isGT = case trichotomy m n of
    LT _ _ g => g isGT
    EQ _ _ g => g isGT
    GT l _ _ => l isLT

  ||| `m < n` implies `Not (m === n)`.
  export
  0 Not_LT_and_EQ : rel m n -> Not (eq m n)
  Not_LT_and_EQ  {m} {n} isLT isEQ = case trichotomy m n of
    LT _ e _ => e isEQ
    EQ l _ _ => l isLT
    GT _ e _ => e isEQ

  ||| `m < n` implies `Not (m >= n)`.
  export
  0 Not_LT_and_GTE : rel m n -> Not (ReflexiveClosure rel n m)
  Not_LT_and_GTE l (Rel prf) = Not_LT_and_GT l prf
  Not_LT_and_GTE l Refl      = Not_LT_and_EQ l reflexive
