module Control.Relation.Trichotomy

import Control.Relation.ReflexiveClosure
import Data.Either0

%default total

||| Trichotomy formalises the fact that three relations are mutually
||| exclusive. A value of type `Trichotomy lt m n` proofs, that
||| exactly one of the relations `lt m n`, `m === n`, or `lt n m` holds.
|||
||| All proofs held by a value of type `Trichotomous` are erased, so
||| at runtime such values get optimized to numbers 0, 1, or 2
||| respectively.
public export
data Trichotomy : (lt : a -> a -> Type) -> (a -> a -> Type) where
  LT :  {0 lt : a -> a -> Type}
     -> (0 l : lt v w)
     -> (0 e : Not (v === w))
     -> (0 g : Not (lt w v))
     -> Trichotomy lt v w

  EQ :  {0 lt : a -> a -> Type}
     -> (0 l : Not (lt v w))
     -> (0 e : v === w)
     -> (0 g : Not (lt w v))
     -> Trichotomy lt v w

  GT :  {0 lt : a -> a -> Type}
     -> (0 l : Not (lt v w))
     -> (0 e : Not (v === w))
     -> (0 g : lt w v)
     -> Trichotomy lt v w

-- identity at runtim
public export
conIndex : Trichotomy lt m n -> Bits8
conIndex (LT _ _ _) = 0
conIndex (EQ _ _ _) = 1
conIndex (GT _ _ _) = 2

public export %inline
Eq (Trichotomy lt m n) where
  x == y = conIndex x == conIndex y

public export
Ord (Trichotomy lt m n) where
  compare x y = compare (conIndex x) (conIndex y)

public export
Show (Trichotomy lt m n) where
  show (LT _ _ _) = "LT"
  show (EQ _ _ _) = "EQ"
  show (GT _ _ _) = "GT"

public export
toOrdering : Trichotomy lt m n -> Ordering
toOrdering (LT _ _ _) = LT
toOrdering (EQ _ _ _) = EQ
toOrdering (GT _ _ _) = GT

public export
swap : Trichotomy lt m n -> Trichotomy lt n m
swap (LT l e g) = GT g (\x => e $ sym x) l
swap (EQ l e g) = EQ g (sym e) l
swap (GT l e g) = LT g (\x => e $ sym x) l

--------------------------------------------------------------------------------
--          Trichotomous
--------------------------------------------------------------------------------

public export
interface Trichotomous (0 a : Type) (0 rel : a -> a -> Type) | rel where
  constructor MkTrichotomous
  trichotomy : (m,n : a) -> Trichotomy rel m n

public export
interface Transitive a rel => Trichotomous a rel => Strict a rel where
  constructor MkStrict

public export
Trichotomous a rel => Antisymmetric a rel where
  antisymmetric q p = case trichotomy x y of
    LT _ _ g   => void $ g p
    EQ f _ _   => void $ f q
    GT f _ _   => void $ f q

public export
Trichotomous a rel => Antisymmetric a (ReflexiveClosure rel) where
  antisymmetric _        Refl   = Refl
  antisymmetric Refl     _      = Refl
  antisymmetric (Rel q) (Rel p) = case trichotomy x y of
    LT _ _ g   => void $ g p
    EQ f _ _   => void $ f q
    GT f _ _   => void $ f q

--------------------------------------------------------------------------------
--          Corollaries
--------------------------------------------------------------------------------

||| `m < n` implies `Not (m > n)`.
export
0 Not_LT_and_GT : Trichotomous a lt => lt m n -> Not (lt n m)
Not_LT_and_GT isLT isGT = case trichotomy m n of
  LT _ _ g => g isGT
  EQ _ _ g => g isGT
  GT l _ _ => l isLT

||| `m < n` implies `Not (m === n)`.
export
0 Not_LT_and_EQ : Trichotomous a lt => lt m n -> Not (m === n)
Not_LT_and_EQ  isLT isEQ = case trichotomy m n of
  LT _ e _ => e isEQ
  EQ l _ _ => l isLT
  GT _ e _ => e isEQ

||| `m < n` implies `Not (m >= n)`.
export
0 Not_LT_and_GTE : Trichotomous a lt => lt m n -> Not (ReflexiveClosure lt n m)
Not_LT_and_GTE l (Rel prf) = Not_LT_and_GT l prf
Not_LT_and_GTE l Refl      = Not_LT_and_EQ l Refl
