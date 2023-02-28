module Data.Maybe.Upper

import Control.Function
import Data.Maybe
import Control.Relation
import Control.Relation.Trichotomy

%default total

||| A total order for `Maybe a` where `a` has a total order
||| and `Nothing` is the maximal value.
|||
||| This is useful, for instance, when implementing provably
||| sorted (assoc-) lists, indexed by a `Maybe key`, where
||| the empty list has a `Nothing` index:
|||
||| ```idris example
||| data AssocList : (ix : Maybe Bits8) -> (a : Type) -> Type where
|||   Nil  : AssocList Nothing a
|||   (::) :  (p : (Bits8, a))
|||        -> (ps : AssocList ix a)
|||        -> (0 prf : Upper (<) (Just $ fst p) ix)
|||        => AssocList (Just $ fst p) a
||| ```
public export
data Upper : (lt : a -> a -> Type) -> (m1,m2 : Maybe a) -> Type where
  UNothing : Upper lt (Just v) Nothing
  UJust    :  {0 lt : a -> a -> Type}
           -> {0 v, w : a}
           -> lt v w -> Upper lt (Just v) (Just w)

public export
Uninhabited (Upper lt Nothing m) where
  uninhabited UNothing impossible
  uninhabited (UJust _) impossible

public export
Strict a lt => Uninhabited (Upper lt (Just k) (Just k)) where
  uninhabited UNothing impossible
  uninhabited (UJust refl) = void (irreflexive refl)

public export
fromLT : Upper lt (Just a) (Just b) -> lt a b
fromLT (UJust x) = x

||| Implementation and alias for `trichotomy`.
export
comp : Trichotomous a lt => (m1,m2 : Maybe a) -> Trichotomy (Upper lt) m1 m2
comp (Just x) (Just y) = case trichotomy {rel = lt} x y of
  LT p c1 c2 => LT (UJust p) (\r => c1 (injective r)) (\x => c2 (fromLT x))
  EQ c1 p c2 => EQ (\x => c1 (fromLT x)) (cong Just p) (\x => c2 (fromLT x))
  GT c1 c2 p => GT (\x => c1 (fromLT x)) (\r => c2 (injective r)) (UJust p)
comp (Just x) Nothing  = LT UNothing absurd absurd
comp Nothing  (Just y) = GT absurd absurd UNothing
comp Nothing  Nothing  = EQ absurd Refl absurd

||| If `lt` is a total order of `a`, then `Upper lt` is a
||| total order of `Maybe a`.
export %inline
Trichotomous a lt => Trichotomous (Maybe a) (Upper lt) where
  trichotomy = comp

export %inline
Transitive a lt => Transitive (Maybe a) (Upper lt) where
  transitive (UJust x) UNothing  = UNothing
  transitive (UJust x) (UJust y) = UJust $ transitive x y
  transitive UNothing  y         = absurd y
