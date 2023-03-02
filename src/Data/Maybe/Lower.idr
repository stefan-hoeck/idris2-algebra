module Data.Maybe.Lower

import Control.Function
import Data.Maybe
import Control.Relation
import Control.Relation.Trichotomy

%default total

||| A total order for `Maybe a` where `a` has a total order
||| and `Nothing` is the minimal value.
|||
||| This is useful, for instance, when implementing provably
||| sorted (assoc-) snoc-lists, indexed by a `Maybe key`, where
||| the empty list has a `Nothing` index.
public export
data Lower : (lt : a -> a -> Type) -> (m1,m2 : Maybe a) -> Type where
  LNothing : Lower lt Nothing (Just v)
  LJust    :  {0 lt : a -> a -> Type}
           -> {0 v, w : a}
           -> lt v w -> Lower lt (Just v) (Just w)

public export
Uninhabited (Lower lt m Nothing) where
  uninhabited LNothing impossible
  uninhabited (LJust _) impossible

public export
Strict a eq lt => Uninhabited (Lower lt (Just k) (Just k)) where
  uninhabited LNothing impossible
  uninhabited (LJust refl) = void (irreflexive refl)

public export
fromLT : Lower lt (Just a) (Just b) -> lt a b
fromLT (LJust x) = x

||| Implementation and alias for `trichotomy`.
export
comp : Trichotomous a (===) lt => (m1,m2 : Maybe a) -> Trichotomy (Lower lt) m1 m2
comp (Just x) (Just y) = case trichotomy {rel = lt} x y of
  LT p c1 c2 => LT (LJust p) (\r => c1 (injective r)) (\x => c2 (fromLT x))
  EQ c1 p c2 => EQ (\x => c1 (fromLT x)) (cong Just p) (\x => c2 (fromLT x))
  GT c1 c2 p => GT (\x => c1 (fromLT x)) (\r => c2 (injective r)) (LJust p)
comp (Just x) Nothing  = GT absurd absurd LNothing
comp Nothing  (Just y) = LT LNothing absurd absurd
comp Nothing  Nothing  = EQ absurd Refl absurd

||| If `lt` is a total order of `a`, then `Lower lt` is a
||| total order of `Maybe a`.
export %inline
Trichotomous a (===) lt => Trichotomous (Maybe a) (===) (Lower lt) where
  trichotomy = comp
  eqLeft Refl lt = lt
  eqRight lt Refl = lt

export %inline
Transitive a lt => Transitive (Maybe a) (Lower lt) where
  transitive y         LNothing  = absurd y
  transitive (LJust x) (LJust y) = LJust $ transitive x y
  transitive LNothing  (LJust y) = LNothing
