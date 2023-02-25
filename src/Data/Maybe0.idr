module Data.Maybe0

%default total

||| An optional data type for erased values.
||| At runtime, this is just 0 or 1.
public export
data Maybe0 : Type -> Type where
  Nothing0 : Maybe0 a
  Just0    : (0 v : a) -> Maybe0 a

public export
map : (0 f : a -> b) -> Maybe0 a -> Maybe0 b
map f Nothing0  = Nothing0
map f (Just0 v) = Just0 (f v)

public export
data IsJust0 : Maybe0 a -> Type where
  ItIsJust0 : IsJust0 (Just0 v)

public export
0 fromJust0 : (m : Maybe0 a) -> {auto prf : IsJust0 m} -> a
fromJust0 (Just0 x) = x

public export
(<|>) : Maybe0 t -> Lazy (Maybe0 t) -> Maybe0 t
(<|>) (Just0 v) _ = Just0 v
(<|>) Nothing0  m = m

public export
zipWith : (0 f : a -> b -> c) -> Maybe0 a -> Maybe0 b -> Maybe0 c
zipWith f (Just0 x) (Just0 y) = Just0 $ f x y
zipWith f _         _         = Nothing0

public export
zipWith3 : (0 f : a -> b -> c -> d) -> Maybe0 a -> Maybe0 b -> Maybe0 c -> Maybe0 d
zipWith3 f (Just0 x) (Just0 y) (Just0 z) = Just0 $ f x y z
zipWith3 f _         _         _         = Nothing0
