module Data.Pair0

%default total

||| A pair of two erased values.
public export
record Pair0 (a,b : Type) where
  constructor P0
  0 fst : a
  0 snd : b

||| This is the identity at runtime.
public export
bimap : (0 f : a -> c) -> (0 g : b -> d) -> Pair0 a b -> Pair0 c d
bimap f g (P0 x y) = P0 (f x) (g y)

public export %inline
map : (0 f : b -> d) -> Pair0 a b -> Pair0 a d
map = bimap id
