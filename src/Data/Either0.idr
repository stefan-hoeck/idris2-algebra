module Data.Either0

%default total

||| A choice of two erased values.
||| At runtime, this is just 0 or 1.
public export
data Either0 : Type -> Type -> Type where
  Left0  : (0 v : a) -> Either0 a b
  Right0 : (0 v : b) -> Either0 a b

||| This is the identity at runtime.
public export
bimap : (0 f : a -> c) -> (0 g : b -> d) -> Either0 a b -> Either0 c d
bimap f g (Left0 v)  = Left0 $ f v
bimap f g (Right0 v) = Right0 $ g v

||| This is the identity at runtime.
public export %inline
map : (0 f : b -> d) -> Either0 a b -> Either0 a d
map = bimap id

public export %inline
0 either0 : (f : a -> e) -> (g : b -> e) -> Either0 a b -> e
either0 f g (Left0 v)  = f v
either0 f g (Right0 v) = g v

public export
data IsLeft0 : Either0 a b -> Type where
  ItIsLeft0 : IsLeft0 (Left0 v)

public export
0 fromLeft0 : (e : Either0 a b) -> {auto prf : IsLeft0 e} -> a
fromLeft0 (Left0 v) = v

public export
data IsRight0 : Either0 a b -> Type where
  ItIsRight0 : IsRight0 (Right0 v)

public export
0 fromRight0 : (e : Either0 a b) -> {auto prf : IsRight0 e} -> b
fromRight0 (Right0 v) = v

public export
(<|>) : Either0 a b -> Lazy (Either0 a b) -> Either0 a b
(<|>) (Right0 v) _ = Right0 v
(<|>) (Left0 _)  e = e
