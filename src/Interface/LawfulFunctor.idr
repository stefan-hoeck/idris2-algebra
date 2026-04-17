module Interface.LawfulFunctor

%default total

||| A functor is 'Lawful'
||| if it satisfies the requirements of a functor.
||| Idris2's `Functor` does not require this.
public export
interface Functor f => LawfulFunctor (0 f : Type -> Type) where
    id_map : forall a . (x : f a) -> Prelude.id <$> x = x
    comp_map : forall a, b, c . (g : a -> b) -> (h : b -> c) -> (x : f a) -> (h . g) <$> x = h <$> g <$> x

LawfulFunctor List where
    id_map [] = Refl
    id_map (x :: xs) = rewrite id_map xs in Refl

    comp_map g h [] = Refl
    comp_map g h (x :: xs) = rewrite comp_map g h xs in Refl

LawfulFunctor Maybe where
    id_map (Just x) = Refl
    id_map Nothing = Refl

    comp_map g h (Just x) = Refl
    comp_map g h Nothing = Refl
