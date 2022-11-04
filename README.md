# idris2-algebra Lawful algebraic structures in Idris2

This library provides laws and proofs for common algebraic structures
such as groups and rings. These laws are encoded as record types
indexed over the type and functions to which they apply. For instance,
for the monoid laws we have:

```idris
record Monoid (a : Type) (z : a) (p : Op2 a) where
  constructor MkMonoid
  associative  : Associative p
  rightNeutral : RightNeutral z p
  leftNeutral  : LeftNeutral z p
```

Here `Op2 a` is an alias for a binary function on `a`: `a -> a -> a`,
and the given field types are aliases for the corresponding algebraic
laws. For instance:

```idris
public export
0 LeftNeutral : (z : a) -> Op2 a -> Type
LeftNeutral z p = {u : a} -> z `p` u === u
```

In addition, the library provides conversions in the form of
record accessors from algebraic structures to weaker ones.

## Why not use Interfaces?

There were several experiments by different people trying to do
this by inheriting directly from the interfaces we try to verify.
For instance:

```idris
interface Semigroup a => SemigroupV a where
  associative : {x,y,z : a} -> x <+> (y <+> z) === (x <+> y) <+> z
```

Unfortunately, this does not go well for more complex cases.
In the following version of `MonoidV`, Idris will no longer be able
to verify that the `Monoid` and `SemigroupV` our interface inherits
from, are using the same version of `(<+>)` (because Idris - unlike Haskell -
has no such thing as typeclass coherence):

```idris
interface SemigroupV a => Monoid a => MonoidV a where
```

It was suggested to index the lawful interfaces over the interfaces
they verify:

```idris
interface SemigroupV (0 a : Type) (0 sem : Semigroup a) where
```

This resolves the coherence issue described above, but it is still
cumbersome to talk about towers of algebraic structures. In addition,
with this approach we haven mostly given up type inference, and will often
have to specify explicitly the interface implementation to use.

But in that case, we can give up interfaces altogether and just
use plain indexed Idris records.
