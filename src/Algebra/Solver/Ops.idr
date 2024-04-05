module Algebra.Solver.Ops

import public Data.List.Elem

export infixl 8 .+>, <+., .+.

||| Checks if elements `x` and `y` are at the same position in list
||| `xs` and thus identical.
public export
eqElem : (e1 : Elem x xs) -> (e2 : Elem y xs) -> Maybe (e1 ~=~ e2)
eqElem Here Here      = Just Refl
eqElem Here (There z) = Nothing
eqElem (There z) Here = Nothing
eqElem (There z) (There w) = case eqElem z w of
  Just Refl => Just Refl
  Nothing   => Nothing
