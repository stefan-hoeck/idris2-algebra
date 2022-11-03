module GroupSolver

import C3
import Algebra.Solver.Group

%default total

IsE : (v : C3) -> Maybe (v === E)
IsE E = Just Refl
IsE _ = Nothing

0 solveC3 :
     (cs : List C3)
  -> (e1,e2 : Expr C3 cs)
  -> {auto prf : normalize E C3.neg (<+>) IsE e1 === normalize E C3.neg (<+>) IsE e2}
  -> eval E C3.neg (<+>) e1 === eval E C3.neg (<+>) e2
solveC3 _ e1 e2 = solve grp_c3 IsE e1 e2

--------------------------------------------------------------------------------
--          Examples
--------------------------------------------------------------------------------

0 noLits1 :
     {x,y,z : C3}
  -> neg (x <+> y) <+> (x <+> (z <+> y)) === (neg y <+> z) <+> y
noLits1 =
  solveC3
    [x,y,z]
    (Neg (x .+. y) <+> (x .+> (z .+. y)))
    ((neg y <+. z) <+. y)

0 lits1 :
     {x,y,z : C3}
  -> neg (x <+> AB) <+> (x <+> (z <+> y)) === (BA <+> z) <+> y
lits1 =
  solveC3
    [x,y,z]
    (Neg (x .+> Lit AB) <+> (x .+> (z .+. y)))
    ((Lit BA <+. z) <+. y)

0 lits2 :
     {x,y : C3}
  -> neg (x <+> AB) <+> (x <+> (AB <+> y)) === y
lits2 =
  solveC3
    [x,y]
    (Neg (x .+> Lit AB) <+> (x .+> (Lit AB <+. y)))
    (var y)
