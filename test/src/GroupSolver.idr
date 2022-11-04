module GroupSolver

import D3
import Algebra.Solver.Group

%default total

IsE : (v : D3) -> Maybe (v === E)
IsE E = Just Refl
IsE _ = Nothing

0 solveD3 :
     (cs : List D3)
  -> (e1,e2 : Expr D3 cs)
  -> {auto prf : normalize GrpD3 IsE e1 === normalize GrpD3 IsE e2}
  -> eval GrpD3 e1 === eval GrpD3 e2
solveD3 _ e1 e2 = solve GrpD3 IsE e1 e2

--------------------------------------------------------------------------------
--          Examples
--------------------------------------------------------------------------------

0 noLits1 :
     {x,y,z : D3}
  -> neg (x <+> y) <+> (x <+> (z <+> y)) === (neg y <+> z) <+> y
noLits1 =
  solveD3
    [x,y,z]
    (Neg (x .+. y) <+> (x .+> (z .+. y)))
    ((neg y <+. z) <+. y)

0 lits1 :
     {x,y,z : D3}
  -> neg (x <+> AB) <+> (x <+> (z <+> y)) === (BA <+> z) <+> y
lits1 =
  solveD3
    [x,y,z]
    (Neg (x .+> Lit AB) <+> (x .+> (z .+. y)))
    ((Lit BA <+. z) <+. y)

0 lits2 :
     {x,y : D3}
  -> neg (x <+> AB) <+> (x <+> (AB <+> y)) === y
lits2 =
  solveD3
    [x,y]
    (Neg (x .+> Lit AB) <+> (x .+> (Lit AB <+. y)))
    (var y)
