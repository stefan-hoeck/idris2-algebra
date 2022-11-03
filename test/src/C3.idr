module C3

import public Algebra.Group

%default total

||| The smallest non-abelian group
public export
data C3 = E | A | B | AB | BA | ABA

public export
(<+>) : C3 -> C3 -> C3
E   <+> y   = y
x   <+> E   = x
A   <+> A   = E
A   <+> B   = AB
A   <+> AB  = B
A   <+> BA  = ABA
A   <+> ABA = BA
B   <+> A   = BA
B   <+> B   = E
B   <+> AB  = ABA
B   <+> BA  = A
B   <+> ABA = AB
AB  <+> A   = ABA
AB  <+> B   = A
AB  <+> AB  = BA
AB  <+> BA  = E
AB  <+> ABA = B
BA  <+> A   = B
BA  <+> B   = ABA
BA  <+> AB  = E
BA  <+> BA  = AB
BA  <+> ABA = A
ABA <+> A   = AB
ABA <+> B   = BA
ABA <+> AB  = A
ABA <+> BA  = B
ABA <+> ABA = E

public export
neg : C3 -> C3
neg E   = E
neg A   = A
neg B   = B
neg AB  = BA
neg BA  = AB
neg ABA = ABA

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

assoc : (x,y,z : C3) -> x <+> (y <+> z) === (x <+> y) <+> z
assoc E y z       = Refl
assoc A E z       = Refl
assoc B E z       = Refl
assoc AB E z      = Refl
assoc BA E z      = Refl
assoc ABA E z     = Refl
assoc A A E       = Refl
assoc A A A       = Refl
assoc A A B       = Refl
assoc A A AB      = Refl
assoc A A BA      = Refl
assoc A A ABA     = Refl
assoc A B E       = Refl
assoc A B A       = Refl
assoc A B B       = Refl
assoc A B AB      = Refl
assoc A B BA      = Refl
assoc A B ABA     = Refl
assoc A AB E      = Refl
assoc A AB A      = Refl
assoc A AB B      = Refl
assoc A AB AB     = Refl
assoc A AB BA     = Refl
assoc A AB ABA    = Refl
assoc A BA E      = Refl
assoc A BA A      = Refl
assoc A BA B      = Refl
assoc A BA AB     = Refl
assoc A BA BA     = Refl
assoc A BA ABA    = Refl
assoc A ABA E     = Refl
assoc A ABA A     = Refl
assoc A ABA B     = Refl
assoc A ABA AB    = Refl
assoc A ABA BA    = Refl
assoc A ABA ABA   = Refl
assoc B A E       = Refl
assoc B A A       = Refl
assoc B A B       = Refl
assoc B A AB      = Refl
assoc B A BA      = Refl
assoc B A ABA     = Refl
assoc B B E       = Refl
assoc B B A       = Refl
assoc B B B       = Refl
assoc B B AB      = Refl
assoc B B BA      = Refl
assoc B B ABA     = Refl
assoc B AB E      = Refl
assoc B AB A      = Refl
assoc B AB B      = Refl
assoc B AB AB     = Refl
assoc B AB BA     = Refl
assoc B AB ABA    = Refl
assoc B BA E      = Refl
assoc B BA A      = Refl
assoc B BA B      = Refl
assoc B BA AB     = Refl
assoc B BA BA     = Refl
assoc B BA ABA    = Refl
assoc B ABA E     = Refl
assoc B ABA A     = Refl
assoc B ABA B     = Refl
assoc B ABA AB    = Refl
assoc B ABA BA    = Refl
assoc B ABA ABA   = Refl
assoc AB A E      = Refl
assoc AB A A      = Refl
assoc AB A B      = Refl
assoc AB A AB     = Refl
assoc AB A BA     = Refl
assoc AB A ABA    = Refl
assoc AB B E      = Refl
assoc AB B A      = Refl
assoc AB B B      = Refl
assoc AB B AB     = Refl
assoc AB B BA     = Refl
assoc AB B ABA    = Refl
assoc AB AB E     = Refl
assoc AB AB A     = Refl
assoc AB AB B     = Refl
assoc AB AB AB    = Refl
assoc AB AB BA    = Refl
assoc AB AB ABA   = Refl
assoc AB BA E     = Refl
assoc AB BA A     = Refl
assoc AB BA B     = Refl
assoc AB BA AB    = Refl
assoc AB BA BA    = Refl
assoc AB BA ABA   = Refl
assoc AB ABA E    = Refl
assoc AB ABA A    = Refl
assoc AB ABA B    = Refl
assoc AB ABA AB   = Refl
assoc AB ABA BA   = Refl
assoc AB ABA ABA  = Refl
assoc BA A E      = Refl
assoc BA A A      = Refl
assoc BA A B      = Refl
assoc BA A AB     = Refl
assoc BA A BA     = Refl
assoc BA A ABA    = Refl
assoc BA B E      = Refl
assoc BA B A      = Refl
assoc BA B B      = Refl
assoc BA B AB     = Refl
assoc BA B BA     = Refl
assoc BA B ABA    = Refl
assoc BA AB E     = Refl
assoc BA AB A     = Refl
assoc BA AB B     = Refl
assoc BA AB AB    = Refl
assoc BA AB BA    = Refl
assoc BA AB ABA   = Refl
assoc BA BA E     = Refl
assoc BA BA A     = Refl
assoc BA BA B     = Refl
assoc BA BA AB    = Refl
assoc BA BA BA    = Refl
assoc BA BA ABA   = Refl
assoc BA ABA E    = Refl
assoc BA ABA A    = Refl
assoc BA ABA B    = Refl
assoc BA ABA AB   = Refl
assoc BA ABA BA   = Refl
assoc BA ABA ABA  = Refl
assoc ABA A E     = Refl
assoc ABA A A     = Refl
assoc ABA A B     = Refl
assoc ABA A AB    = Refl
assoc ABA A BA    = Refl
assoc ABA A ABA   = Refl
assoc ABA B E     = Refl
assoc ABA B A     = Refl
assoc ABA B B     = Refl
assoc ABA B AB    = Refl
assoc ABA B BA    = Refl
assoc ABA B ABA   = Refl
assoc ABA AB E    = Refl
assoc ABA AB A    = Refl
assoc ABA AB B    = Refl
assoc ABA AB AB   = Refl
assoc ABA AB BA   = Refl
assoc ABA AB ABA  = Refl
assoc ABA BA E    = Refl
assoc ABA BA A    = Refl
assoc ABA BA B    = Refl
assoc ABA BA AB   = Refl
assoc ABA BA BA   = Refl
assoc ABA BA ABA  = Refl
assoc ABA ABA E   = Refl
assoc ABA ABA A   = Refl
assoc ABA ABA B   = Refl
assoc ABA ABA AB  = Refl
assoc ABA ABA BA  = Refl
assoc ABA ABA ABA = Refl

lne : (c : C3) -> E <+> c === c
lne c = Refl

rne : (c : C3) -> c <+> E === c
rne E   = Refl
rne A   = Refl
rne B   = Refl
rne AB  = Refl
rne BA  = Refl
rne ABA = Refl

linv : (c : C3) -> neg c <+> c === E
linv E   = Refl
linv A   = Refl
linv B   = Refl
linv AB  = Refl
linv BA  = Refl
linv ABA = Refl

rinv : (c : C3) -> c <+> neg c === E
rinv E   = Refl
rinv A   = Refl
rinv B   = Refl
rinv AB  = Refl
rinv BA  = Refl
rinv ABA = Refl

export
grp_c3 : Group C3 E C3.neg (<+>)
grp_c3 = MkGroup (assoc _ _ _) (lne _) (rne _) (linv _) (rinv _)
