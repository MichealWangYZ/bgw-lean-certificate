/-
G2-coulomb: the 12 signed coordinate permutations (core Lean data).
`SG a b c neg : x ↦ (±x_a, ±x_b, ±x_c)`.
-/
import GW.Endpoint.Coulomb.GeomDefs

namespace GW.Endpoint.Coulomb

structure SG where
  a : Fin 3
  b : Fin 3
  c : Fin 3
  neg : Bool
deriving DecidableEq, Repr

def SG.pm (g : SG) (i : Fin 3) : Fin 3 := match i with | ⟨0, _⟩ => g.a | ⟨1, _⟩ => g.b | _ => g.c

def SG.valid (g : SG) : Bool := decide (g.a ≠ g.b) && decide (g.a ≠ g.c) && decide (g.b ≠ g.c)

/-- The inverse permutation index. -/
def SG.iv (g : SG) (j : Fin 3) : Fin 3 := if g.a = j then 0 else if g.b = j then 1 else 2

def SG.inv (g : SG) : SG := ⟨g.iv 0, g.iv 1, g.iv 2, g.neg⟩

/-- Action on integer vectors. -/
def SG.actI (g : SG) (n : IV) : IV :=
  let s : Int := if g.neg then -1 else 1
  ⟨s * n.g (g.pm 0), s * n.g (g.pm 1), s * n.g (g.pm 2)⟩

/-- Action on keys. -/
def SG.actK (g : SG) (k : Int × Int × Int) : Int × Int × Int :=
  let v := g.actI (keyIV k)
  (v.x, v.y, v.z)

def G12 : List SG :=
  [⟨0,1,2,false⟩, ⟨0,2,1,false⟩, ⟨1,0,2,false⟩, ⟨1,2,0,false⟩, ⟨2,0,1,false⟩, ⟨2,1,0,false⟩,
   ⟨0,1,2,true⟩, ⟨0,2,1,true⟩, ⟨1,0,2,true⟩, ⟨1,2,0,true⟩, ⟨2,0,1,true⟩, ⟨2,1,0,true⟩]

/-- The group checks: valid, closed under inverse, and permuting the cell normals. -/
def symOK (ns : List IV) : Bool :=
  G12.all fun g => g.valid && G12.elem g.inv && ns.all fun n => ns.elem (g.actI n)

end GW.Endpoint.Coulomb
