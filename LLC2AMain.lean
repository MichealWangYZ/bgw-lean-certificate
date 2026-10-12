/- ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
LL-C2A evaluator: exact rational values of the STRUCTURAL ring family
`GW.LL.ring k` for k = 0..4, on fixtures including a nonscalar N=2 case.

Separate from `ll_c1_eval` so the LL-C1 artifact and its contracts are
untouched. Values use `contributionOf (2^k)`, whose divisor is certified equal
to the automorphism count by `GW.LL.card_aut_ring`, and whose whole value is
certified by `GW.LL.contribution_ring`.
-/
import GW.LL.StructuralRing
import Mathlib.Data.Matrix.Notation

open GW.LL FeynDiagram

structure CFixture where
  name : String
  dim : ℕ
  G : Matrix (Fin dim) (Fin dim) ℚ
  v : Matrix (Fin dim) (Fin dim) ℚ
  i : Fin dim
  j : Fin dim

def cq (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- Nonscalar N=2, `G` positive definite, `v` symmetric, `v*B ≠ B*v`. -/
def cf1 : CFixture :=
  { name := "N2-pd", dim := 2, G := !![2, 1; 1, 2], v := !![1, 2; 2, 3], i := 0, j := 1 }

/-- Nonscalar N=2 with non-integer rationals. -/
def cf2 : CFixture :=
  { name := "N2-rational", dim := 2,
    G := !![cq 1 2, cq (-1) 3; cq (-1) 3, cq 3 2],
    v := !![cq 2 5, cq 1 7; cq 1 7, cq (-4) 3], i := 1, j := 0 }

/-- N=3, for one additional small order. -/
def cf3 : CFixture :=
  { name := "N3-pd", dim := 3,
    G := !![3, 1, 0; 1, 3, 1; 0, 1, 3],
    v := !![1, 2, 3; 2, 0, 1; 3, 1, 2], i := 0, j := 1 }

def cfixtures : List CFixture := [cf1, cf2, cf3]

def ratStr' (x : ℚ) : String := s!"{x.num}/{x.den}"

def orders : List ℕ := [0, 1, 2, 3, 4]

def valueAt (f : CFixture) (k : ℕ) : String :=
  ratStr' (contributionOf (2 ^ k) (ring k) f.G f.v f.i f.j)

def rowFor (f : CFixture) : String :=
  let vals := orders.map fun k =>
    "\"k" ++ toString k ++ "\": \"" ++ valueAt f k ++ "\""
  "  {\"name\": \"" ++ f.name ++ "\", \"N\": " ++ toString f.dim ++
    ", \"i\": " ++ toString f.i.val ++ ", \"j\": " ++ toString f.j.val ++
    ", " ++ String.intercalate ", " vals ++ "}"

def main : IO Unit := do
  IO.println "{"
  IO.println "  \"source\": \"Lin-Lindsey Part I arXiv:1809.02900v1, PDF section 4.7.1, Fig. 4.11\","
  IO.println "  \"family\": \"GW.LL.ring k, structural; divisor 2^k certified by GW.LL.card_aut_ring\","
  IO.println ("  \"orders\": [" ++ String.intercalate ", " (orders.map toString) ++ "],")
  IO.println "  \"values\": ["
  IO.println (String.intercalate ",\n" (cfixtures.map rowFor))
  IO.println "  ]"
  IO.println "}"
