/- ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
LL-C1 evaluator: prints the exact rational value of the first three ring
diagrams on fixed fixtures, as computed by the Lean graph contraction.

The values printed here are produced by `GW.LL.contributionOf` applied to the
diagram DATA. The symmetry divisors 1, 2, 4 are literals, certified equal to
the automorphism counts by `GW.LL.symmetry_ring0/1/2` together with
`FeynDiagram.contribution_eq_of_card`; evaluating the automorphism enumeration
at runtime is infeasible for ring 2, which is why the literal form exists.

`tests/test_ll_c1.py` recomputes these numbers from an independent Python
implementation and compares exactly. That reference must never read this
output as an expected-answer column.
-/
import GW.LL.Ring
import Mathlib.Data.Matrix.Notation

open GW.LL FeynDiagram

/-- A named fixture: dimension, `G`, `v`, and the external index pair. -/
structure Fixture where
  name : String
  dim : ℕ
  G : Matrix (Fin dim) (Fin dim) ℚ
  v : Matrix (Fin dim) (Fin dim) ℚ
  i : Fin dim
  j : Fin dim

def q (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- N=1 scalar. -/
def fx1 : Fixture :=
  { name := "N1-scalar", dim := 1, G := !![2], v := !![3], i := 0, j := 0 }

/-- N=2, `G` symmetric positive definite (eigenvalues 1 and 3), `v` symmetric,
and `v * B ≠ B * v`. External indices equal. -/
def fx2 : Fixture :=
  { name := "N2-pd-equal-ext", dim := 2, G := !![2, 1; 1, 2], v := !![1, 2; 2, 3],
    i := 0, j := 0 }

/-- Same matrices, unequal external indices. -/
def fx3 : Fixture :=
  { name := "N2-pd-unequal-ext", dim := 2, G := !![2, 1; 1, 2], v := !![1, 2; 2, 3],
    i := 0, j := 1 }

/-- N=2 with non-integer rational entries. -/
def fx4 : Fixture :=
  { name := "N2-rational", dim := 2,
    G := !![q 1 2, q (-1) 3; q (-1) 3, q 3 2],
    v := !![q 2 5, q 1 7; q 1 7, q (-4) 3], i := 1, j := 0 }

/-- N=3, `G` symmetric diagonally dominant (hence positive definite),
`v` symmetric and non-diagonal. -/
def fx5 : Fixture :=
  { name := "N3-pd-unequal-ext", dim := 3,
    G := !![3, 1, 0; 1, 3, 1; 0, 1, 3],
    v := !![1, 2, 3; 2, 0, 1; 3, 1, 2], i := 0, j := 1 }

/-- Same N=3 matrices, equal external indices. -/
def fx6 : Fixture :=
  { name := "N3-pd-equal-ext", dim := 3,
    G := !![3, 1, 0; 1, 3, 1; 0, 1, 3],
    v := !![1, 2, 3; 2, 0, 1; 3, 1, 2], i := 1, j := 1 }

def fixtures : List Fixture := [fx1, fx2, fx3, fx4, fx5, fx6]

def ratStr (x : ℚ) : String := s!"{x.num}/{x.den}"

def lineFor (f : Fixture) : String :=
  let c0 := contributionOf 1 ring0 f.G f.v f.i f.j
  let c1 := contributionOf 2 ring1 f.G f.v f.i f.j
  let c2 := contributionOf 4 ring2 f.G f.v f.i f.j
  "  {\"name\": \"" ++ f.name ++ "\", \"N\": " ++ toString f.dim ++
    ", \"i\": " ++ toString f.i.val ++ ", \"j\": " ++ toString f.j.val ++
    ", \"ring0\": \"" ++ ratStr c0 ++ "\", \"ring1\": \"" ++ ratStr c1 ++
    "\", \"ring2\": \"" ++ ratStr c2 ++ "\"}"

def main : IO Unit := do
  IO.println "{"
  IO.println "  \"source\": \"Lin-Lindsey Part I arXiv:1809.02900v1, PDF section 4.7.1, Fig. 4.11\","
  IO.println "  \"symmetry_factors\": {\"ring0\": 1, \"ring1\": 2, \"ring2\": 4},"
  IO.println "  \"values\": ["
  let body := (fixtures.map lineFor)
  IO.println (String.intercalate ",\n" body)
  IO.println "  ]"
  IO.println "}"
