/- ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
LL-C4 evaluator: exact rational values of the finite static electronic RPA
model -- polarizability, dielectric matrix, Neumann coefficients and partial
sums -- on fixtures whose transitions all run occupied -> empty.

The printed matrices are not the theorems. The named connections are:

* `GW.LL.coeff_electronicW_eq_neumannCoeff` -- the emitted `neumann` values ARE
  the coefficients of the formal screened interaction;
* `GW.LL.dielectric_mul_partialScreened`    -- the exact truncation identity;
* `GW.LL.chi0_quadForm_nonpos`              -- the sign convention is coherent.

The electronic quantities are a SPECIFICATION, not a derivation, and not a
BerkeleyGW convention. Static (zero-frequency) only; no `Sigma = i G W`.
-/
import GW.LL.Electronic
import Mathlib.Data.Matrix.Notation

open GW.LL

structure EFixture where
  name : String
  dim : ℕ
  v : Matrix (Fin dim) (Fin dim) ℚ
  ts : List (Transition ℚ dim)
  i : Fin dim
  j : Fin dim

def eq' (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- Two transitions, `N = 2`. Weight 4 is a stated spin/degeneracy input. -/
def ef1 : EFixture :=
  { name := "N2-two-channel", dim := 2, v := !![2, 1; 1, 3],
    ts := [{ occ := 0, emp := 2, weight := 4, m := ![1, 0] },
           { occ := eq' (-1) 2, emp := eq' 3 2, weight := 4, m := ![1, 1] }],
    i := 0, j := 1 }

/-- Non-integer rationals throughout. -/
def ef2 : EFixture :=
  { name := "N2-rational", dim := 2, v := !![eq' 1 2, eq' (-1) 3; eq' (-1) 3, eq' 3 2],
    ts := [{ occ := eq' (-1) 5, emp := eq' 7 5, weight := eq' 2 3, m := ![eq' 1 2, eq' (-2) 3] }],
    i := 1, j := 0 }

/-- `N = 3`, three channels with distinct energies. -/
def ef3 : EFixture :=
  { name := "N3-three-channel", dim := 3, v := !![3, 1, 0; 1, 3, 1; 0, 1, 3],
    ts := [{ occ := 0, emp := 1, weight := 2, m := ![1, 0, 0] },
           { occ := eq' (-1) 2, emp := 2, weight := 2, m := ![0, 1, 0] },
           { occ := -1, emp := 3, weight := 2, m := ![1, 1, 1] }],
    i := 0, j := 1 }

def efixtures : List EFixture := [ef1, ef2, ef3]

def ratStrE (x : ℚ) : String := s!"{x.num}/{x.den}"

def matStrE {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : String :=
  let row := fun a : Fin n =>
    "[" ++ String.intercalate ", "
      ((List.finRange n).map fun b => "\"" ++ ratStrE (M a b) ++ "\"") ++ "]"
  "[" ++ String.intercalate ", " ((List.finRange n).map row) ++ "]"

def eorders : List ℕ := [0, 1, 2, 3]

def seriesE (f : EFixture) (which : String) : String :=
  if which = "chi0" then "{\"0\": " ++ matStrE (chi0 f.ts) ++ "}"
  else if which = "eps" then "{\"0\": " ++ matStrE (dielectric f.v f.ts) ++ "}"
  else
    let entry := fun k : ℕ =>
      let M := if which = "neumann" then neumannCoeff f.v f.ts k
               else partialScreened f.v f.ts k
      "\"" ++ toString k ++ "\": " ++ matStrE M
    "{" ++ String.intercalate ", " (eorders.map entry) ++ "}"

def rowForE (f : EFixture) : String :=
  "  {\"name\": \"" ++ f.name ++ "\", \"N\": " ++ toString f.dim ++
    ", \"i\": " ++ toString f.i.val ++ ", \"j\": " ++ toString f.j.val ++
    ",\n   \"chi0\": " ++ seriesE f "chi0" ++
    ",\n   \"eps\": " ++ seriesE f "eps" ++
    ",\n   \"neumann\": " ++ seriesE f "neumann" ++
    ",\n   \"partial\": " ++ seriesE f "partial" ++ "}"

def main : IO Unit := do
  IO.println "{"
  IO.println "  \"model\": \"finite static RPA: chi0 from occupied->empty transitions, eps = 1 - v chi0\","
  IO.println "  \"specified_not_derived\": \"conventions and spin/degeneracy weights are INPUTS; not a BerkeleyGW convention or result\","
  IO.println "  \"scope\": \"static only; no Sigma = i G W, no self-consistency, no convergence claim\","
  IO.println "  \"bridges\": [\"GW.LL.coeff_electronicW_eq_neumannCoeff\", \"GW.LL.dielectric_mul_partialScreened\"],"
  IO.println "  \"static_orders\": [0],"
  IO.println ("  \"orders\": [" ++ String.intercalate ", " (eorders.map toString) ++ "],")
  IO.println "  \"values\": ["
  IO.println (String.intercalate ",\n" (efixtures.map rowForE))
  IO.println "  ]"
  IO.println "}"
