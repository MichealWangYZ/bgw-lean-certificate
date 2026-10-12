/- ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
LL-C3 evaluator: exact rational values of the normalized first-order correction
and its Hartree/Fock split, on fixtures with symmetric `G` and `v`.

The printed matrices are not the theorems. The named connections are:

* `GW.LL.disconnected_cancels`            -- the normalization subtraction is exact
* `GW.LL.firstOrder_eq_hartree_fock`      -- the closed form
* `GW.LL.dressed_ring0_eq_neg_fock`       -- the Fock term IS C2A's ring 0, dressed
* `GW.LL.firstOrder_eq_dressed_ring0_add_hartree`

Wick's theorem is a DEFINITION here, not a result; see `GW/LL/Wick.lean`.
-/
import GW.LL.Wick
import Mathlib.Data.Matrix.Notation

open GW.LL

structure WFixture where
  name : String
  dim : ℕ
  G : Matrix (Fin dim) (Fin dim) ℚ
  v : Matrix (Fin dim) (Fin dim) ℚ
  i : Fin dim
  j : Fin dim

def wq (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- Symmetric `G` and `v`, `N = 2`. -/
def wf1 : WFixture :=
  { name := "N2-sym", dim := 2, G := !![2, 1; 1, 3], v := !![1, 2; 2, 3], i := 0, j := 1 }

/-- Symmetric, non-integer rationals. -/
def wf2 : WFixture :=
  { name := "N2-rational", dim := 2,
    G := !![wq 1 2, wq (-1) 3; wq (-1) 3, wq 3 2],
    v := !![wq 2 5, wq 1 7; wq 1 7, wq (-4) 3], i := 1, j := 0 }

/-- `N = 3`, symmetric, with a zero in `G` so the loop vector is not uniform. -/
def wf3 : WFixture :=
  { name := "N3-sym", dim := 3,
    G := !![3, 1, 0; 1, 3, 1; 0, 1, 3],
    v := !![1, 2, 3; 2, 0, 1; 3, 1, 2], i := 0, j := 1 }

def wfixtures : List WFixture := [wf1, wf2, wf3]

def ratStrW (x : ℚ) : String := s!"{x.num}/{x.den}"

def matStrW {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : String :=
  let row := fun a : Fin n =>
    "[" ++ String.intercalate ", "
      ((List.finRange n).map fun b => "\"" ++ ratStrW (M a b) ++ "\"") ++ "]"
  "[" ++ String.intercalate ", " ((List.finRange n).map row) ++ "]"

/-- The four emitted matrices, all at first order in `v`. -/
def seriesW (f : WFixture) (which : String) : String :=
  let M : Matrix (Fin f.dim) (Fin f.dim) ℚ :=
    if which = "delta" then Matrix.of fun a b => firstOrder f.G f.v a b
    else if which = "hartree" then hartreeMatrix f.G f.v
    else if which = "fock" then fockMatrix f.G f.v
    else f.G * ring0Matrix f.G f.v * f.G
  "{\"1\": " ++ matStrW M ++ "}"

def rowForW (f : WFixture) : String :=
  "  {\"name\": \"" ++ f.name ++ "\", \"N\": " ++ toString f.dim ++
    ", \"i\": " ++ toString f.i.val ++ ", \"j\": " ++ toString f.j.val ++
    ",\n   \"delta\": " ++ seriesW f "delta" ++
    ",\n   \"hartree\": " ++ seriesW f "hartree" ++
    ",\n   \"fock\": " ++ seriesW f "fock" ++
    ",\n   \"ringDressed\": " ++ seriesW f "ringDressed" ++ "}"

def main : IO Unit := do
  IO.println "{"
  IO.println "  \"source\": \"Lin-Lindsey Part I arXiv:1809.02900v1, classical real Gibbs model, sections 3-4\","
  IO.println "  \"assumed_input\": \"Wick/Isserlis is the DEFINITION of the moment here, not a proved theorem\","
  IO.println "  \"interaction\": \"U = (1/8) * sum_ij v_ij x_i^2 x_j^2 (normalization: Lin-Lindsey Part I eq. (2.4), printed p. 5, verified by the C3/C4 review)\","
  IO.println "  \"bridges\": [\"GW.LL.disconnected_cancels\", \"GW.LL.firstOrder_eq_hartree_fock\", \"GW.LL.dressed_ring0_eq_neg_fock\"],"
  IO.println "  \"orders\": [1],"
  IO.println "  \"values\": ["
  IO.println (String.intercalate ",\n" (wfixtures.map rowForW))
  IO.println "  ]"
  IO.println "}"
