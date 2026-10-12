/- ARCHIVED (2026-10-01): LL track, parked (docs/ENDPOINT.md section 7); many-body theory continues in GW.Endpoint.ManyBody; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
LL-C2B evaluator: exact rational coefficients of the screened interaction `W`
and of the ring series `T`, at degrees 0..4, on fixtures including a nonscalar
N=2 case where `v * B ≠ B * v`.

The executable values are NOT the theorems. What links them is named:

* `GW.LL.coeff_W`            : `coeff k (W G v) = Wcoeff G v k`
* `GW.LL.coeff_T_eq_Tcoeff`  : `coeff k (T G v) = Tcoeff G v k`

so the matrices printed below are the actual power-series coefficients, and the
arbitrary-order statements `GW.LL.T_eq_neg_hadamardSeries_W`, `PL_mul_W` and
`W_mul_PR` are what make the finite table below a regression rather than the
proof. Formal coefficients only: nothing here is evaluated at a point and no
convergence is claimed.
-/
import GW.LL.Screening
import Mathlib.Data.Matrix.Notation

open GW.LL

structure BFixture where
  name : String
  dim : ℕ
  G : Matrix (Fin dim) (Fin dim) ℚ
  v : Matrix (Fin dim) (Fin dim) ℚ
  i : Fin dim
  j : Fin dim

def bq (n d : Int) : ℚ := (n : ℚ) / (d : ℚ)

/-- Nonscalar N=2, `v * B ≠ B * v`; the same inputs as the C2A table. -/
def bf1 : BFixture :=
  { name := "N2-pd", dim := 2, G := !![2, 1; 1, 2], v := !![1, 2; 2, 3], i := 0, j := 1 }

/-- Nonscalar N=2 with non-integer rationals. -/
def bf2 : BFixture :=
  { name := "N2-rational", dim := 2,
    G := !![bq 1 2, bq (-1) 3; bq (-1) 3, bq 3 2],
    v := !![bq 2 5, bq 1 7; bq 1 7, bq (-4) 3], i := 1, j := 0 }

/-- N=3, one additional small order. -/
def bf3 : BFixture :=
  { name := "N3-pd", dim := 3,
    G := !![3, 1, 0; 1, 3, 1; 0, 1, 3],
    v := !![1, 2, 3; 2, 0, 1; 3, 1, 2], i := 0, j := 1 }

def bfixtures : List BFixture := [bf1, bf2, bf3]

def ratStr (x : ℚ) : String := s!"{x.num}/{x.den}"

def border : List ℕ := [0, 1, 2, 3, 4]

/-- A full matrix as a JSON array of arrays of exact rationals. -/
def matStr {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : String :=
  let row := fun a : Fin n =>
    "[" ++ String.intercalate ", "
      ((List.finRange n).map fun b => "\"" ++ ratStr (M a b) ++ "\"") ++ "]"
  "[" ++ String.intercalate ", " ((List.finRange n).map row) ++ "]"

def seriesFor (f : BFixture) (which : Bool) : String :=
  let entry := fun k : ℕ =>
    let M := if which then Wcoeff f.G f.v k else Tcoeff f.G f.v k
    "\"" ++ toString k ++ "\": " ++ matStr M
  "{" ++ String.intercalate ", " (border.map entry) ++ "}"

def rowForB (f : BFixture) : String :=
  "  {\"name\": \"" ++ f.name ++ "\", \"N\": " ++ toString f.dim ++
    ", \"i\": " ++ toString f.i.val ++ ", \"j\": " ++ toString f.j.val ++
    ",\n   \"W\": " ++ seriesFor f true ++
    ",\n   \"T\": " ++ seriesFor f false ++ "}"

def main : IO Unit := do
  IO.println "{"
  IO.println "  \"source\": \"Lin-Lindsey Part I arXiv:1809.02900v1, PDF section 4.7.1, Fig. 4.11\","
  IO.println "  \"series\": \"W = S_L C(v) via PowerSeries.invOfUnit; T from GW.LL.ring k\","
  IO.println "  \"bridges\": [\"GW.LL.coeff_W\", \"GW.LL.coeff_T_eq_Tcoeff\"],"
  IO.println "  \"degree_convention\": \"bubble counting; ring k has k+1 interactions\","
  IO.println ("  \"orders\": [" ++ String.intercalate ", " (border.map toString) ++ "],")
  IO.println "  \"values\": ["
  IO.println (String.intercalate ",\n" (bfixtures.map rowForB))
  IO.println "  ]"
  IO.println "}"
