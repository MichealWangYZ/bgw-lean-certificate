/- ARCHIVED (2026-10-01): BGW-M3 lineage, superseded by GW.Endpoint.Kernel.EpsSpec and Data.E*; kept, not extended, outside the fast gate. See docs/CODEMAP.md.
BGW-M3-R1: the general machinery that carries a finite transition sum from the
exported (rounded) denominators to the denominators the physical operands
imply.

Nothing here is specific to a run. `GW/BGW/M3Chi.lean` supplies the pinned
data and discharges every hypothesis below by kernel computation, so the two
endpoint theorems there are unconditional.

The shape of the argument. Each transition `t` contributes `a_t * d_t` to the
sum, where `a_t` is built from the prefactor, the unweighted matrix elements,
the phases and the index map, and `d_t` is the energy denominator. The code
uses a rounded `edenHat_t`; the operands imply `dStar_t = occ / (eval - econd)`
exactly. `row_bound` turns an integer residual witness into a bound on
`|edenHat_t - dStar_t|`, and `transfer` propagates it through the sum.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Field.Basic

namespace GW.BGW.M3

/-! ## Generic list lemmas -/

/-- The transfer inequality: replacing each `d x` by `D x`, with a per-element
error bound, moves the weighted sum by at most the weighted sum of the
bounds. -/
theorem list_transfer {α : Type*} (l : List α) (A d D e : α → ℚ)
    (h : ∀ x ∈ l, |d x - D x| ≤ e x) :
    |(l.map (fun x => A x * d x)).sum - (l.map (fun x => A x * D x)).sum|
      ≤ (l.map (fun x => |A x| * e x)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : |d a - D a| ≤ e a := h a (by simp)
      have ht : ∀ x ∈ t, |d x - D x| ≤ e x := fun x hx => h x (by simp [hx])
      simp only [List.map_cons, List.sum_cons]
      have key : A a * d a + (t.map (fun x => A x * d x)).sum
                 - (A a * D a + (t.map (fun x => A x * D x)).sum)
               = A a * (d a - D a)
                 + ((t.map (fun x => A x * d x)).sum - (t.map (fun x => A x * D x)).sum) := by
        ring
      rw [key]
      refine (abs_add _ _).trans ?_
      have h1 : |A a * (d a - D a)| ≤ |A a| * e a := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)
      exact add_le_add h1 (ih ht)

theorem sum_map_const_mul_nat {α : Type*} (l : List α) (C : ℚ) (f : α → ℕ) :
    (l.map (fun r => C * ((f r : ℕ) : ℚ))).sum = C * (((l.map f).sum : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

theorem sum_map_const_mul_int {α : Type*} (l : List α) (C : ℚ) (f : α → ℤ) :
    (l.map (fun r => C * ((f r : ℤ) : ℚ))).sum = C * (((l.map f).sum : ℤ) : ℚ) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

/-- A signed list sum as the difference of two `Nat` sums. Used because a
1792-term `Int` fold does not reduce in the kernel while the `Nat` form
does. -/
theorem int_sum_split {α : Type*} (l : List α) (f : α → ℤ) :
    (l.map f).sum
      = ((l.map (fun r => (f r).toNat)).sum : ℤ)
        - ((l.map (fun r => (-(f r)).toNat)).sum : ℤ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      push_cast
      have : ((f a).toNat : ℤ) - ((-(f a)).toNat : ℤ) = f a := by
        rcases le_or_lt 0 (f a) with hpos | hneg
        · rw [Int.toNat_of_nonneg hpos, Int.toNat_of_nonpos (by linarith)]; simp
        · rw [Int.toNat_of_nonpos (le_of_lt hneg), Int.toNat_of_nonneg (by linarith)]; ring
      linarith [this]

theorem abs_int_cast_eq {z : ℤ} : |(z : ℚ)| = ((z.natAbs : ℕ) : ℚ) := by
  simp [Int.cast_natAbs]

/-- From an integer residual witness to a bound on the difference of two
rationals given as integer ratios. -/
theorem abs_sub_div_le {p u v q : ℤ} (hq : 0 < q) (hv : v ≠ 0) {E k : ℕ}
    (h : (p * v - u * q).natAbs * 2 ^ k ≤ E * (q.natAbs * v.natAbs)) :
    |(p : ℚ) / (q : ℚ) - (u : ℚ) / (v : ℚ)| ≤ (E : ℚ) / 2 ^ k := by
  have hq' : (q : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hq.ne'
  have hv' : (v : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hv
  have key : (p : ℚ) / q - (u : ℚ) / v = ((p * v - u * q : ℤ) : ℚ) / ((q : ℚ) * v) := by
    push_cast; field_simp; ring
  rw [key, abs_div, abs_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [abs_int_cast_eq, abs_int_cast_eq, abs_int_cast_eq]
  have hcast := (Nat.cast_le (α := ℚ)).mpr h
  push_cast at hcast
  nlinarith [hcast, Nat.cast_nonneg (α := ℚ) (p * v - u * q).natAbs,
             Nat.cast_nonneg (α := ℚ) q.natAbs, Nat.cast_nonneg (α := ℚ) v.natAbs]

/-! ## The pinned-run data model -/

/-- The scale exponents and prefactor of one pinned run. Every exported
quantity is an exact integer once multiplied by the stated power of two;
the exports are float64 and therefore dyadic, so nothing is lost. -/
structure Scales where
  sGme : ℕ
  sEden : ℕ
  sDen : ℕ
  sOcc : ℕ
  kEps : ℕ
  sFact : ℕ
  factZ : ℤ

/-- One transition of the pinned run.

`ez`, `dZ`, `oZ` are exported operands. `qw` is the star-summed product of the
unweighted matrix elements for the target entry, and `resid`/`eUp` are the
denominator witnesses. All three witnesses are checked against the operands by
`rowOK` and, for `qw`, by the k-point table in the generated module. -/
structure Row where
  /-- exported `eval`, at scale `2^sDen` -/
  evZ : ℤ
  /-- exported `econd`, at scale `2^sDen` -/
  ecZ : ℤ
  /-- exported `occ_v`, at scale `2^sOcc` -/
  ovZ : ℤ
  /-- exported `occ_c`, at scale `2^sOcc` -/
  ocZ : ℤ
  /-- exported `eden`, at scale `2^sEden` -/
  ez : ℤ
  /-- `eval - econd`; checked against `evZ`, `ecZ` by `rowOK` -/
  dZ : ℤ
  /-- `occ_v - occ_c`; checked against `ovZ`, `ocZ` by `rowOK` -/
  oZ : ℤ
  /-- star-summed product of unweighted matrix elements for the target entry;
  checked against the k-point table in the generated module -/
  qw : ℤ
  /-- denominator residual witness; checked against the operands by `rowOK` -/
  resid : ℕ
  /-- dyadic upper bound on the denominator error, at scale `2^kEps` -/
  eUp : ℕ
deriving DecidableEq

namespace Row
variable (S : Scales) (r : Row)

/-- The denominator as the code exported it. -/
def edenHatQ : ℚ := (r.ez : ℚ) / ((2 : ℚ) ^ S.sEden)

/-- The denominator the operands imply, exactly: `occ / (eval - econd)`. -/
def dStarQ : ℚ := ((r.oZ * 2 ^ S.sDen : ℤ) : ℚ) / ((r.dZ * 2 ^ S.sOcc : ℤ) : ℚ)

/-- The weight this transition carries into the entry. -/
def coefQ : ℚ := ((S.factZ : ℚ) / (2 : ℚ) ^ S.sFact) * (r.qw : ℚ) / (2 : ℚ) ^ (2 * S.sGme)

/-- The certified bound on this transition's denominator error. -/
def epsQ : ℚ := (r.eUp : ℚ) / (2 : ℚ) ^ S.kEps

end Row

/-- The row's witnesses are the ones its own operands imply. Decidable, so the
generated module discharges it by `rfl`. -/
def rowOK (S : Scales) (r : Row) : Bool :=
  (r.dZ == r.evZ - r.ecZ) &&
  (r.oZ == r.ovZ - r.ocZ) &&
  (!(r.dZ == 0)) &&
  (r.resid == (r.ez * (r.dZ * 2 ^ S.sOcc)
                 - (r.oZ * 2 ^ S.sDen) * (2 ^ S.sEden : ℤ)).natAbs) &&
  (r.resid * 2 ^ S.kEps ≤ r.eUp * ((2 ^ S.sEden : ℤ).natAbs * (r.dZ * 2 ^ S.sOcc).natAbs))

theorem row_bound (S : Scales) (r : Row) (h : rowOK S r = true) :
    |r.edenHatQ S - r.dStarQ S| ≤ r.epsQ S := by
  simp only [rowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨-, -⟩, hd⟩, hres⟩, hle⟩ := h
  have hv : r.dZ * 2 ^ S.sOcc ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨hd, by positivity⟩
  have hq : (0 : ℤ) < 2 ^ S.sEden := by positivity
  have := abs_sub_div_le (p := r.ez) (u := r.oZ * 2 ^ S.sDen)
    (v := r.dZ * 2 ^ S.sOcc) (q := (2 ^ S.sEden : ℤ)) hq hv (E := r.eUp) (k := S.kEps)
    (by rw [← hres]; exact hle)
  simpa [Row.edenHatQ, Row.dStarQ, Row.epsQ] using this

/-- The transfer, for a table whose rows all pass `rowOK`. -/
theorem table_transfer (S : Scales) (l : List Row) (h : l.all (rowOK S) = true) :
    |(l.map (fun r => r.coefQ S * r.edenHatQ S)).sum
       - (l.map (fun r => r.coefQ S * r.dStarQ S)).sum|
      ≤ (l.map (fun r => |r.coefQ S| * r.epsQ S)).sum := by
  refine list_transfer l _ _ _ _ (fun x hx => row_bound S x ?_)
  exact (List.all_eq_true.mp h) x hx

/-- The exported-denominator reconstruction, as a single scaled integer sum. -/
theorem recon_eval (S : Scales) (l : List Row) :
    (l.map (fun r => r.coefQ S * r.edenHatQ S)).sum
      = ((S.factZ : ℚ) / (2 : ℚ) ^ (S.sFact + 2 * S.sGme + S.sEden))
        * (((l.map (fun r => r.qw * r.ez)).sum : ℤ) : ℚ) := by
  have hf : (fun r : Row => r.coefQ S * r.edenHatQ S)
      = (fun r : Row => ((S.factZ : ℚ) / (2 : ℚ) ^ (S.sFact + 2 * S.sGme + S.sEden))
            * ((r.qw * r.ez : ℤ) : ℚ)) := by
    funext r
    simp only [Row.coefQ, Row.edenHatQ]
    push_cast
    ring
  rw [hf, sum_map_const_mul_int]

/-- The transfer allowance, as a single scaled natural sum. -/
theorem transfer_eval (S : Scales) (l : List Row) :
    (l.map (fun r => |r.coefQ S| * r.epsQ S)).sum
      = (|(S.factZ : ℚ)| / (2 : ℚ) ^ (S.sFact + 2 * S.sGme + S.kEps))
        * (((l.map (fun r => r.qw.natAbs * r.eUp)).sum : ℕ) : ℚ) := by
  have hf : (fun r : Row => |r.coefQ S| * r.epsQ S)
      = (fun r : Row => (|(S.factZ : ℚ)| / (2 : ℚ) ^ (S.sFact + 2 * S.sGme + S.kEps))
            * ((r.qw.natAbs * r.eUp : ℕ) : ℚ)) := by
    funext r
    simp only [Row.coefQ, Row.epsQ]
    rw [abs_div, abs_mul, abs_div]
    simp only [abs_int_cast_eq]
    rw [abs_of_nonneg (by positivity : (0:ℚ) ≤ (2:ℚ) ^ S.sFact),
        abs_of_nonneg (by positivity : (0:ℚ) ≤ (2:ℚ) ^ (2 * S.sGme))]
    push_cast
    ring
  rw [hf, sum_map_const_mul_nat]

/-- `|x|` on ℚ as a `max`: `norm_num` will not evaluate `|q|` directly. -/
def absQ (x : ℚ) : ℚ := max x (-x)

theorem absQ_eq (x : ℚ) : |x| = absQ x := abs_eq_max_neg

end GW.BGW.M3
